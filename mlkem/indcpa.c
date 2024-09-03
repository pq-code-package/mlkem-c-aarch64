// SPDX-License-Identifier: Apache-2.0
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "params.h"
#include "indcpa.h"
#include "polyvec.h"
#include "poly.h"
#include "ntt.h"
#include "symmetric.h"
#include "randombytes.h"
#include "fips202x4.h"
#include "fips202.h"

/*************************************************
* Name:        pack_pk
*
* Description: Serialize the public key as concatenation of the
*              serialized vector of polynomials pk
*              and the public seed used to generate the matrix A.
*
* Arguments:   uint8_t *r: pointer to the output serialized public key
*              polyvec *pk: pointer to the input public-key polyvec
*              const uint8_t *seed: pointer to the input public seed
**************************************************/
static void pack_pk(uint8_t r[KYBER_INDCPA_PUBLICKEYBYTES],
                    polyvec *pk,
                    const uint8_t seed[KYBER_SYMBYTES])
{
    polyvec_tobytes(r, pk);
    memcpy(r + KYBER_POLYVECBYTES, seed, KYBER_SYMBYTES);
}

/*************************************************
* Name:        unpack_pk
*
* Description: De-serialize public key from a byte array;
*              approximate inverse of pack_pk
*
* Arguments:   - polyvec *pk: pointer to output public-key polynomial vector
*              - uint8_t *seed: pointer to output seed to generate matrix A
*              - const uint8_t *packedpk: pointer to input serialized public key
**************************************************/
static void unpack_pk(polyvec *pk,
                      uint8_t seed[KYBER_SYMBYTES],
                      const uint8_t packedpk[KYBER_INDCPA_PUBLICKEYBYTES])
{
    polyvec_frombytes(pk, packedpk);
    memcpy(seed, packedpk + KYBER_POLYVECBYTES, KYBER_SYMBYTES);
}

/*************************************************
* Name:        pack_sk
*
* Description: Serialize the secret key
*
* Arguments:   - uint8_t *r: pointer to output serialized secret key
*              - polyvec *sk: pointer to input vector of polynomials (secret key)
**************************************************/
static void pack_sk(uint8_t r[KYBER_INDCPA_SECRETKEYBYTES], polyvec *sk)
{
    polyvec_tobytes(r, sk);
}

/*************************************************
* Name:        unpack_sk
*
* Description: De-serialize the secret key; inverse of pack_sk
*
* Arguments:   - polyvec *sk: pointer to output vector of polynomials (secret key)
*              - const uint8_t *packedsk: pointer to input serialized secret key
**************************************************/
static void unpack_sk(polyvec *sk, const uint8_t packedsk[KYBER_INDCPA_SECRETKEYBYTES])
{
    polyvec_frombytes(sk, packedsk);
}

/*************************************************
* Name:        pack_ciphertext
*
* Description: Serialize the ciphertext as concatenation of the
*              compressed and serialized vector of polynomials b
*              and the compressed and serialized polynomial v
*
* Arguments:   uint8_t *r: pointer to the output serialized ciphertext
*              poly *pk: pointer to the input vector of polynomials b
*              poly *v: pointer to the input polynomial v
**************************************************/
static void pack_ciphertext(uint8_t r[KYBER_INDCPA_BYTES], polyvec *b, poly *v)
{
    polyvec_compress(r, b);
    poly_compress(r + KYBER_POLYVECCOMPRESSEDBYTES, v);
}

/*************************************************
* Name:        unpack_ciphertext
*
* Description: De-serialize and decompress ciphertext from a byte array;
*              approximate inverse of pack_ciphertext
*
* Arguments:   - polyvec *b: pointer to the output vector of polynomials b
*              - poly *v: pointer to the output polynomial v
*              - const uint8_t *c: pointer to the input serialized ciphertext
**************************************************/
static void unpack_ciphertext(polyvec *b, poly *v, const uint8_t c[KYBER_INDCPA_BYTES])
{
    polyvec_decompress(b, c);
    poly_decompress(v, c + KYBER_POLYVECCOMPRESSEDBYTES);
}

/*************************************************
* Name:        rej_uniform
*
* Description: Run rejection sampling on uniform random bytes to generate
*              uniform random integers mod q
*
* Arguments:   - int16_t *r: pointer to output buffer
*              - unsigned int len: requested number of 16-bit integers (uniform mod q)
*              - const uint8_t *buf: pointer to input buffer (assumed to be uniformly random bytes)
*              - unsigned int buflen: length of input buffer in bytes
*
* Returns number of sampled 16-bit integers (at most len)
**************************************************/
static unsigned int rej_uniform(int16_t *r,
                                unsigned int len,
                                const uint8_t *buf,
                                unsigned int buflen)
{
    unsigned int ctr, pos;
    uint16_t val0, val1;

    ctr = pos = 0;
    while (ctr < len && pos + 3 <= buflen)
    {
        val0 = ((buf[pos + 0] >> 0) | ((uint16_t)buf[pos + 1] << 8)) & 0xFFF;
        val1 = ((buf[pos + 1] >> 4) | ((uint16_t)buf[pos + 2] << 4)) & 0xFFF;
        pos += 3;

        if (val0 < KYBER_Q)
        {
            r[ctr++] = val0;
        }
        if (ctr < len && val1 < KYBER_Q)
        {
            r[ctr++] = val1;
        }
    }

    return ctr;
}

#define gen_a(A,B)  gen_matrix(A,B,0)
#define gen_at(A,B) gen_matrix(A,B,1)

/*************************************************
* Name:        gen_matrix
*
* Description: Deterministically generate matrix A (or the transpose of A)
*              from a seed. Entries of the matrix are polynomials that look
*              uniformly random. Performs rejection sampling on output of
*              a XOF
*
* Arguments:   - polyvec *a: pointer to ouptput matrix A
*              - const uint8_t *seed: pointer to input seed
*              - int transposed: boolean deciding whether A or A^T is generated
**************************************************/
#define GEN_MATRIX_NBLOCKS ((12*KYBER_N/8*(1 << 12)/KYBER_Q + XOF_BLOCKBYTES)/XOF_BLOCKBYTES)
// Not static for benchmarking
void gen_matrix(polyvec *a, const uint8_t seed[KYBER_SYMBYTES], int transposed)
{
    unsigned int ctr, i, j;
    unsigned int buflen;
    uint8_t bufx[KECCAK_WAY][GEN_MATRIX_NBLOCKS * XOF_BLOCKBYTES];
    uint8_t *buf = NULL;
    int16_t *vec = NULL;
    uint8_t x, y;
    xof_state state;

    keccakx4_state statex;
    // The input data to each Keccak lane.
    // Original size; KYBER_SYMBYTES + 2, we add padding to make align load/store.
    uint8_t seedxy[KECCAK_WAY][KYBER_SYMBYTES + 16];
    for (j = 0; j < KECCAK_WAY; j++)
    {
        memcpy(seedxy[j], seed, KYBER_SYMBYTES);
    }
    for (i = 0; i < (KYBER_K * KYBER_K / KECCAK_WAY) * KECCAK_WAY; i += KECCAK_WAY)
    {
        for (j = 0; j < KECCAK_WAY; j++)
        {
            x = (i + j) / KYBER_K;
            y = (i + j) % KYBER_K;
            if (transposed)
            {
                seedxy[j][KYBER_SYMBYTES + 0] = x;
                seedxy[j][KYBER_SYMBYTES + 1] = y;
            }
            else
            {
                seedxy[j][KYBER_SYMBYTES + 0] = y;
                seedxy[j][KYBER_SYMBYTES + 1] = x;
            }
        }

        shake128x4_absorb(&statex, seedxy[0], seedxy[1], seedxy[2], seedxy[3], KYBER_SYMBYTES + 2);
        shake128x4_squeezeblocks(bufx[0], bufx[1], bufx[2], bufx[3], GEN_MATRIX_NBLOCKS, &statex);

        for (j = 0; j < KECCAK_WAY; j++)
        {
            x = (i + j) / KYBER_K;
            y = (i + j) % KYBER_K;
            vec = a[x].vec[y].coeffs;
            buf = bufx[j];
            buflen = GEN_MATRIX_NBLOCKS * XOF_BLOCKBYTES;
            ctr = rej_uniform(vec, KYBER_N, buf, buflen);

            while (ctr < KYBER_N )
            {
                shake256x4_squeezeblocks_single(buf, 1, j, &statex);
                buflen = XOF_BLOCKBYTES;
                ctr += rej_uniform(vec + ctr, KYBER_N - ctr, buf, buflen);
            }
        }
    }

    // For left over vector, we use single keccak.
    for (; i < KYBER_K * KYBER_K; i++)
    {
        x = i / KYBER_K;
        y = i % KYBER_K;
        buf = bufx[0];
        vec = a[x].vec[y].coeffs;

        if (transposed)
        {
            xof_absorb(&state, seed, x, y);
        }
        else
        {
            xof_absorb(&state, seed, y, x);
        }
        xof_squeezeblocks(buf, GEN_MATRIX_NBLOCKS, &state);
        buflen = GEN_MATRIX_NBLOCKS * XOF_BLOCKBYTES;
        ctr = rej_uniform(vec, KYBER_N, buf, buflen);

        while (ctr < KYBER_N)
        {
            xof_squeezeblocks(buf, 1, &state);
            buflen = XOF_BLOCKBYTES;
            ctr += rej_uniform(vec + ctr, KYBER_N - ctr, buf, buflen);
        }
    }
}

/*************************************************
* Name:        indcpa_keypair_derand
*
* Description: Generates public and private key for the CPA-secure
*              public-key encryption scheme underlying Kyber
*
* Arguments:   - uint8_t *pk: pointer to output public key
*                             (of length KYBER_INDCPA_PUBLICKEYBYTES bytes)
*              - uint8_t *sk: pointer to output private key
*                             (of length KYBER_INDCPA_SECRETKEYBYTES bytes)
*              - const uint8_t *coins: pointer to input randomness
*                             (of length KYBER_SYMBYTES bytes)
**************************************************/
void indcpa_keypair_derand(uint8_t pk[KYBER_INDCPA_PUBLICKEYBYTES],
                           uint8_t sk[KYBER_INDCPA_SECRETKEYBYTES],
                           const uint8_t coins[KYBER_SYMBYTES])
{
    unsigned int i;
    uint8_t buf[2 * KYBER_SYMBYTES];
    const uint8_t *publicseed = buf;
    const uint8_t *noiseseed = buf + KYBER_SYMBYTES;
    polyvec a[KYBER_K], e, pkpv, skpv;

    // Add KYBER_K for domain separation of security levels
    memcpy(buf, coins, KYBER_SYMBYTES);
    buf[KYBER_SYMBYTES] = KYBER_K;
    hash_g(buf, buf, KYBER_SYMBYTES+1);

    gen_a(a, publicseed);

    #if KYBER_K == 2
    poly_getnoise_eta1_4x(skpv.vec+0, skpv.vec+1, e.vec+0, e.vec+1, noiseseed, 0, 1, 2, 3);
    #elif KYBER_K == 3
    poly_getnoise_eta1_4x(skpv.vec+0, skpv.vec+1, skpv.vec+2, e.vec+0, noiseseed, 0, 1, 2, 3);
    poly_getnoise_eta1_4x(e.vec+1, e.vec+2, pkpv.vec+0, pkpv.vec+1, noiseseed, 4, 5, 6, 7);
    #elif KYBER_K == 4
    poly_getnoise_eta1_4x(skpv.vec+0, skpv.vec+1, skpv.vec+2, skpv.vec+3, noiseseed,  0, 1, 2, 3);
    poly_getnoise_eta1_4x(e.vec+0, e.vec+1, e.vec+2, e.vec+3, noiseseed, 4, 5, 6, 7);
    #endif

    polyvec_ntt(&skpv);
    polyvec_ntt(&e);

    // matrix-vector multiplication
    for (i = 0; i < KYBER_K; i++)
    {
        polyvec_basemul_acc_montgomery(&pkpv.vec[i], &a[i], &skpv);
        poly_tomont(&pkpv.vec[i]);
    }

    polyvec_add(&pkpv, &pkpv, &e);
    polyvec_reduce(&pkpv);

    pack_sk(sk, &skpv);
    pack_pk(pk, &pkpv, publicseed);
}

/*************************************************
* Name:        indcpa_enc
*
* Description: Encryption function of the CPA-secure
*              public-key encryption scheme underlying Kyber.
*
* Arguments:   - uint8_t *c: pointer to output ciphertext
*                            (of length KYBER_INDCPA_BYTES bytes)
*              - const uint8_t *m: pointer to input message
*                                  (of length KYBER_INDCPA_MSGBYTES bytes)
*              - const uint8_t *pk: pointer to input public key
*                                   (of length KYBER_INDCPA_PUBLICKEYBYTES)
*              - const uint8_t *coins: pointer to input random coins used as seed
*                                      (of length KYBER_SYMBYTES) to deterministically
*                                      generate all randomness
**************************************************/
void indcpa_enc(uint8_t c[KYBER_INDCPA_BYTES],
                const uint8_t m[KYBER_INDCPA_MSGBYTES],
                const uint8_t pk[KYBER_INDCPA_PUBLICKEYBYTES],
                const uint8_t coins[KYBER_SYMBYTES])
{
    unsigned int i;
    uint8_t seed[KYBER_SYMBYTES];
    polyvec sp, pkpv, ep, at[KYBER_K], b;
    poly v, k, epp;

    unpack_pk(&pkpv, seed, pk);
    poly_frommsg(&k, m);
    gen_at(at, seed);

    #if KYBER_K == 2
    poly_getnoise_eta1122_4x(sp.vec+0, sp.vec+1, ep.vec+0, ep.vec+1, coins, 0, 1, 2, 3);
    poly_getnoise_eta2(&epp, coins, 4);
    #elif KYBER_K == 3
    poly_getnoise_eta1_4x(sp.vec+0, sp.vec+1, sp.vec+2, ep.vec+0, coins, 0, 1, 2, 3);
    poly_getnoise_eta1_4x(ep.vec+1, ep.vec+2, &epp, b.vec+0, coins,  4, 5, 6, 7);
    #elif KYBER_K == 4
    poly_getnoise_eta1_4x(sp.vec+0, sp.vec+1, sp.vec+2, sp.vec+3, coins, 0, 1, 2, 3);
    poly_getnoise_eta1_4x(ep.vec+0, ep.vec+1, ep.vec+2, ep.vec+3, coins, 4, 5, 6, 7);
    poly_getnoise_eta2(&epp, coins, 8);
    #endif

    polyvec_ntt(&sp);

    // matrix-vector multiplication
    for (i = 0; i < KYBER_K; i++)
    {
        polyvec_basemul_acc_montgomery(&b.vec[i], &at[i], &sp);
    }

    polyvec_basemul_acc_montgomery(&v, &pkpv, &sp);

    polyvec_invntt_tomont(&b);
    poly_invntt_tomont(&v);

    polyvec_add(&b, &b, &ep);
    poly_add(&v, &v, &epp);
    poly_add(&v, &v, &k);
    polyvec_reduce(&b);
    poly_reduce(&v);

    pack_ciphertext(c, &b, &v);
}

/*************************************************
* Name:        indcpa_dec
*
* Description: Decryption function of the CPA-secure
*              public-key encryption scheme underlying Kyber.
*
* Arguments:   - uint8_t *m: pointer to output decrypted message
*                            (of length KYBER_INDCPA_MSGBYTES)
*              - const uint8_t *c: pointer to input ciphertext
*                                  (of length KYBER_INDCPA_BYTES)
*              - const uint8_t *sk: pointer to input secret key
*                                   (of length KYBER_INDCPA_SECRETKEYBYTES)
**************************************************/
void indcpa_dec(uint8_t m[KYBER_INDCPA_MSGBYTES],
                const uint8_t c[KYBER_INDCPA_BYTES],
                const uint8_t sk[KYBER_INDCPA_SECRETKEYBYTES])
{
    polyvec b, skpv;
    poly v, mp;

    unpack_ciphertext(&b, &v, c);
    unpack_sk(&skpv, sk);

    polyvec_ntt(&b);
    polyvec_basemul_acc_montgomery(&mp, &skpv, &b);
    poly_invntt_tomont(&mp);

    poly_sub(&mp, &v, &mp);
    poly_reduce(&mp);

    poly_tomsg(m, &mp);
}
