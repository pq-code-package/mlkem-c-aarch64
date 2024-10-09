// SPDX-License-Identifier: Apache-2.0
#include "indcpa.h"
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "fips202.h"
#include "fips202x4.h"
#include "indcpa.h"
#include "ntt.h"
#include "params.h"
#include "poly.h"
#include "polyvec.h"
#include "randombytes.h"
#include "rej_uniform.h"
#include "symmetric.h"

#include "arith_native.h"
#include "debug/debug.h"

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
static void pack_pk(uint8_t r[KYBER_INDCPA_PUBLICKEYBYTES], polyvec *pk,
                    const uint8_t seed[KYBER_SYMBYTES]) {
  POLYVEC_BOUND(pk, KYBER_Q);
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
 *              - const uint8_t *packedpk: pointer to input serialized public
 *key
 **************************************************/
static void unpack_pk(polyvec *pk, uint8_t seed[KYBER_SYMBYTES],
                      const uint8_t packedpk[KYBER_INDCPA_PUBLICKEYBYTES]) {
  polyvec_frombytes(pk, packedpk);
  memcpy(seed, packedpk + KYBER_POLYVECBYTES, KYBER_SYMBYTES);

  // TODO! pk must be subject to a "modulus check" at the top-level
  // crypto_kem_enc_derand(). Once that's done, the reduction is no
  // longer necessary here.
  polyvec_reduce(pk);
}

/*************************************************
 * Name:        pack_sk
 *
 * Description: Serialize the secret key
 *
 * Arguments:   - uint8_t *r: pointer to output serialized secret key
 *              - polyvec *sk: pointer to input vector of polynomials (secret
 *key)
 **************************************************/
static void pack_sk(uint8_t r[KYBER_INDCPA_SECRETKEYBYTES], polyvec *sk) {
  POLYVEC_BOUND(sk, KYBER_Q);
  polyvec_tobytes(r, sk);
}

/*************************************************
 * Name:        unpack_sk
 *
 * Description: De-serialize the secret key; inverse of pack_sk
 *
 * Arguments:   - polyvec *sk: pointer to output vector of polynomials (secret
 *key)
 *              - const uint8_t *packedsk: pointer to input serialized secret
 *key
 **************************************************/
static void unpack_sk(polyvec *sk,
                      const uint8_t packedsk[KYBER_INDCPA_SECRETKEYBYTES]) {
  polyvec_frombytes(sk, packedsk);
  polyvec_reduce(sk);
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
static void pack_ciphertext(uint8_t r[KYBER_INDCPA_BYTES], polyvec *b,
                            poly *v) {
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
static void unpack_ciphertext(polyvec *b, poly *v,
                              const uint8_t c[KYBER_INDCPA_BYTES]) {
  polyvec_decompress(b, c);
  poly_decompress(v, c + KYBER_POLYVECCOMPRESSEDBYTES);
}

#define gen_a(A, B) gen_matrix(A, B, 0)
#define gen_at(A, B) gen_matrix(A, B, 1)

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
#define GEN_MATRIX_NBLOCKS \
  ((12 * KYBER_N / 8 * (1 << 12) / KYBER_Q + SHAKE128_RATE) / SHAKE128_RATE)
// Not static for benchmarking
void gen_matrix(polyvec *a, const uint8_t seed[KYBER_SYMBYTES],
                int transposed) {
  unsigned int ctr[KECCAK_WAY], i;
  unsigned int buflen;
  uint8_t bufx[KECCAK_WAY][GEN_MATRIX_NBLOCKS * SHAKE128_RATE];
  int16_t *vec[KECCAK_WAY] = {NULL};

  keccakx4_state statex;
  // The input data to each Keccak lane.
  // Original size; KYBER_SYMBYTES + 2, we add padding to make align load/store.
  uint8_t seedxy[KECCAK_WAY][KYBER_SYMBYTES + 16];
  for (unsigned j = 0; j < KECCAK_WAY; j++) {
    memcpy(seedxy[j], seed, KYBER_SYMBYTES);
  }

  // TODO: All loops in this function should be unrolled for decent
  // performance.
  //
  // Either add suitable pragmas, or split gen_matrix according to KYBER_K
  // and unroll by hand.

  for (i = 0; i < (KYBER_K * KYBER_K / KECCAK_WAY) * KECCAK_WAY;
       i += KECCAK_WAY) {
    uint8_t x, y;

    for (unsigned int j = 0; j < KECCAK_WAY; j++) {
      x = (i + j) / KYBER_K;
      y = (i + j) % KYBER_K;
      if (transposed) {
        seedxy[j][KYBER_SYMBYTES + 0] = x;
        seedxy[j][KYBER_SYMBYTES + 1] = y;
      } else {
        seedxy[j][KYBER_SYMBYTES + 0] = y;
        seedxy[j][KYBER_SYMBYTES + 1] = x;
      }
    }

    shake128x4_absorb(&statex, seedxy[0], seedxy[1], seedxy[2], seedxy[3],
                      KYBER_SYMBYTES + 2);
    shake128x4_squeezeblocks(bufx[0], bufx[1], bufx[2], bufx[3],
                             GEN_MATRIX_NBLOCKS, &statex);

    for (unsigned int j = 0; j < KECCAK_WAY; j++) {
      x = (i + j) / KYBER_K;
      y = (i + j) % KYBER_K;
      vec[j] = a[x].vec[y].coeffs;
      buflen = GEN_MATRIX_NBLOCKS * SHAKE128_RATE;
      ctr[j] = rej_uniform(vec[j], KYBER_N, bufx[j], buflen);
    }

    while (ctr[0] < KYBER_N || ctr[1] < KYBER_N || ctr[2] < KYBER_N ||
           ctr[3] < KYBER_N) {
      shake128x4_squeezeblocks(bufx[0], bufx[1], bufx[2], bufx[3], 1, &statex);
      buflen = SHAKE128_RATE;

      for (unsigned j = 0; j < KECCAK_WAY; j++) {
        ctr[j] +=
            rej_uniform(vec[j] + ctr[j], KYBER_N - ctr[j], bufx[j], buflen);
      }
    }
  }

  // For left over vector, we use single keccak.
  for (; i < KYBER_K * KYBER_K; i++) {
    shake128ctx state;
    uint8_t x, y;

    x = i / KYBER_K;
    y = i % KYBER_K;
    vec[0] = a[x].vec[y].coeffs;

    if (transposed) {
      seedxy[0][KYBER_SYMBYTES + 0] = x;
      seedxy[0][KYBER_SYMBYTES + 1] = y;
      shake128_absorb(&state, seedxy[0], KYBER_SYMBYTES + 2);
    } else {
      seedxy[0][KYBER_SYMBYTES + 0] = y;
      seedxy[0][KYBER_SYMBYTES + 1] = x;
      shake128_absorb(&state, seedxy[0], KYBER_SYMBYTES + 2);
    }

    shake128_squeezeblocks(bufx[0], GEN_MATRIX_NBLOCKS, &state);
    buflen = GEN_MATRIX_NBLOCKS * SHAKE128_RATE;
    ctr[0] = rej_uniform(vec[0], KYBER_N, bufx[0], buflen);

    while (ctr[0] < KYBER_N) {
      shake128_squeezeblocks(bufx[0], 1, &state);
      buflen = SHAKE128_RATE;
      ctr[0] += rej_uniform(vec[0] + ctr[0], KYBER_N - ctr[0], bufx[0], buflen);
    }
  }

#if defined(MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER)
  // The public matrix is generated in NTT domain. If the native backend
  // uses a custom order in NTT domain, permute A accordingly.
  for (i = 0; i < KYBER_K; i++) {
    for (int j = 0; j < KYBER_K; j++) {
      poly_permute_bitrev_to_custom(&a[i].vec[j]);
    }
  }
#endif /* MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER */
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
                           const uint8_t coins[KYBER_SYMBYTES]) {
  unsigned int i;
  uint8_t buf[2 * KYBER_SYMBYTES] ALIGN;
  const uint8_t *publicseed = buf;
  const uint8_t *noiseseed = buf + KYBER_SYMBYTES;
  polyvec a[KYBER_K], e, pkpv, skpv;
  polyvec_mulcache skpv_cache;

  // Add KYBER_K for domain separation of security levels
  memcpy(buf, coins, KYBER_SYMBYTES);
  buf[KYBER_SYMBYTES] = KYBER_K;
  hash_g(buf, buf, KYBER_SYMBYTES + 1);

  gen_a(a, publicseed);

#if KYBER_K == 2
  poly_getnoise_eta1_4x(skpv.vec + 0, skpv.vec + 1, e.vec + 0, e.vec + 1,
                        noiseseed, 0, 1, 2, 3);
#elif KYBER_K == 3
  poly_getnoise_eta1_4x(skpv.vec + 0, skpv.vec + 1, skpv.vec + 2, e.vec + 0,
                        noiseseed, 0, 1, 2, 3);
  poly_getnoise_eta1_4x(e.vec + 1, e.vec + 2, pkpv.vec + 0, pkpv.vec + 1,
                        noiseseed, 4, 5, 6, 7);
#elif KYBER_K == 4
  poly_getnoise_eta1_4x(skpv.vec + 0, skpv.vec + 1, skpv.vec + 2, skpv.vec + 3,
                        noiseseed, 0, 1, 2, 3);
  poly_getnoise_eta1_4x(e.vec + 0, e.vec + 1, e.vec + 2, e.vec + 3, noiseseed,
                        4, 5, 6, 7);
#endif

  polyvec_ntt(&skpv);
  polyvec_ntt(&e);

  polyvec_mulcache_compute(&skpv_cache, &skpv);

  // matrix-vector multiplication
  for (i = 0; i < KYBER_K; i++) {
    polyvec_basemul_acc_montgomery_cached(&pkpv.vec[i], &a[i], &skpv,
                                          &skpv_cache);
    poly_tomont(&pkpv.vec[i]);
  }

  // Bounds: |pkpv| < q, |e| < NTT_BOUND
  polyvec_add(&pkpv, &pkpv, &e);
  polyvec_reduce(&pkpv);
  polyvec_reduce(&skpv);

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
 *              - const uint8_t *coins: pointer to input random coins used as
 *seed (of length KYBER_SYMBYTES) to deterministically generate all randomness
 **************************************************/

// Check that the arithmetic in indcpa_enc() does not overflow
STATIC_ASSERT(INVNTT_BOUND + KYBER_ETA1 < INT16_MAX, indcpa_enc_bound_0)
STATIC_ASSERT(INVNTT_BOUND + KYBER_ETA2 + KYBER_Q < INT16_MAX,
              indcpa_enc_bound_1)

void indcpa_enc(uint8_t c[KYBER_INDCPA_BYTES],
                const uint8_t m[KYBER_INDCPA_MSGBYTES],
                const uint8_t pk[KYBER_INDCPA_PUBLICKEYBYTES],
                const uint8_t coins[KYBER_SYMBYTES]) {
  unsigned int i;
  uint8_t seed[KYBER_SYMBYTES] ALIGN;
  polyvec sp, pkpv, ep, at[KYBER_K], b;
  polyvec_mulcache sp_cache;
  poly v, k, epp;

  unpack_pk(&pkpv, seed, pk);
  poly_frommsg(&k, m);
  gen_at(at, seed);

#if KYBER_K == 2
  poly_getnoise_eta1122_4x(sp.vec + 0, sp.vec + 1, ep.vec + 0, ep.vec + 1,
                           coins, 0, 1, 2, 3);
  poly_getnoise_eta2(&epp, coins, 4);
#elif KYBER_K == 3
  poly_getnoise_eta1_4x(sp.vec + 0, sp.vec + 1, sp.vec + 2, ep.vec + 0, coins,
                        0, 1, 2, 3);
  poly_getnoise_eta1_4x(ep.vec + 1, ep.vec + 2, &epp, b.vec + 0, coins, 4, 5, 6,
                        7);
#elif KYBER_K == 4
  poly_getnoise_eta1_4x(sp.vec + 0, sp.vec + 1, sp.vec + 2, sp.vec + 3, coins,
                        0, 1, 2, 3);
  poly_getnoise_eta1_4x(ep.vec + 0, ep.vec + 1, ep.vec + 2, ep.vec + 3, coins,
                        4, 5, 6, 7);
  poly_getnoise_eta2(&epp, coins, 8);
#endif

  polyvec_ntt(&sp);
  polyvec_mulcache_compute(&sp_cache, &sp);

  // matrix-vector multiplication
  for (i = 0; i < KYBER_K; i++) {
    polyvec_basemul_acc_montgomery_cached(&b.vec[i], &at[i], &sp, &sp_cache);
  }

  polyvec_basemul_acc_montgomery_cached(&v, &pkpv, &sp, &sp_cache);

  polyvec_invntt_tomont(&b);
  poly_invntt_tomont(&v);

  // Arithmetic cannot overflow, see static assertion at the top
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

// Check that the arithmetic in indcpa_dec() does not overflow
STATIC_ASSERT(INVNTT_BOUND + KYBER_Q < INT16_MAX, indcpa_dec_bound_0)

void indcpa_dec(uint8_t m[KYBER_INDCPA_MSGBYTES],
                const uint8_t c[KYBER_INDCPA_BYTES],
                const uint8_t sk[KYBER_INDCPA_SECRETKEYBYTES]) {
  polyvec b, skpv;
  poly v, mp;

  unpack_ciphertext(&b, &v, c);
  unpack_sk(&skpv, sk);

  polyvec_ntt(&b);
  polyvec_basemul_acc_montgomery(&mp, &skpv, &b);
  poly_invntt_tomont(&mp);

  // Arithmetic cannot overflow, see static assertion at the top
  poly_sub(&mp, &v, &mp);
  poly_reduce(&mp);

  poly_tomsg(m, &mp);
}
