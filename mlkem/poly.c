// SPDX-License-Identifier: Apache-2.0
#include <stdint.h>
#include <string.h>
#include "cbmc.h"
#include "params.h"
#include "poly.h"
#include "ntt.h"
#include "reduce.h"
#include "cbd.h"
#include "symmetric.h"
#include "verify.h"
#include "fips202x4.h"

/************************************************************
 * Name: scalar_compress_q_16
 *
 * Description: Computes round(u * 16 / q)
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
uint32_t scalar_compress_q_16(int32_t u)
{
    uint32_t d0 = (uint32_t) u;
    d0 <<= 4;
    d0 +=  1665;

    /* This multiply will exceed UINT32_MAX and wrap around */
    /* for large values of u. This is expected and required */
    #ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
    #endif
    d0 *=  80635;
    #ifdef CBMC
#pragma CPROVER check pop
    #endif
    d0 >>= 28;
    d0 &=  0xF;
    return d0;
}

/************************************************************
 * Name: scalar_decompress_q_16
 *
 * Description: Computes round(u * q / 16)
 *
 * Arguments: - u: Unsigned canonical modulus modulo 16
 *                 to be decompressed.
 ************************************************************/
uint32_t scalar_decompress_q_16(uint32_t u)
{
    return ((u * KYBER_Q) + 8) / 16;
}

/************************************************************
 * Name: scalar_compress_q_32
 *
 * Description: Computes round(u * 32 / q)
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
uint32_t scalar_compress_q_32(int32_t u)
{
    uint32_t d0 = (uint32_t) u;
    d0 <<= 5;
    d0 +=  1664;

    /* This multiply will exceed UINT32_MAX and wrap around */
    /* for large values of u. This is expected and required */
    #ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
    #endif
    d0 *=  40318;
    #ifdef CBMC
#pragma CPROVER check pop
    #endif
    d0 >>= 27;
    d0 &=  0x1f;
    return d0;
}

/************************************************************
 * Name: scalar_decompress_q_32
 *
 * Description: Computes round(u * q / 32)
 *
 * Arguments: - u: Unsigned canonical modulus modulo 32
 *                 to be decompressed.
 ************************************************************/
uint32_t scalar_decompress_q_32(uint32_t u)
{
    return ((u * KYBER_Q) + 16) / 32;
}

/************************************************************
 * Name: scalar_signed_to_unsigned_q_16
 *
 * Description: converts signed polynomial coefficient
 *              from signed (-3328 .. 3328) form to
 *              unsigned form (0 .. 3328).
 *
 * Note: Cryptographic constant time implementation
 *
 * Examples:       0 -> 0
 *                 1 -> 1
 *              3328 -> 3328
 *                -1 -> 3328
 *                -2 -> 3327
 *             -3328 -> 1
 *
 * Arguments: c: signed coefficient to be converted
 ************************************************************/
uint16_t scalar_signed_to_unsigned_q_16 (int16_t c)
{
    // Add Q if c is negative, but in constant time
    cmov_int16(&c, c + KYBER_Q, c < 0);

    __CPROVER_assert(c >= 0, "scalar_signed_to_unsigned_q_16 result lower bound");
    __CPROVER_assert(c < KYBER_Q, "scalar_signed_to_unsigned_q_16 result upper bound");

    // and therefore cast to uint16_t is safe.
    return (uint16_t) c;
}

/*************************************************
* Name:        poly_compress
*
* Description: Compression and subsequent serialization of a polynomial
*
* Arguments:   - uint8_t *r: pointer to output byte array
*                            (of length KYBER_POLYCOMPRESSEDBYTES)
*              - const poly *a: pointer to input polynomial
**************************************************/
void poly_compress(uint8_t r[KYBER_POLYCOMPRESSEDBYTES], const poly *a)
{
    uint8_t t[8] = { 0 };

    #if (KYBER_POLYCOMPRESSEDBYTES == 128)
    for (size_t i = 0; i < KYBER_N / 8; i++)
// *INDENT-OFF*
        __CPROVER_assigns(i, __CPROVER_object_whole(t), __CPROVER_object_whole(r))
        __CPROVER_loop_invariant(i <= KYBER_N / 8)
        __CPROVER_decreases(32 - i)
// *INDENT-ON*
    {
        for (size_t j = 0; j < 8; j++)
// *INDENT-OFF*
            __CPROVER_assigns(j, __CPROVER_object_whole(t))
            __CPROVER_loop_invariant(i <= KYBER_N / 8)
            __CPROVER_loop_invariant(j <= 8)
            __CPROVER_loop_invariant(__CPROVER_forall { size_t k2; (0 <= k2 && k2 < j) ==> (t[k2] >= 0 && t[k2] < 16) })
            __CPROVER_decreases(8 - j)
// *INDENT-ON*
        {
            // map to positive standard representatives
            // REF-CHANGE: Hoist signed-to-unsigned conversion into separate function
            int32_t u;
            u = (int32_t) scalar_signed_to_unsigned_q_16(a->coeffs[8 * i + j]);
            // REF-CHANGE: Hoist scalar compression into separate function
            t[j] = scalar_compress_q_16(u);
        }

        __CPROVER_assert(t[0] < 16, "UB on t[0]");
        __CPROVER_assert(t[1] < 16, "UB on t[1]");
        __CPROVER_assert((t[0] | (t[1] << 4)) <= 255, "Range of t");

        r[i * 4]     = t[0] | (t[1] << 4);
        r[i * 4 + 1] = t[2] | (t[3] << 4);
        r[i * 4 + 2] = t[4] | (t[5] << 4);
        r[i * 4 + 3] = t[6] | (t[7] << 4);
    }
    #elif (KYBER_POLYCOMPRESSEDBYTES == 160)
    for (size_t i = 0; i < KYBER_N / 8; i++)
    {
        for (size_t j = 0; j < 8; j++)
        {
            // map to positive standard representatives
            // REF-CHANGE: Hoist signed-to-unsigned conversion into separate function
            int32_t u = (int32_t) scalar_signed_to_unsigned_q_16(a->coeffs[8 * i + j]);
            // REF-CHANGE: Hoist scalar compression into separate function
            t[j] = scalar_compress_q_32(u);
        }

        // REF-CHANGE: Explicitly truncate to avoid warning about
        // implicit truncation in CBMC.
        r[0] = 0xFF & ((t[0] >> 0) | (t[1] << 5));
        r[1] = 0xFF & ((t[1] >> 3) | (t[2] << 2) | (t[3] << 7));
        r[2] = 0xFF & ((t[3] >> 1) | (t[4] << 4));
        r[3] = 0xFF & ((t[4] >> 4) | (t[5] << 1) | (t[6] << 6));
        r[4] = 0xFF & ((t[6] >> 2) | (t[7] << 3));
        r += 5;
    }
    #else
#error "KYBER_POLYCOMPRESSEDBYTES needs to be in {128, 160}"
    #endif
}

/*************************************************
* Name:        poly_decompress
*
* Description: De-serialization and subsequent decompression of a polynomial;
*              approximate inverse of poly_compress
*
* Arguments:   - poly *r: pointer to output polynomial
*              - const uint8_t *a: pointer to input byte array
*                                  (of length KYBER_POLYCOMPRESSEDBYTES bytes)
*
* Upon return, the coefficients of the output polynomial are unsigned-canonical
* (non-negative and smaller than KYBER_Q).
*
**************************************************/
void poly_decompress(poly *r, const uint8_t a[KYBER_POLYCOMPRESSEDBYTES])
/* ------ CBMC contract ------ */
__CPROVER_requires(__CPROVER_is_fresh(r, sizeof(*r)))
__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(KYBER_POLYCOMPRESSEDBYTES)))
__CPROVER_ensures(
    /* Output coefficients are unsigned canonical */
    /* NOTE: Because of https://github.com/diffblue/cbmc/issues/8337 we have to
             avoid a variable name clash with variables used by poly_decompress. */
    __CPROVER_forall
{
    unsigned _i; (_i < KYBER_N) ==> ( 0 <= r->coeffs[_i] && r->coeffs[_i] < KYBER_Q )
})
/* --- End of CBMC contract --- */
{
    unsigned int i;

    #if (KYBER_POLYCOMPRESSEDBYTES == 128)
    for (i = 0; i < KYBER_N / 2; i++)
    {
        // REF-CHANGE: Hoist scalar decompression into separate function
        r->coeffs[2 * i + 0] = scalar_decompress_q_16((a[0] >> 0) & 0xF);
        r->coeffs[2 * i + 1] = scalar_decompress_q_16((a[0] >> 4) & 0xF);
        a += 1;
    }
    #elif (KYBER_POLYCOMPRESSEDBYTES == 160)
    unsigned int j;
    uint8_t t[8];
    for (i = 0; i < KYBER_N / 8; i++)
    {
        // REF-CHANGE: Explicitly truncate to avoid warning about
        // implicit truncation in CBMC.
        t[0] = 0x1F &  (a[0] >> 0);
        t[1] = 0x1F & ((a[0] >> 5) | (a[1] << 3));
        t[2] = 0x1F &  (a[1] >> 2);
        t[3] = 0x1F & ((a[1] >> 7) | (a[2] << 1));
        t[4] = 0x1F & ((a[2] >> 4) | (a[3] << 4));
        t[5] = 0x1F &  (a[3] >> 1);
        t[6] = 0x1F & ((a[3] >> 6) | (a[4] << 2));
        t[7] = 0x1F &  (a[4] >> 3);
        a += 5;

        for (j = 0; j < 8; j++)
        {
            // REF-CHANGE: Truncation happened before
            r->coeffs[8 * i + j] = ((uint32_t) t[j] * KYBER_Q + 16) >> 5;
        }
    }
    #else
#error "KYBER_POLYCOMPRESSEDBYTES needs to be in {128, 160}"
    #endif
}

/*************************************************
* Name:        poly_tobytes
*
* Description: Serialization of a polynomial
*
* Arguments:   - uint8_t *r: pointer to output byte array
*                            (needs space for KYBER_POLYBYTES bytes)
*              - const poly *a: pointer to input polynomial
**************************************************/
void poly_tobytes(uint8_t r[KYBER_POLYBYTES], const poly *a)
{
    unsigned int i;
    uint16_t t0, t1;

    for (i = 0; i < KYBER_N / 2; i++)
    {
        // map to positive standard representatives
        // REF-CHANGE: Hoist signed-to-unsigned conversion into separate function
        t0 = scalar_signed_to_unsigned_q_16(a->coeffs[2 * i]);
        t1 = scalar_signed_to_unsigned_q_16(a->coeffs[2 * i + 1]);
        r[3 * i + 0] = (t0 >> 0);
        r[3 * i + 1] = (t0 >> 8) | (t1 << 4);
        r[3 * i + 2] = (t1 >> 4);
    }
}

/*************************************************
* Name:        poly_frombytes
*
* Description: De-serialization of a polynomial;
*              inverse of poly_tobytes
*
* Arguments:   - poly *r: pointer to output polynomial
*              - const uint8_t *a: pointer to input byte array
*                                  (of KYBER_POLYBYTES bytes)
**************************************************/
void poly_frombytes(poly *r, const uint8_t a[KYBER_POLYBYTES])
{
    unsigned int i;
    for (i = 0; i < KYBER_N / 2; i++)
    {
        r->coeffs[2 * i]   = ((a[3 * i + 0] >> 0) | ((uint16_t)a[3 * i + 1] << 8)) & 0xFFF;
        r->coeffs[2 * i + 1] = ((a[3 * i + 1] >> 4) | ((uint16_t)a[3 * i + 2] << 4)) & 0xFFF;
    }
}

/*************************************************
* Name:        poly_frommsg
*
* Description: Convert 32-byte message to polynomial
*
* Arguments:   - poly *r: pointer to output polynomial
*              - const uint8_t *msg: pointer to input message
**************************************************/
void poly_frommsg(poly *r, const uint8_t msg[KYBER_INDCPA_MSGBYTES])
{
    unsigned int i, j;

    #if (KYBER_INDCPA_MSGBYTES != KYBER_N/8)
#error "KYBER_INDCPA_MSGBYTES must be equal to KYBER_N/8 bytes!"
    #endif

    for (i = 0; i < KYBER_N / 8; i++)
    {
        for (j = 0; j < 8; j++)
        {
            r->coeffs[8 * i + j] = 0;
            cmov_int16(r->coeffs + 8 * i + j, ((KYBER_Q + 1) / 2), (msg[i] >> j) & 1);
        }
    }
}

/*************************************************
* Name:        poly_tomsg
*
* Description: Convert polynomial to 32-byte message
*
* Arguments:   - uint8_t *msg: pointer to output message
*              - const poly *a: pointer to input polynomial
**************************************************/
void poly_tomsg(uint8_t msg[KYBER_INDCPA_MSGBYTES], const poly *a)
{
    unsigned int i, j;
    uint32_t t;

    for (i = 0; i < KYBER_N / 8; i++)
    {
        msg[i] = 0;
        for (j = 0; j < 8; j++)
        {
            t  = a->coeffs[8 * i + j];
            // t += ((int16_t)t >> 15) & KYBER_Q;
            // t  = (((t << 1) + KYBER_Q/2)/KYBER_Q) & 1;
            t <<= 1;
            t += 1665;
            t *= 80635;
            t >>= 28;
            t &= 1;
            msg[i] |= t << j;
        }
    }
}

/*************************************************
* Name:        poly_getnoise_eta1
*
* Description: Sample a polynomial deterministically from a seed and a nonce,
*              with output polynomial close to centered binomial distribution
*              with parameter KYBER_ETA1
*
* Arguments:   - poly *r: pointer to output polynomial
*              - const uint8_t *seed: pointer to input seed
*                                     (of length KYBER_SYMBYTES bytes)
*              - uint8_t nonce: one-byte input nonce
**************************************************/
void poly_getnoise_eta1(poly *r, const uint8_t seed[KYBER_SYMBYTES], uint8_t nonce)
{
    uint8_t buf[KYBER_ETA1 * KYBER_N / 4];
    prf(buf, sizeof(buf), seed, nonce);
    poly_cbd_eta1(r, buf);
}

/*************************************************
* Name:        poly_getnoise_eta1_4x
*
* Description: Batch sample four polynomials deterministically from a seed and nonces,
*              with output polynomials close to centered binomial distribution
*              with parameter KYBER_ETA1
*
* Arguments:   - poly *r{0,1,2,3}: pointer to output polynomial
*              - const uint8_t *seed: pointer to input seed
*                                     (of length KYBER_SYMBYTES bytes)
*              - uint8_t nonce{0,1,2,3}: one-byte input nonce
**************************************************/
void poly_getnoise_eta1_4x(poly *r0,
                           poly *r1,
                           poly *r2,
                           poly *r3,
                           const uint8_t seed[KYBER_SYMBYTES],
                           uint8_t nonce0,
                           uint8_t nonce1,
                           uint8_t nonce2,
                           uint8_t nonce3)
{
    uint8_t buf[KECCAK_WAY][KYBER_ETA1 * KYBER_N / 4];
    uint8_t extkey[KECCAK_WAY][KYBER_SYMBYTES + 1];
    memcpy(extkey[0], seed, KYBER_SYMBYTES);
    memcpy(extkey[1], seed, KYBER_SYMBYTES);
    memcpy(extkey[2], seed, KYBER_SYMBYTES);
    memcpy(extkey[3], seed, KYBER_SYMBYTES);
    extkey[0][KYBER_SYMBYTES] = nonce0;
    extkey[1][KYBER_SYMBYTES] = nonce1;
    extkey[2][KYBER_SYMBYTES] = nonce2;
    extkey[3][KYBER_SYMBYTES] = nonce3;
    shake256x4(buf[0], buf[1], buf[2], buf[3], KYBER_ETA1 * KYBER_N / 4,
               extkey[0], extkey[1], extkey[2], extkey[3], KYBER_SYMBYTES + 1);
    poly_cbd_eta1(r0, buf[0]);
    poly_cbd_eta1(r1, buf[1]);
    poly_cbd_eta1(r2, buf[2]);
    poly_cbd_eta1(r3, buf[3]);
}

/*************************************************
* Name:        poly_getnoise_eta2
*
* Description: Sample a polynomial deterministically from a seed and a nonce,
*              with output polynomial close to centered binomial distribution
*              with parameter KYBER_ETA2
*
* Arguments:   - poly *r: pointer to output polynomial
*              - const uint8_t *seed: pointer to input seed
*                                     (of length KYBER_SYMBYTES bytes)
*              - uint8_t nonce: one-byte input nonce
**************************************************/
void poly_getnoise_eta2(poly *r, const uint8_t seed[KYBER_SYMBYTES], uint8_t nonce)
{
    uint8_t buf[KYBER_ETA2 * KYBER_N / 4];
    prf(buf, sizeof(buf), seed, nonce);
    poly_cbd_eta2(r, buf);
}

/*************************************************
* Name:        poly_getnoise_eta2_4x
*
* Description: Batch sample four polynomials deterministically from a seed and nonces,
*              with output polynomials close to centered binomial distribution
*              with parameter KYBER_ETA2
*
* Arguments:   - poly *r{0,1,2,3}: pointer to output polynomial
*              - const uint8_t *seed: pointer to input seed
*                                     (of length KYBER_SYMBYTES bytes)
*              - uint8_t nonce{0,1,2,3}: one-byte input nonce
**************************************************/
void poly_getnoise_eta2_4x(poly *r0,
                           poly *r1,
                           poly *r2,
                           poly *r3,
                           const uint8_t seed[KYBER_SYMBYTES],
                           uint8_t nonce0,
                           uint8_t nonce1,
                           uint8_t nonce2,
                           uint8_t nonce3)
{
    uint8_t buf[KECCAK_WAY][KYBER_ETA2 * KYBER_N / 4];
    uint8_t extkey[KECCAK_WAY][KYBER_SYMBYTES + 1];
    memcpy(extkey[0], seed, KYBER_SYMBYTES);
    memcpy(extkey[1], seed, KYBER_SYMBYTES);
    memcpy(extkey[2], seed, KYBER_SYMBYTES);
    memcpy(extkey[3], seed, KYBER_SYMBYTES);
    extkey[0][KYBER_SYMBYTES] = nonce0;
    extkey[1][KYBER_SYMBYTES] = nonce1;
    extkey[2][KYBER_SYMBYTES] = nonce2;
    extkey[3][KYBER_SYMBYTES] = nonce3;
    shake256x4(buf[0], buf[1], buf[2], buf[3], KYBER_ETA2 * KYBER_N / 4,
               extkey[0], extkey[1], extkey[2], extkey[3], KYBER_SYMBYTES + 1);
    poly_cbd_eta2(r0, buf[0]);
    poly_cbd_eta2(r1, buf[1]);
    poly_cbd_eta2(r2, buf[2]);
    poly_cbd_eta2(r3, buf[3]);
}

/*************************************************
* Name:        poly_getnoise_eta1122_4x
*
* Description: Batch sample four polynomials deterministically from a seed and a nonces,
*              with output polynomials close to centered binomial distribution
*              with parameter KYBER_ETA1 and KYBER_ETA2
*
* Arguments:   - poly *r{0,1,2,3}: pointer to output polynomial
*              - const uint8_t *seed: pointer to input seed
*                                     (of length KYBER_SYMBYTES bytes)
*              - uint8_t nonce{0,1,2,3}: one-byte input nonce
**************************************************/
void poly_getnoise_eta1122_4x(poly *r0,
                              poly *r1,
                              poly *r2,
                              poly *r3,
                              const uint8_t seed[KYBER_SYMBYTES],
                              uint8_t nonce0,
                              uint8_t nonce1,
                              uint8_t nonce2,
                              uint8_t nonce3)
{
    uint8_t buf1[KECCAK_WAY/2][KYBER_ETA1 * KYBER_N / 4];
    uint8_t buf2[KECCAK_WAY/2][KYBER_ETA2 * KYBER_N / 4];
    uint8_t extkey[KECCAK_WAY][KYBER_SYMBYTES + 1];
    memcpy(extkey[0], seed, KYBER_SYMBYTES);
    memcpy(extkey[1], seed, KYBER_SYMBYTES);
    memcpy(extkey[2], seed, KYBER_SYMBYTES);
    memcpy(extkey[3], seed, KYBER_SYMBYTES);
    extkey[0][KYBER_SYMBYTES] = nonce0;
    extkey[1][KYBER_SYMBYTES] = nonce1;
    extkey[2][KYBER_SYMBYTES] = nonce2;
    extkey[3][KYBER_SYMBYTES] = nonce3;

    #if KYBER_ETA1 == KYBER_ETA2
    shake256x4(buf1[0], buf1[1], buf2[0], buf2[1], KYBER_ETA1 * KYBER_N / 4,
               extkey[0], extkey[1], extkey[2], extkey[3], KYBER_SYMBYTES + 1);
    #else
    shake256(buf1[0], sizeof(buf1[0]), extkey[0], sizeof(extkey[0]));
    shake256(buf1[1], sizeof(buf1[1]), extkey[1], sizeof(extkey[1]));
    shake256(buf2[0], sizeof(buf2[0]), extkey[2], sizeof(extkey[2]));
    shake256(buf2[1], sizeof(buf2[1]), extkey[3], sizeof(extkey[3]));
    #endif

    poly_cbd_eta1(r0, buf1[0]);
    poly_cbd_eta1(r1, buf1[1]);
    poly_cbd_eta2(r2, buf2[0]);
    poly_cbd_eta2(r3, buf2[1]);
}

/*************************************************
* Name:        poly_ntt
*
* Description: Computes negacyclic number-theoretic transform (NTT) of
*              a polynomial in place;
*              inputs assumed to be in normal order, output in bitreversed order
*
* Arguments:   - uint16_t *r: pointer to in/output polynomial
**************************************************/
void poly_ntt(poly *r)
{
    ntt(r->coeffs);
    poly_reduce(r);
}

/*************************************************
* Name:        poly_invntt_tomont
*
* Description: Computes inverse of negacyclic number-theoretic transform (NTT)
*              of a polynomial in place;
*              inputs assumed to be in bitreversed order, output in normal order
*
* Arguments:   - uint16_t *a: pointer to in/output polynomial
**************************************************/
void poly_invntt_tomont(poly *r)
{
    invntt(r->coeffs);
}

/*************************************************
* Name:        poly_basemul_montgomery
*
* Description: Multiplication of two polynomials in NTT domain
*
* Arguments:   - poly *r: pointer to output polynomial
*              - const poly *a: pointer to first input polynomial
*              - const poly *b: pointer to second input polynomial
**************************************************/
void poly_basemul_montgomery(poly *r, const poly *a, const poly *b)
{
    unsigned int i;
    for (i = 0; i < KYBER_N / 4; i++)
    {
        basemul(&r->coeffs[4 * i], &a->coeffs[4 * i], &b->coeffs[4 * i], zetas[64 + i]);
        basemul(&r->coeffs[4 * i + 2], &a->coeffs[4 * i + 2], &b->coeffs[4 * i + 2], -zetas[64 + i]);
    }
}

/*************************************************
* Name:        poly_tomont
*
* Description: Inplace conversion of all coefficients of a polynomial
*              from normal domain to Montgomery domain
*
* Arguments:   - poly *r: pointer to input/output polynomial
**************************************************/
void poly_tomont(poly *r)
{
    unsigned int i;
    const int16_t f = (1ULL << 32) % KYBER_Q;
    for (i = 0; i < KYBER_N; i++)
    {
        r->coeffs[i] = montgomery_reduce((int32_t)r->coeffs[i] * f);
    }
}

/*************************************************
* Name:        poly_reduce
*
* Description: Applies Barrett reduction to all coefficients of a polynomial
*              for details of the Barrett reduction see comments in reduce.c
*
* Arguments:   - poly *r: pointer to input/output polynomial
**************************************************/
void poly_reduce(poly *r)
{
    unsigned int i;
    for (i = 0; i < KYBER_N; i++)
    {
        r->coeffs[i] = barrett_reduce(r->coeffs[i]);
    }
}

/*************************************************
* Name:        poly_add
*
* Description: Add two polynomials; no modular reduction is performed
*
* Arguments: - poly *r: pointer to output polynomial
*            - const poly *a: pointer to first input polynomial
*            - const poly *b: pointer to second input polynomial
**************************************************/
void poly_add(poly *r, const poly *a, const poly *b)
{
    unsigned int i;
    for (i = 0; i < KYBER_N; i++)
    {
        r->coeffs[i] = a->coeffs[i] + b->coeffs[i];
    }
}

/*************************************************
* Name:        poly_sub
*
* Description: Subtract two polynomials; no modular reduction is performed
*
* Arguments: - poly *r:       pointer to output polynomial
*            - const poly *a: pointer to first input polynomial
*            - const poly *b: pointer to second input polynomial
**************************************************/
void poly_sub(poly *r, const poly *a, const poly *b)
{
    unsigned int i;
    for (i = 0; i < KYBER_N; i++)
    {
        r->coeffs[i] = a->coeffs[i] - b->coeffs[i];
    }
}
