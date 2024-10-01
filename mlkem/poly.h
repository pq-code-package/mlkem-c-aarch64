// SPDX-License-Identifier: Apache-2.0
#ifndef POLY_H
#define POLY_H

#include <stddef.h>
#include <stdint.h>
#include "params.h"
#include "cbmc.h"
#include "verify.h"

/*
 * Elements of R_q = Z_q[X]/(X^n + 1). Represents polynomial
 * coeffs[0] + X*coeffs[1] + X^2*coeffs[2] + ... + X^{n-1}*coeffs[n-1]
 */
typedef struct
{
    int16_t coeffs[KYBER_N];
} ALIGN(16) poly;

/*
 * INTERNAL presentation of precomputed data speeding up
 * the base multiplication of two polynomials in NTT domain.
 */
// REF-CHANGE: This structure does not exist in the reference
// implementation.
typedef struct
{
    int16_t coeffs[KYBER_N >> 1];
} poly_mulcache;

#define scalar_compress_q_16           KYBER_NAMESPACE(scalar_compress_q_16)
#define scalar_decompress_q_16         KYBER_NAMESPACE(scalar_decompress_q_16)
#define scalar_compress_q_32           KYBER_NAMESPACE(scalar_compress_q_32)
#define scalar_decompress_q_32         KYBER_NAMESPACE(scalar_decompress_q_32)
#define scalar_signed_to_unsigned_q_16 KYBER_NAMESPACE(scalar_signed_to_unsigned_q_16)

static inline uint32_t scalar_compress_q_16   (int32_t u)
REQUIRES(0 <= u && u <= QM1)
ENSURES(RETURN_VALUE < 16)
ENSURES(RETURN_VALUE == (((uint32_t) u * 16 + KYBER_Q / 2) / KYBER_Q) % 16);

static inline uint32_t scalar_decompress_q_16 (uint32_t u)
REQUIRES(0 <= u && u < 16)
ENSURES(RETURN_VALUE <= QM1);

static inline uint32_t scalar_compress_q_32   (int32_t u)
REQUIRES(0 <= u && u <= QM1)
ENSURES(RETURN_VALUE < 32)
ENSURES(RETURN_VALUE == (((uint32_t) u * 32 + KYBER_Q / 2) / KYBER_Q) % 32);

static inline uint32_t scalar_decompress_q_32 (uint32_t u)
REQUIRES(0 <= u && u < 32)
ENSURES(RETURN_VALUE <= QM1);

static inline uint16_t scalar_signed_to_unsigned_q_16 (int16_t c)
REQUIRES(c >= -QM1) // c >= -3328
REQUIRES(c <= QM1)  // c <= 3328
ENSURES(RETURN_VALUE >= 0 && RETURN_VALUE <= QM1)
ENSURES(RETURN_VALUE == (int32_t) c + (((int32_t) c < 0) * KYBER_Q));

#define poly_compress KYBER_NAMESPACE(poly_compress)
void poly_compress(uint8_t r[KYBER_POLYCOMPRESSEDBYTES], const poly *a)
REQUIRES(r != NULL && IS_FRESH(r, KYBER_POLYCOMPRESSEDBYTES))
REQUIRES(a != NULL && IS_FRESH(a, sizeof(poly)))
REQUIRES(ARRAY_IN_TYPE(unsigned, k, 0, (KYBER_N-1), a->coeffs, -QM1, QM1))
ASSIGNS(OBJECT_WHOLE(r));

/************************************************************
 * Name: scalar_compress_q_16
 *
 * Description: Computes round(u * 16 / q)
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
static inline uint32_t scalar_compress_q_16(int32_t u)
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
static inline uint32_t scalar_decompress_q_16(uint32_t u)
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
static inline uint32_t scalar_compress_q_32(int32_t u)
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
static inline uint32_t scalar_decompress_q_32(uint32_t u)
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
static inline uint16_t scalar_signed_to_unsigned_q_16 (int16_t c)
{
    // Add Q if c is negative, but in constant time
    cmov_int16(&c, c + KYBER_Q, c < 0);

    __CPROVER_assert(c >= 0, "scalar_signed_to_unsigned_q_16 result lower bound");
    __CPROVER_assert(c < KYBER_Q, "scalar_signed_to_unsigned_q_16 result upper bound");

    // and therefore cast to uint16_t is safe.
    return (uint16_t) c;
}

#define poly_decompress KYBER_NAMESPACE(poly_decompress)
void poly_decompress(poly *r, const uint8_t a[KYBER_POLYCOMPRESSEDBYTES])
REQUIRES(a != NULL && IS_FRESH(a, KYBER_POLYCOMPRESSEDBYTES))
REQUIRES(r != NULL && IS_FRESH(r, sizeof(poly)))
ASSIGNS(OBJECT_WHOLE(r))
ENSURES(ARRAY_IN_TYPE(unsigned, k, 0, (KYBER_N-1), r->coeffs, 0, QM1));

#define poly_tobytes KYBER_NAMESPACE(poly_tobytes)
void poly_tobytes(uint8_t r[KYBER_POLYBYTES], const poly *a);
#define poly_frombytes KYBER_NAMESPACE(poly_frombytes)
void poly_frombytes(poly *r, const uint8_t a[KYBER_POLYBYTES]);

#define poly_frommsg KYBER_NAMESPACE(poly_frommsg)
void poly_frommsg(poly *r, const uint8_t msg[KYBER_INDCPA_MSGBYTES]);
#define poly_tomsg KYBER_NAMESPACE(poly_tomsg)
void poly_tomsg(uint8_t msg[KYBER_INDCPA_MSGBYTES], const poly *r);

#define poly_getnoise_eta1_4x KYBER_NAMESPACE(poly_getnoise_eta1_4x)
void poly_getnoise_eta1_4x(poly *r0,
                           poly *r1,
                           poly *r2,
                           poly *r3,
                           const uint8_t seed[KYBER_SYMBYTES],
                           uint8_t nonce0,
                           uint8_t nonce1,
                           uint8_t nonce2,
                           uint8_t nonce3);

#define poly_getnoise_eta2 KYBER_NAMESPACE(poly_getnoise_eta2)
void poly_getnoise_eta2(poly *r, const uint8_t seed[KYBER_SYMBYTES], uint8_t nonce);

#define poly_getnoise_eta2_4x KYBER_NAMESPACE(poly_getnoise_eta2_4x)
void poly_getnoise_eta2_4x(poly *r0,
                           poly *r1,
                           poly *r2,
                           poly *r3,
                           const uint8_t seed[KYBER_SYMBYTES],
                           uint8_t nonce0,
                           uint8_t nonce1,
                           uint8_t nonce2,
                           uint8_t nonce3);

#define poly_getnoise_eta1122_4x KYBER_NAMESPACE(poly_getnoise_eta1122_4x)
void poly_getnoise_eta1122_4x(poly *r0,
                              poly *r1,
                              poly *r2,
                              poly *r3,
                              const uint8_t seed[KYBER_SYMBYTES],
                              uint8_t nonce0,
                              uint8_t nonce1,
                              uint8_t nonce2,
                              uint8_t nonce3);

#define poly_basemul_montgomery KYBER_NAMESPACE(poly_basemul_montgomery)
void poly_basemul_montgomery(poly *r, const poly *a, const poly *b);
#define poly_basemul_montgomery_cached KYBER_NAMESPACE(poly_basemul_montgomery_cached)
void poly_basemul_montgomery_cached(poly *r, const poly *a, const poly *b, const poly_mulcache *b_cache);
#define poly_tomont KYBER_NAMESPACE(poly_tomont)
void poly_tomont(poly *r);

// REF-CHANGE: This function does not exist in the reference implementation
#define poly_mulcache_compute KYBER_NAMESPACE(poly_mulcache_compute)
void poly_mulcache_compute(poly_mulcache *x, const poly *a);

#define poly_reduce KYBER_NAMESPACE(poly_reduce)
void poly_reduce(poly *r);

#define poly_add KYBER_NAMESPACE(poly_add)
void poly_add(poly *r, const poly *a, const poly *b);
#define poly_sub KYBER_NAMESPACE(poly_sub)
void poly_sub(poly *r, const poly *a, const poly *b);

#endif
