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
/* INDENT-OFF */
__CPROVER_requires(0 <= u && u < KYBER_Q)
__CPROVER_ensures(__CPROVER_return_value < 16)
__CPROVER_ensures(__CPROVER_return_value == (((uint32_t) u * 16 + KYBER_Q / 2) / KYBER_Q) % 16);
/* INDENT-ON */

static inline uint32_t scalar_decompress_q_16 (uint32_t u)
/* INDENT-OFF */
__CPROVER_requires(0 <= u && u < 16)
__CPROVER_ensures(__CPROVER_return_value < KYBER_Q);
/* INDENT-ON */

static inline uint32_t scalar_compress_q_32   (int32_t u)
/* INDENT-OFF */
__CPROVER_requires(0 <= u && u < KYBER_Q)
__CPROVER_ensures(__CPROVER_return_value < 32)
__CPROVER_ensures(__CPROVER_return_value == (((uint32_t) u * 32 + KYBER_Q / 2) / KYBER_Q) % 32);
/* INDENT-ON */

static inline uint32_t scalar_decompress_q_32 (uint32_t u)
/* INDENT-OFF */
__CPROVER_requires(0 <= u && u < 32)
__CPROVER_ensures(__CPROVER_return_value < KYBER_Q);
/* INDENT-ON */

static inline uint16_t scalar_signed_to_unsigned_q_16 (int16_t c)
/* *INDENT-OFF* */
__CPROVER_requires(c > -KYBER_Q) // c >= -3328
__CPROVER_requires(c < KYBER_Q)  // c <= 3328
__CPROVER_ensures(__CPROVER_return_value >= 0)
__CPROVER_ensures(__CPROVER_return_value < KYBER_Q)
__CPROVER_ensures(__CPROVER_return_value == (int32_t) c + (((int32_t) c < 0) * KYBER_Q));
/* *INDENT-ON* */

#define poly_compress KYBER_NAMESPACE(poly_compress)
void poly_compress(uint8_t r[KYBER_POLYCOMPRESSEDBYTES], const poly *a)
/* *INDENT-OFF* */
__CPROVER_requires(r != NULL)
__CPROVER_requires(__CPROVER_is_fresh(r, KYBER_POLYCOMPRESSEDBYTES))
__CPROVER_requires(a != NULL)
__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(poly)))
__CPROVER_requires(__CPROVER_forall { unsigned k; (k < KYBER_N) ==> ( -KYBER_Q < a->coeffs[k] && a->coeffs[k] < KYBER_Q ) })
__CPROVER_assigns(__CPROVER_object_whole(r));
/* *INDENT-ON* */

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
/* *INDENT-OFF* */
__CPROVER_requires(a != NULL)
__CPROVER_requires(__CPROVER_is_fresh(a, KYBER_POLYCOMPRESSEDBYTES))
__CPROVER_requires(r != NULL)
__CPROVER_requires(__CPROVER_is_fresh(r, sizeof(poly)))
__CPROVER_assigns(__CPROVER_object_whole(r))
__CPROVER_ensures(__CPROVER_forall { unsigned k; (k < KYBER_N) ==> ( r->coeffs[k] >= 0 && r->coeffs[k] < KYBER_Q ) });
/* *INDENT-ON* */

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
