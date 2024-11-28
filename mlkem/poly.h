// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#ifndef POLY_H
#define POLY_H

#include <stddef.h>
#include <stdint.h>
#include "cbmc.h"
#include "params.h"
#include "reduce.h"

// Absolute exclusive upper bound for the output of the inverse NTT
#define INVNTT_BOUND (8 * MLKEM_Q)

// Absolute exclusive upper bound for the output of the forward NTT
#define NTT_BOUND (8 * MLKEM_Q)

/*
 * Elements of R_q = Z_q[X]/(X^n + 1). Represents polynomial
 * coeffs[0] + X*coeffs[1] + X^2*coeffs[2] + ... + X^{n-1}*coeffs[n-1]
 */
typedef struct
{
  int16_t coeffs[MLKEM_N];
} ALIGN poly;

/*
 * INTERNAL presentation of precomputed data speeding up
 * the base multiplication of two polynomials in NTT domain.
 */
// REF-CHANGE: This structure does not exist in the reference
// implementation.
typedef struct
{
  int16_t coeffs[MLKEM_N >> 1];
} poly_mulcache;

#define poly_compress_du MLKEM_NAMESPACE(poly_compress_du)
/*************************************************
 * Name:        poly_compress_du
 *
 * Description: Compression (du bits) and subsequent serialization of a
 *polynomial
 *
 * Arguments:   - uint8_t *r: pointer to output byte array
 *                            (of length MLKEM_POLYCOMPRESSEDBYTES)
 *              - const poly *a: pointer to input polynomial
 *                  Coefficients must be unsigned canonical,
 *                  i.e. in [0,1,..,MLKEM_Q-1].
 **************************************************/
void poly_compress_du(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_DU], const poly *a)
__contract__(
  requires(memory_no_alias(r, MLKEM_POLYCOMPRESSEDBYTES_DU))
  requires(memory_no_alias(a, sizeof(poly)))
  requires(array_bound(a->coeffs, 0, (MLKEM_N - 1), 0, (MLKEM_Q - 1)))
  assigns(memory_slice(r, MLKEM_POLYCOMPRESSEDBYTES_DU))
);

#define poly_decompress_du MLKEM_NAMESPACE(poly_decompress_du)
/*************************************************
 * Name:        poly_decompress_du
 *
 * Description: De-serialization and subsequent decompression (du bits) of a
 *polynomial; approximate inverse of poly_compress_du
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES bytes)
 *
 * Upon return, the coefficients of the output polynomial are unsigned-canonical
 * (non-negative and smaller than MLKEM_Q).
 *
 **************************************************/
void poly_decompress_du(poly *r, const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_DU])
__contract__(
  requires(memory_no_alias(a, MLKEM_POLYCOMPRESSEDBYTES_DU))
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_bound(r->coeffs, 0, (MLKEM_N - 1), 0, (MLKEM_Q - 1)))
);

#define poly_compress_dv MLKEM_NAMESPACE(poly_compress_dv)
/*************************************************
 * Name:        poly_compress_dv
 *
 * Description: Compression (dv bits) and subsequent serialization of a
 *polynomial
 *
 * Arguments:   - uint8_t *r: pointer to output byte array
 *                            (of length MLKEM_POLYCOMPRESSEDBYTES_DV)
 *              - const poly *a: pointer to input polynomial
 *                  Coefficients must be unsigned canonical,
 *                  i.e. in [0,1,..,MLKEM_Q-1].
 **************************************************/
void poly_compress_dv(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_DV], const poly *a)
__contract__(
  requires(memory_no_alias(r, MLKEM_POLYCOMPRESSEDBYTES_DV))
  requires(memory_no_alias(a, sizeof(poly)))
  requires(array_bound(a->coeffs, 0, (MLKEM_N - 1), 0, (MLKEM_Q - 1)))
  assigns(object_whole(r))
);

#define poly_decompress_dv MLKEM_NAMESPACE(poly_decompress_dv)
/*************************************************
 * Name:        poly_decompress_dv
 *
 * Description: De-serialization and subsequent decompression (dv bits) of a
 *polynomial; approximate inverse of poly_compress
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_DV
 *bytes)
 *
 * Upon return, the coefficients of the output polynomial are unsigned-canonical
 * (non-negative and smaller than MLKEM_Q).
 *
 **************************************************/
void poly_decompress_dv(poly *r, const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_DV])
__contract__(
  requires(memory_no_alias(a, MLKEM_POLYCOMPRESSEDBYTES_DV))
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(object_whole(r))
  ensures(array_bound(r->coeffs, 0, (MLKEM_N - 1), 0, (MLKEM_Q - 1)))
);

#define poly_tobytes MLKEM_NAMESPACE(poly_tobytes)
/*************************************************
 * Name:        poly_tobytes
 *
 * Description: Serialization of a polynomial.
 *              Signed coefficients are converted to
 *              unsigned form before serialization.
 *
 * Arguments:   INPUT:
 *              - a: const pointer to input polynomial,
 *                with each coefficient in the range [0,1,..,Q-1]
 *              OUTPUT
 *              - r: pointer to output byte array
 *                   (of MLKEM_POLYBYTES bytes)
 **************************************************/
void poly_tobytes(uint8_t r[MLKEM_POLYBYTES], const poly *a)
__contract__(
  requires(memory_no_alias(r, MLKEM_POLYBYTES))
  requires(memory_no_alias(a, sizeof(poly)))
  requires(array_bound(a->coeffs, 0, (MLKEM_N - 1), 0, (MLKEM_Q - 1)))
  assigns(object_whole(r))
);


#define poly_frombytes MLKEM_NAMESPACE(poly_frombytes)
/*************************************************
 * Name:        poly_frombytes
 *
 * Description: De-serialization of a polynomial.
 *
 * Arguments:   INPUT
 *              - a: pointer to input byte array
 *                   (of MLKEM_POLYBYTES bytes)
 *              OUTPUT
 *              - r: pointer to output polynomial, with
 *                   each coefficient unsigned and in the range
 *                   0 .. 4095
 **************************************************/
void poly_frombytes(poly *r, const uint8_t a[MLKEM_POLYBYTES])
__contract__(
  requires(memory_no_alias(a, MLKEM_POLYBYTES))
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_bound(r->coeffs, 0, (MLKEM_N - 1), 0, 4095))
);


#define poly_frommsg MLKEM_NAMESPACE(poly_frommsg)
/*************************************************
 * Name:        poly_frommsg
 *
 * Description: Convert 32-byte message to polynomial
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *msg: pointer to input message
 **************************************************/
void poly_frommsg(poly *r, const uint8_t msg[MLKEM_INDCPA_MSGBYTES])
__contract__(
  requires(memory_no_alias(msg, MLKEM_INDCPA_MSGBYTES))
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(object_whole(r))
  ensures(array_bound(r->coeffs, 0, (MLKEM_N - 1), 0, (MLKEM_Q - 1)))
);

#define poly_tomsg MLKEM_NAMESPACE(poly_tomsg)
/*************************************************
 * Name:        poly_tomsg
 *
 * Description: Convert polynomial to 32-byte message
 *
 * Arguments:   - uint8_t *msg: pointer to output message
 *              - const poly *r: pointer to input polynomial
 *                Coefficients must be unsigned canonical
 **************************************************/
void poly_tomsg(uint8_t msg[MLKEM_INDCPA_MSGBYTES], const poly *r)
__contract__(
  requires(memory_no_alias(msg, MLKEM_INDCPA_MSGBYTES))
  requires(memory_no_alias(r, sizeof(poly)))
  requires(array_bound(r->coeffs, 0, (MLKEM_N - 1), 0, (MLKEM_Q - 1)))
  assigns(object_whole(msg))
);

#define poly_getnoise_eta1_4x MLKEM_NAMESPACE(poly_getnoise_eta1_4x)
/*************************************************
 * Name:        poly_getnoise_eta1_4x
 *
 * Description: Batch sample four polynomials deterministically from a seed
 * and nonces, with output polynomials close to centered binomial distribution
 * with parameter MLKEM_ETA1.
 *
 * Arguments:   - poly *r{0,1,2,3}: pointer to output polynomial
 *              - const uint8_t *seed: pointer to input seed
 *                                     (of length MLKEM_SYMBYTES bytes)
 *              - uint8_t nonce{0,1,2,3}: one-byte input nonce
 **************************************************/
void poly_getnoise_eta1_4x(poly *r0, poly *r1, poly *r2, poly *r3,
                           const uint8_t seed[MLKEM_SYMBYTES], uint8_t nonce0,
                           uint8_t nonce1, uint8_t nonce2, uint8_t nonce3)
/* Depending on MLKEM_K, the pointers passed to this function belong
   to the same objects, so we cannot use memory_no_alias for r0-r3.

   NOTE: Somehow it is important to use memory_no_alias() first in the
         conjunctions defining each case.
*/
#if MLKEM_K == 2
__contract__(
  requires(memory_no_alias(seed, MLKEM_SYMBYTES))
  requires( /* Case A: r0, r1 consecutive, r2, r3 consecutive */
    (memory_no_alias(r0, 2 * sizeof(poly)) && memory_no_alias(r2, 2 * sizeof(poly)) &&
     r1 == r0 + 1 && r3 == r2 + 1 && !same_object(r0, r2)))
  assigns(memory_slice(r0, sizeof(poly)))
  assigns(memory_slice(r1, sizeof(poly)))
  assigns(memory_slice(r2, sizeof(poly)))
  assigns(memory_slice(r3, sizeof(poly)))
  ensures(
    array_abs_bound(r0->coeffs,0, MLKEM_N - 1, MLKEM_ETA1)
    && array_abs_bound(r1->coeffs,0, MLKEM_N - 1, MLKEM_ETA1)
    && array_abs_bound(r2->coeffs,0, MLKEM_N - 1, MLKEM_ETA1)
    && array_abs_bound(r3->coeffs,0, MLKEM_N - 1, MLKEM_ETA1));
);
#elif MLKEM_K == 4
__contract__(
  requires(memory_no_alias(seed, MLKEM_SYMBYTES))
  requires( /* Case B: r0, r1, r2, r3 consecutive */
    (memory_no_alias(r0, 4 * sizeof(poly)) && r1 == r0 + 1 && r2 == r0 + 2 && r3 == r0 + 3))
  assigns(memory_slice(r0, sizeof(poly)))
  assigns(memory_slice(r1, sizeof(poly)))
  assigns(memory_slice(r2, sizeof(poly)))
  assigns(memory_slice(r3, sizeof(poly)))
  ensures(
    array_abs_bound(r0->coeffs,0, MLKEM_N - 1, MLKEM_ETA1)
    && array_abs_bound(r1->coeffs,0, MLKEM_N - 1, MLKEM_ETA1)
    && array_abs_bound(r2->coeffs,0, MLKEM_N - 1, MLKEM_ETA1)
    && array_abs_bound(r3->coeffs,0, MLKEM_N - 1, MLKEM_ETA1));
);
#elif MLKEM_K == 3
__contract__(
  requires(memory_no_alias(seed, MLKEM_SYMBYTES))
  requires( /* Case C: r0, r1, r2 consecutive */
 (memory_no_alias(r0, 3 * sizeof(poly)) && memory_no_alias(r3, 1 * sizeof(poly)) &&
  r1 == r0 + 1 && r2 == r0 + 2 && !same_object(r3, r0)))
  assigns(memory_slice(r0, sizeof(poly)))
  assigns(memory_slice(r1, sizeof(poly)))
  assigns(memory_slice(r2, sizeof(poly)))
  assigns(memory_slice(r3, sizeof(poly)))
  ensures(
    array_abs_bound(r0->coeffs,0, MLKEM_N - 1, MLKEM_ETA1)
    && array_abs_bound(r1->coeffs,0, MLKEM_N - 1, MLKEM_ETA1)
    && array_abs_bound(r2->coeffs,0, MLKEM_N - 1, MLKEM_ETA1)
    && array_abs_bound(r3->coeffs,0, MLKEM_N - 1, MLKEM_ETA1));
);
#endif /* MLKEM_K */

#if MLKEM_ETA1 == MLKEM_ETA2
// We only require poly_getnoise_eta2_4x for ml-kem-768 and ml-kem-1024
// where MLKEM_ETA2 = MLKEM_ETA1 = 2.
// For ml-kem-512, poly_getnoise_eta1122_4x is used instead.
#define poly_getnoise_eta2_4x poly_getnoise_eta1_4x
#endif /* MLKEM_ETA1 == MLKEM_ETA2 */

#define poly_getnoise_eta2 MLKEM_NAMESPACE(poly_getnoise_eta2)
/*************************************************
 * Name:        poly_getnoise_eta2
 *
 * Description: Sample a polynomial deterministically from a seed and a nonce,
 *              with output polynomial close to centered binomial distribution
 *              with parameter MLKEM_ETA2
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *seed: pointer to input seed
 *                                     (of length MLKEM_SYMBYTES bytes)
 *              - uint8_t nonce: one-byte input nonce
 **************************************************/
void poly_getnoise_eta2(poly *r, const uint8_t seed[MLKEM_SYMBYTES],
                        uint8_t nonce)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(memory_no_alias(seed, MLKEM_SYMBYTES))
  assigns(object_whole(r))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N - 1, MLKEM_ETA2))
);

#define poly_getnoise_eta1122_4x MLKEM_NAMESPACE(poly_getnoise_eta1122_4x)
/*************************************************
 * Name:        poly_getnoise_eta1122_4x
 *
 * Description: Batch sample four polynomials deterministically from a seed
 * and a nonces, with output polynomials close to centered binomial
 * distribution with parameter MLKEM_ETA1 and MLKEM_ETA2
 *
 * Arguments:   - poly *r{0,1,2,3}: pointer to output polynomial
 *              - const uint8_t *seed: pointer to input seed
 *                                     (of length MLKEM_SYMBYTES bytes)
 *              - uint8_t nonce{0,1,2,3}: one-byte input nonce
 **************************************************/
void poly_getnoise_eta1122_4x(poly *r0, poly *r1, poly *r2, poly *r3,
                              const uint8_t seed[MLKEM_SYMBYTES],
                              uint8_t nonce0, uint8_t nonce1, uint8_t nonce2,
                              uint8_t nonce3)
__contract__(
  requires( /* r0, r1 consecutive, r2, r3 consecutive */
 (memory_no_alias(r0, 2 * sizeof(poly)) && memory_no_alias(r2, 2 * sizeof(poly)) &&
   r1 == r0 + 1 && r3 == r2 + 1 && !same_object(r0, r2)))
  requires(memory_no_alias(seed, MLKEM_SYMBYTES))
  assigns(object_whole(r0), object_whole(r1), object_whole(r2), object_whole(r3))
  ensures(array_abs_bound(r0->coeffs,0, MLKEM_N - 1, MLKEM_ETA1)
     && array_abs_bound(r1->coeffs,0, MLKEM_N - 1, MLKEM_ETA1)
     && array_abs_bound(r2->coeffs,0, MLKEM_N - 1, MLKEM_ETA2)
     && array_abs_bound(r3->coeffs,0, MLKEM_N - 1, MLKEM_ETA2));
);

#define poly_basemul_montgomery_cached \
  MLKEM_NAMESPACE(poly_basemul_montgomery_cached)
/*************************************************
 * Name:        poly_basemul_montgomery_cached
 *
 * Description: Multiplication of two polynomials in NTT domain,
 *              using mulcache for second operand.
 *
 *              Bounds:
 *              - a is assumed to be coefficient-wise < q in absolute value.
 *
 *              The result is coefficient-wise bound by 3/2 q in absolute
 *              value.
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const poly *a: pointer to first input polynomial
 *              - const poly *b: pointer to second input polynomial
 *              - const poly_mulcache *b_cache: pointer to mulcache
 *                  for second input polynomial. Can be computed
 *                  via poly_mulcache_compute().
 **************************************************/
void poly_basemul_montgomery_cached(poly *r, const poly *a, const poly *b,
                                    const poly_mulcache *b_cache)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(memory_no_alias(a, sizeof(poly)))
  requires(memory_no_alias(b, sizeof(poly)))
  requires(memory_no_alias(b_cache, sizeof(poly_mulcache)))
  requires(array_abs_bound(a->coeffs, 0, MLKEM_N - 1, (MLKEM_Q - 1)))
  assigns(object_whole(r))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N - 1, (3 * HALF_Q - 1)))
);

#define poly_tomont MLKEM_NAMESPACE(poly_tomont)
/*************************************************
 * Name:        poly_tomont
 *
 * Description: Inplace conversion of all coefficients of a polynomial
 *              from normal domain to Montgomery domain
 *
 *              Bounds: Output < q in absolute value.
 *
 * Arguments:   - poly *r: pointer to input/output polynomial
 **************************************************/
void poly_tomont(poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N - 1, (MLKEM_Q - 1)))
);

// REF-CHANGE: This function does not exist in the reference implementation
#define poly_mulcache_compute MLKEM_NAMESPACE(poly_mulcache_compute)
/************************************************************
 * Name: poly_mulcache_compute
 *
 * Description: Computes the mulcache for a polynomial in NTT domain
 *
 *              The mulcache of a degree-2 polynomial b := b0 + b1*X
 *              in Fq[X]/(X^2-zeta) is the value b1*zeta, needed when
 *              computing products of b in Fq[X]/(X^2-zeta).
 *
 *              The mulcache of a polynomial in NTT domain -- which is
 *              a 128-tuple of degree-2 polynomials in Fq[X]/(X^2-zeta),
 *              for varying zeta, is the 128-tuple of mulcaches of those
 *              polynomials.
 *
 * Arguments: - x: Pointer to mulcache to be populated
 *            - a: Pointer to input polynomial
 ************************************************************/
// NOTE: The default C implementation of this function populates
// the mulcache with values in (-q,q), but this is not needed for the
// higher level safety proofs, and thus not part of the spec.
void poly_mulcache_compute(poly_mulcache *x, const poly *a)
__contract__(
  requires(memory_no_alias(x, sizeof(poly_mulcache)))
  requires(memory_no_alias(a, sizeof(poly)))
  assigns(object_whole(x))
);

#define poly_reduce MLKEM_NAMESPACE(poly_reduce)
/*************************************************
 * Name:        poly_reduce
 *
 * Description: Converts polynomial to _unsigned canonical_ representatives.
 *
 *              The input coefficients can be arbitrary integers in int16_t.
 *              The output coefficients are in [0,1,...,MLKEM_Q-1].
 *
 * Arguments:   - poly *r: pointer to input/output polynomial
 **************************************************/
// REF-CHANGE: The semantics of poly_reduce() is different in
//             the reference implementation, which requires
//             signed canonical output data. Unsigned canonical
//             outputs are better suited to the only remaining
//             use of poly_reduce() in the context of (de)serialization.
void poly_reduce(poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_bound(r->coeffs, 0, MLKEM_N - 1, 0, (MLKEM_Q - 1)))
);

#define poly_add MLKEM_NAMESPACE(poly_add)
/************************************************************
 * Name: poly_add
 *
 * Description: Adds two polynomials in place
 *
 * Arguments: - r: Pointer to input-output polynomial to be added to.
 *            - b: Pointer to input polynomial that should be added
 *                 to r. Must be disjoint from r.
 *
 * The coefficients of r and b must be so that the addition does
 * not overflow. Otherwise, the behaviour of this function is undefined.
 *
 ************************************************************/
// REF-CHANGE:
// The reference implementation uses a 3-argument poly_add.
// We specialize to the accumulator form to avoid reasoning about aliasing.
void poly_add(poly *r, const poly *b)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(memory_no_alias(b, sizeof(poly)))
  requires(forall(int, k0, 0, MLKEM_N - 1, (int32_t) r->coeffs[k0] + b->coeffs[k0] <= INT16_MAX))
  requires(forall(int, k1, 0, MLKEM_N - 1, (int32_t) r->coeffs[k1] + b->coeffs[k1] >= INT16_MIN))
  ensures(forall(int, k, 0, MLKEM_N - 1, r->coeffs[k] == old(*r).coeffs[k] + b->coeffs[k]))
  assigns(memory_slice(r, sizeof(poly)))
);

#define poly_sub MLKEM_NAMESPACE(poly_sub)
/*************************************************
 * Name:        poly_sub
 *
 * Description: Subtract two polynomials; no modular reduction is performed
 *
 * Arguments: - poly *r:       Pointer to input-output polynomial to be added
 *to.
 *            - const poly *b: Pointer to second input polynomial
 **************************************************/
// REF-CHANGE:
// The reference implementation uses a 3-argument poly_sub.
// We specialize to the accumulator form to avoid reasoning about aliasing.
void poly_sub(poly *r, const poly *b)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(memory_no_alias(b, sizeof(poly)))
  requires(forall(int, k0, 0, MLKEM_N - 1, (int32_t) r->coeffs[k0] - b->coeffs[k0] <= INT16_MAX))
  requires(forall(int, k1, 0, MLKEM_N - 1, (int32_t) r->coeffs[k1] - b->coeffs[k1] >= INT16_MIN))
  ensures(forall(int, k, 0, MLKEM_N - 1, r->coeffs[k] == old(*r).coeffs[k] - b->coeffs[k]))
  assigns(object_whole(r))
);

#endif
