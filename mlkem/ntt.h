// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#ifndef NTT_H
#define NTT_H

#include <stdint.h>
#include "arith_native.h"
#include "cbmc.h"
#include "params.h"
#include "poly.h"
#include "reduce.h"

#define zetas MLKEM_NAMESPACE(zetas)
extern const int16_t zetas[128];

/*************************************************
 * Name:        poly_ntt
 *
 * Description: Computes negacyclic number-theoretic transform (NTT) of
 *              a polynomial in place.
 *
 *              The input is assumed to be in normal order and
 *              coefficient-wise bound by MLKEM_Q in absolute value.
 *
 *              The output polynomial is in bitreversed order, and
 *              coefficient-wise bound by NTT_BOUND in absolute value.
 *
 *              (NOTE: Sometimes the input to the NTT is actually smaller,
 *               which gives better bounds.)
 *
 * Arguments:   - poly *p: pointer to in/output polynomial
 **************************************************/

#define poly_ntt MLKEM_NAMESPACE(poly_ntt)
void poly_ntt(poly *r)  // clang-format off
REQUIRES(IS_FRESH(r, sizeof(poly)))
REQUIRES(ARRAY_ABS_BOUND(r->coeffs, 0, MLKEM_N - 1, MLKEM_Q - 1))
ASSIGNS(OBJECT_UPTO(r, sizeof(poly)))
ENSURES(ARRAY_ABS_BOUND(r->coeffs, 0, MLKEM_N - 1, NTT_BOUND - 1));
// clang-format on

/*************************************************
 * Name:        poly_invntt_tomont
 *
 * Description: Computes inverse of negacyclic number-theoretic transform (NTT)
 *              of a polynomial in place;
 *              inputs assumed to be in bitreversed order, output in normal
 *              order
 *
 *              The input is assumed to be in bitreversed order, and can
 *              have arbitrary coefficients in int16_t.
 *
 *              The output polynomial is in normal order, and
 *              coefficient-wise bound by INVNTT_BOUND in absolute value.
 *
 * Arguments:   - uint16_t *a: pointer to in/output polynomial
 **************************************************/
#define poly_invntt_tomont MLKEM_NAMESPACE(poly_invntt_tomont)
void poly_invntt_tomont(poly *r)  // clang-format off
REQUIRES(IS_FRESH(r, sizeof(poly)))
ASSIGNS(OBJECT_UPTO(r, sizeof(poly)))
ENSURES(ARRAY_ABS_BOUND(r->coeffs, 0, MLKEM_N - 1, INVNTT_BOUND - 1));
// clang-format on

#define basemul_cached MLKEM_NAMESPACE(basemul_cached)
/************************************************************
 * Name: basemul_cached
 *
 * Description: Computes a representative modulo q of
 *              (a0*b0 + a1*b_cached, a0*b1 + a1*b0)/65536
 *
 *              If b_cached is b1*zeta, this represents the
 *              product of (a0 + a1*X) and (b0 + b1*X) in
 *              Fq[X]/(X^2 - zeta).
 *
 * Arguments: - r: Pointer to output polynomial
 *                   Upon return, coefficients are bound by
 *                   3*(q+1)/2 in absolute value.
 *            - a: Pointer to first input polynomial
 *                   Must be coefficient-wise < q in absolute value.
 *            - b: Pointer to second input polynomial
 *                   Can have arbitrary int16_t coefficients
 *            - b_cached: Some precomputed value, typically derived from
 *                   b1 and a twiddle factor. Can be an arbitary int16_t.
 ************************************************************/
void basemul_cached(int16_t r[2], const int16_t a[2], const int16_t b[2],
                    int16_t b_cached)  // clang-format off
REQUIRES(IS_FRESH(r, 2 * sizeof(int16_t)))
REQUIRES(IS_FRESH(a, 2 * sizeof(int16_t)))
REQUIRES(IS_FRESH(b, 2 * sizeof(int16_t)))
REQUIRES(ARRAY_ABS_BOUND(a, 0, 1, MLKEM_Q - 1))
ASSIGNS(OBJECT_UPTO(r, 2 * sizeof(int16_t)))
ENSURES(ARRAY_ABS_BOUND(r, 0, 1, (3 * HALF_Q - 1)));
// clang-format on


#endif
