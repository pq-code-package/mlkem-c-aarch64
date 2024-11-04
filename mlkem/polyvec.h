// SPDX-License-Identifier: Apache-2.0
#ifndef POLYVEC_H
#define POLYVEC_H

#include <stdint.h>
#include "params.h"
#include "poly.h"

typedef struct {
  poly vec[MLKEM_K];
} ALIGN polyvec;

// REF-CHANGE: This struct does not exist in the reference implementation
typedef struct {
  poly_mulcache vec[MLKEM_K];
} polyvec_mulcache;

#define polyvec_compress MLKEM_NAMESPACE(polyvec_compress)
void polyvec_compress(uint8_t r[MLKEM_POLYVECCOMPRESSEDBYTES],
                      const polyvec *a);
#define polyvec_decompress MLKEM_NAMESPACE(polyvec_decompress)
void polyvec_decompress(polyvec *r,
                        const uint8_t a[MLKEM_POLYVECCOMPRESSEDBYTES]);

#define polyvec_tobytes MLKEM_NAMESPACE(polyvec_tobytes)
/*************************************************
 * Name:        polyvec_tobytes
 *
 * Description: Serialize vector of polynomials
 *
 * Arguments:   - uint8_t *r: pointer to output byte array
 *                            (needs space for MLKEM_POLYVECBYTES)
 *              - const polyvec *a: pointer to input vector of polynomials
 *                  Each polynomial must have coefficients in [0,..,q-1].
 **************************************************/
void polyvec_tobytes(uint8_t r[MLKEM_POLYVECBYTES],
                     const polyvec *a)  // clang-format off
REQUIRES(IS_FRESH(a, sizeof(polyvec)))
REQUIRES(IS_FRESH(r, MLKEM_POLYVECBYTES))
REQUIRES(FORALL(int, k0, 0, MLKEM_K - 1,
         ARRAY_IN_BOUNDS(int, k1, 0, (MLKEM_N - 1), a->vec[k0].coeffs, 0, (MLKEM_Q - 1))))
ASSIGNS(OBJECT_WHOLE(r));
// clang-format on

#define polyvec_frombytes MLKEM_NAMESPACE(polyvec_frombytes)
/*************************************************
 * Name:        polyvec_frombytes
 *
 * Description: De-serialize vector of polynomials;
 *              inverse of polyvec_tobytes
 *
 * Arguments:   - const polyvec *a: pointer to output vector of polynomials
 *                 (of length MLKEM_POLYVECBYTES). Output will have coefficients
 *                 normalized to [0,..,q-1].
 *              - uint8_t *r: pointer to input byte array
 **************************************************/
void polyvec_frombytes(polyvec *r,
                       const uint8_t a[MLKEM_POLYVECBYTES])  // clang-format off
REQUIRES(IS_FRESH(r, sizeof(polyvec)))
REQUIRES(IS_FRESH(a, MLKEM_POLYVECBYTES))
ENSURES(FORALL(int, k0, 0, MLKEM_K - 1,
        ARRAY_IN_BOUNDS(int, k1, 0, (MLKEM_N - 1),
                        r->vec[k0].coeffs, 0, 4095)))
ASSIGNS(OBJECT_WHOLE(r));  // clang-format on

#define polyvec_ntt MLKEM_NAMESPACE(polyvec_ntt)
void polyvec_ntt(polyvec *r);
#define polyvec_invntt_tomont MLKEM_NAMESPACE(polyvec_invntt_tomont)
void polyvec_invntt_tomont(polyvec *r);

#define polyvec_basemul_acc_montgomery \
  MLKEM_NAMESPACE(polyvec_basemul_acc_montgomery)
void polyvec_basemul_acc_montgomery(poly *r, const polyvec *a,
                                    const polyvec *b);

// REF-CHANGE: This function does not exist in the reference implementation
#define polyvec_basemul_acc_montgomery_cached \
  MLKEM_NAMESPACE(polyvec_basemul_acc_montgomery_cached)
/*************************************************
 * Name:        polyvec_basemul_acc_montgomery_cached
 *
 * Description: Scalar product of two vectors of polynomials in NTT domain,
 *              using mulcache for second operand.
 *
 *              Bounds:
 *              - a is assumed to be coefficient-wise < q in absolute value.
 *              - No bounds guarantees for the coefficients in the result.
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const polyvec *a: pointer to first input polynomial vector
 *              - const polyvec *b: pointer to second input polynomial vector
 *              - const polyvec_mulcache *b_cache: pointer to mulcache
 *                  for second input polynomial vector. Can be computed
 *                  via polyvec_mulcache_compute().
 **************************************************/
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache)
    // clang-format off
REQUIRES(IS_FRESH(r, sizeof(poly)))
REQUIRES(IS_FRESH(a, sizeof(polyvec)))
REQUIRES(IS_FRESH(b, sizeof(polyvec)))
REQUIRES(IS_FRESH(b_cache, sizeof(polyvec_mulcache)))
// Input is coefficient-wise < q in absolute value
REQUIRES(FORALL(int, k1, 0, MLKEM_K - 1,
 ARRAY_IN_BOUNDS(int, k2, 0, MLKEM_N - 1,
   a->vec[k1].coeffs, -(MLKEM_Q - 1), (MLKEM_Q - 1))))
ASSIGNS(OBJECT_WHOLE(r));
// clang-format on

// REF-CHANGE: This function does not exist in the reference implementation
#define polyvec_mulcache_compute MLKEM_NAMESPACE(polyvec_mulcache_compute)
/************************************************************
 * Name: polyvec_mulcache_compute
 *
 * Description: Computes the mulcache for a vector of polynomials in NTT domain
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
 *              The mulcache of a vector of polynomials is the vector
 *              of mulcaches of its entries.
 *
 * Arguments: - x: Pointer to mulcache to be populated
 *            - a: Pointer to input polynomial vector
 ************************************************************/
// NOTE: The default C implementation of this function populates
// the mulcache with values in (-q,q), but this is not needed for the
// higher level safety proofs, and thus not part of the spec.
void polyvec_mulcache_compute(polyvec_mulcache *x, const polyvec *a)
    // clang-format off
REQUIRES(IS_FRESH(x, sizeof(polyvec_mulcache)))
REQUIRES(IS_FRESH(a, sizeof(polyvec)))
ASSIGNS(OBJECT_WHOLE(x));
// clang-format on

#define polyvec_reduce MLKEM_NAMESPACE(polyvec_reduce)
void polyvec_reduce(polyvec *r);

#define polyvec_add MLKEM_NAMESPACE(polyvec_add)
void polyvec_add(polyvec *r, const polyvec *b);

#endif
