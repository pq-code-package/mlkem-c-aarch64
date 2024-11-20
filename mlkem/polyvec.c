// SPDX-License-Identifier: Apache-2.0
#include "polyvec.h"
#include <stdint.h>
#include "arith_native.h"
#include "config.h"
#include "ntt.h"
#include "params.h"
#include "poly.h"

#include "debug/debug.h"
void polyvec_compress_du(uint8_t r[MLKEM_POLYVECCOMPRESSEDBYTES_DU],
                         const polyvec *a) {
  unsigned int i;
  POLYVEC_UBOUND(a, MLKEM_Q);

  for (i = 0; i < MLKEM_K; i++)  // clang-format off
    ASSIGNS(i, OBJECT_WHOLE(r))
    INVARIANT(i <= MLKEM_K)
    // clang-format on
    {
      poly_compress_du(r + i * MLKEM_POLYCOMPRESSEDBYTES_DU, &a->vec[i]);
    }
}

void polyvec_decompress_du(polyvec *r,
                           const uint8_t a[MLKEM_POLYVECCOMPRESSEDBYTES_DU]) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++)  // clang-format off
    ASSIGNS(i, OBJECT_WHOLE(r))
    INVARIANT(i <= MLKEM_K)
    // clang-format on
    {
      poly_decompress_du(&r->vec[i], a + i * MLKEM_POLYCOMPRESSEDBYTES_DU);
    }

  POLYVEC_UBOUND(r, MLKEM_Q);
}

void polyvec_tobytes(uint8_t r[MLKEM_POLYVECBYTES], const polyvec *a) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++)  // clang-format off
    ASSIGNS(i, OBJECT_WHOLE(r))
    INVARIANT(i <= MLKEM_K)  // clang-format on
    {
      poly_tobytes(r + i * MLKEM_POLYBYTES, &a->vec[i]);
    }
}

void polyvec_frombytes(polyvec *r, const uint8_t a[MLKEM_POLYVECBYTES]) {
  int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_frombytes(&r->vec[i], a + i * MLKEM_POLYBYTES);
  }
}

void polyvec_ntt(polyvec *r) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_ntt(&r->vec[i]);
  }
}

void polyvec_invntt_tomont(polyvec *r) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_invntt_tomont(&r->vec[i]);
  }
}

/*************************************************
 * Name:        polyvec_basemul_acc_montgomery
 *
 * Description: Multiply elements of a and b in NTT domain, accumulate into r,
 *              and multiply by 2^-16.
 *
 *              Bounds:
 *              - a is assumed to be coefficient-wise < q in absolute value.
 *              - b is assumed to be the output of a forward NTT and
 *                thus coefficient-wise bound by NTT_BOUND
 *              - b_cache is assumed to be coefficient-wise bound by
 *                MLKEM_Q.
 *
 * Arguments: - poly *r: pointer to output polynomial
 *            - const polyvec *a: pointer to first input vector of polynomials
 *            - const polyvec *b: pointer to second input vector of polynomials
 *            - const polyvec_mulcache *b_cache: mulcache for b
 **************************************************/
#if !defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache) {
  POLYVEC_BOUND(a, MLKEM_Q);
  POLYVEC_BOUND(b, NTT_BOUND);
  POLYVEC_BOUND(b_cache, MLKEM_Q);

  int i;
  poly t;

  poly_basemul_montgomery_cached(r, &a->vec[0], &b->vec[0], &b_cache->vec[0]);
  for (i = 1; i < MLKEM_K; i++)  // clang-format off
    ASSIGNS(i, t, OBJECT_WHOLE(r))
    INVARIANT(i >= 1 && i <= MLKEM_K)
    INVARIANT(ARRAY_ABS_BOUND(r->coeffs, 0, MLKEM_N - 1, i * (3 * HALF_Q - 1)))
    DECREASES(MLKEM_K - i)
    // clang-format on
    {
      poly_basemul_montgomery_cached(&t, &a->vec[i], &b->vec[i],
                                     &b_cache->vec[i]);
      poly_add(r, &t);
      // abs bounds: < (i+1) * 3/2 * q
    }

  // Those bounds are true for the C implementation, but not needed
  // in the higher level bounds reasoning. It is thus best to omit
  // them from the spec to not unnecessarily constraint native implementations.
  ASSERT(ARRAY_ABS_BOUND(r->coeffs, 0, MLKEM_N - 1, MLKEM_K * (3 * HALF_Q - 1)),
         "polyvec_basemul_acc_montgomery_cached output bounds");
  // TODO: Integrate CBMC assertion into POLY_BOUND if CBMC is set
  POLY_BOUND(r, MLKEM_K * 3 * HALF_Q);
}
#else  /* !MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache) {
  POLYVEC_BOUND(a, MLKEM_Q);
  POLYVEC_BOUND(b, NTT_BOUND);
  POLYVEC_BOUND(b_cache, MLKEM_Q);
  polyvec_basemul_acc_montgomery_cached_native(r, a, b, b_cache);
}
#endif /* MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */

/*************************************************
 * Name:        polyvec_basemul_acc_montgomery
 *
 * Description: Multiply elements of a and b in NTT domain, accumulate into r,
 *              and multiply by 2^-16.
 *
 * Arguments: - poly *r: pointer to output polynomial
 *            - const polyvec *a: pointer to first input vector of polynomials
 *            - const polyvec *b: pointer to second input vector of polynomials
 **************************************************/
void polyvec_basemul_acc_montgomery(poly *r, const polyvec *a,
                                    const polyvec *b) {
  polyvec_mulcache b_cache;
  polyvec_mulcache_compute(&b_cache, b);
  polyvec_basemul_acc_montgomery_cached(r, a, b, &b_cache);
}

/*************************************************
 * Name:        polyvec_mulcache_compute
 *
 * Description: Precompute values speeding up
 *              base multiplications of polynomials
 *              in NTT domain.
 *
 * Arguments: - polyvec_mulcache *x: pointer to output cache.
 *            - const poly *a: pointer to input polynomial
 **************************************************/
void polyvec_mulcache_compute(polyvec_mulcache *x, const polyvec *a) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_mulcache_compute(&x->vec[i], &a->vec[i]);
  }
}


/*************************************************
 * Name:        polyvec_reduce
 *
 * Description: Applies Barrett reduction to each coefficient
 *              of each element of a vector of polynomials;
 *              for details of the Barrett reduction see comments in reduce.c
 *
 * Arguments:   - polyvec *r: pointer to input/output polynomial
 **************************************************/
void polyvec_reduce(polyvec *r) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_reduce(&r->vec[i]);
  }
}

void polyvec_add(polyvec *r, const polyvec *b) {
  int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_add(&r->vec[i], &b->vec[i]);
  }
}

void polyvec_tomont(polyvec *r) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_tomont(&r->vec[i]);
  }
}
