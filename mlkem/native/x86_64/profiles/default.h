// SPDX-License-Identifier: Apache-2.0

// ML-KEM arithmetic native profile for clean assembly

#ifdef MLKEM_ARITH_NATIVE_PROFILE_H
#error Only one MLKEM_ARITH assembly profile can be defined -- did you include multiple profiles?
#else
#define MLKEM_ARITH_NATIVE_PROFILE_H

#include <string.h>

#include "../../arith_native.h"
#include "../arith_native_x86_64.h"
#include "../consts.h"

#include "poly.h"

#define MLKEM_USE_NATIVE_REJ_UNIFORM
#define MLKEM_USE_NATIVE_NTT
#define MLKEM_USE_NATIVE_INTT
#define MLKEM_USE_NATIVE_POLY_REDUCE
#define MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#define MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#define MLKEM_USE_NATIVE_POLY_TOBYTES
#define MLKEM_USE_NATIVE_POLY_FROMBYTES

#define INVNTT_BOUND_NATIVE (KYBER_Q + 1)  // poly_reduce() is in [0,..,KYBER_Q]
#define NTT_BOUND_NATIVE (KYBER_Q + 1)     // poly_reduce() is in [0,..,KYBER_Q]

static inline int rej_uniform_native(int16_t *r, unsigned int len,
                                     const uint8_t *buf, unsigned int buflen) {
  // AVX2 implementation assumes specific buffer lengths
  if (len != KYBER_N || buflen != REJ_UNIFORM_AVX_BUFLEN) {
    return -1;
  }

  return (int)rej_uniform_avx2(r, buf);
}

static inline void ntt_native(poly *data) {
  ntt_avx2((__m256i *)data, qdata.vec);
  nttpack_avx2((__m256i *)(data->coeffs), qdata.vec);
  nttpack_avx2((__m256i *)(data->coeffs + KYBER_N / 2), qdata.vec);

  // TODO! Remove this after working out the bounds for
  // the output of the AVX2 NTT
  poly_reduce(data);
}

static inline void intt_native(poly *data) {
  nttunpack_avx2((__m256i *)(data->coeffs), qdata.vec);
  invntt_avx2((__m256i *)data, qdata.vec);

  // TODO! Remove this after working out the bounds for
  // the output of the AVX2 invNTT
  poly_reduce(data);
}

static inline void poly_reduce_native(poly *data) {
  reduce_avx2((__m256i *)data->coeffs, qdata.vec);
}

static inline void poly_mulcache_compute_native(poly_mulcache *x,
                                                const poly *y) {
  // AVX2 backend does not use mulcache
  ((void)y);

  // TODO! The mulcache is subject to the absolute bound < q
  // This needs to be dropped if the mulcache is not present.
  // Until that's done, memset to 0 to avoid failure.
  memset(x, 0, sizeof(poly_mulcache));
}

static inline void polyvec_basemul_acc_montgomery_cached_native(
    poly *r, const polyvec *a, const polyvec *b,
    const polyvec_mulcache *b_cache) {
  polyvec_basemul_acc_montgomery_cached_avx2(r, a, b, b_cache);
}

static inline void poly_tobytes_native(uint8_t r[KYBER_POLYBYTES],
                                       const poly *a) {
  poly tmp = *a;
  // TODO! This needs to be removed once all AVX2 assembly is integrated
  // and adjusted to the custom coefficient order in NTT domain
  nttunpack_avx2((__m256i *)tmp.coeffs, qdata.vec);
  ntttobytes_avx2(r, (const __m256i *)tmp.coeffs, qdata.vec);
}

static inline void poly_frombytes_native(poly *r,
                                         const uint8_t a[KYBER_POLYBYTES]) {
  nttfrombytes_avx2((__m256i *)r->coeffs, a, qdata.vec);
  nttpack_avx2((__m256i *)(r->coeffs), qdata.vec);
  nttpack_avx2((__m256i *)(r->coeffs + KYBER_N / 2), qdata.vec);
}

#endif /* MLKEM_ARITH_NATIVE_PROFILE_H */
