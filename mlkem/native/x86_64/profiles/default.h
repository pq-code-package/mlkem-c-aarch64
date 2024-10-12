// SPDX-License-Identifier: Apache-2.0

// ML-KEM arithmetic native profile for clean assembly

#ifdef MLKEM_ARITH_NATIVE_PROFILE_H
#error Only one MLKEM_ARITH assembly profile can be defined -- did you include multiple profiles?
#else
#define MLKEM_ARITH_NATIVE_PROFILE_H

#include "../../arith_native.h"
#include "../arith_native_x86_64.h"
#include "../consts.h"

#include "poly.h"

#define MLKEM_USE_NATIVE_REJ_UNIFORM
#define MLKEM_USE_NATIVE_NTT
#define MLKEM_USE_NATIVE_INTT
#define MLKEM_USE_NATIVE_POLY_REDUCE

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

#endif /* MLKEM_ARITH_NATIVE_PROFILE_H */
