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

#define INVNTT_BOUND INT16_MAX  // TODO!!!
#define NTT_BOUND    INT16_MAX  // TODO!!!

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
  poly_reduce(data);
}

static inline void intt_native(poly *data) {
  nttunpack_avx2((__m256i *)(data->coeffs), qdata.vec);
  invntt_avx2((__m256i *)data, qdata.vec);
  poly_reduce(data);
}

#endif /* MLKEM_ARITH_NATIVE_PROFILE_H */
