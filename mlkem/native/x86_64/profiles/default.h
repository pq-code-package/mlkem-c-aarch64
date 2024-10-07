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
#define MLKEM_USE_NATIVE_POLY_FROMBYTES
#define MLKEM_USE_NATIVE_POLY_TOBYTES

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

static inline void poly_frombytes_native(poly *a,
                                         const uint8_t r[KYBER_POLYBYTES]) {
  poly_frombytes_avx2((__m256i *)(a->coeffs), r, qdata.vec);
  nttpack_avx2((__m256i *)(a->coeffs), qdata.vec);
  nttpack_avx2((__m256i *)(a->coeffs + KYBER_N / 2), qdata.vec);
}

static inline void poly_tobytes_native(uint8_t r[KYBER_POLYBYTES],
                                       const poly *a) {
  poly tmp;
  for (unsigned int i = 0; i < KYBER_N; i++) {
    tmp.coeffs[i] = scalar_signed_to_unsigned_q_16(a->coeffs[i]);
  }
  nttunpack_avx2((__m256i *)(tmp.coeffs), qdata.vec);
  poly_tobytes_avx2(r, (const __m256i *)&tmp, qdata.vec);
}

#endif /* MLKEM_ARITH_NATIVE_PROFILE_H */
