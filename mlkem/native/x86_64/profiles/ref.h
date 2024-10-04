// SPDX-License-Identifier: Apache-2.0

// ML-KEM arithmetic native profile for clean assembly

#ifdef MLKEM_ARITH_NATIVE_PROFILE_H
#error Only one MLKEM_ARITH assembly profile can be defined -- did you include multiple profiles?
#else
#define MLKEM_ARITH_NATIVE_PROFILE_H

#include "../../arith_native.h"
#include "../arith_native_x86_64.h"

#define MLKEM_USE_NATIVE_REJ_UNIFORM

static inline int rej_uniform_native(int16_t *r, unsigned int len,
                                     const uint8_t *buf, unsigned int buflen) {
  // AVX2 implementation assumes specific buffer lengths
  if (len != KYBER_N || buflen != REJ_UNIFORM_AVX_BUFLEN) {
    return -1;
  }

  return (int)rej_uniform_avx2(r, buf);
}

#endif /* MLKEM_ARITH_NATIVE_PROFILE_H */
