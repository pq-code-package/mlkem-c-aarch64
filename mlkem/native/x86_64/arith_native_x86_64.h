// SPDX-License-Identifier: Apache-2.0
#ifndef MLKEM_X86_64_NATIVE_H
#define MLKEM_X86_64_NATIVE_H

#include <stdint.h>
#include "config.h"
#include "fips202.h"
#include "params.h"

#if defined(MLKEM_USE_NATIVE_X86_64) && defined(SYS_X86_64_AVX2)

#include <immintrin.h>
#include <stdint.h>

#define REJ_UNIFORM_AVX_NBLOCKS \
  ((12 * KYBER_N / 8 * (1 << 12) / KYBER_Q + SHAKE128_RATE) / SHAKE128_RATE)
#define REJ_UNIFORM_AVX_BUFLEN (REJ_UNIFORM_AVX_NBLOCKS * SHAKE128_RATE)

// TODO: Document buffer constraints
unsigned int rej_uniform_avx2(int16_t *r, const uint8_t *buf);
void ntt_avx2(__m256i *r, const __m256i *qdata);
void invntt_avx2(__m256i *r, const __m256i *qdata);
void nttpack_avx2(__m256i *r, const __m256i *qdata);
void nttunpack_avx2(__m256i *r, const __m256i *qdata);
void reduce_avx2(__m256i *r, const __m256i *qdata);

#endif /* MLKEM_USE_NATIVE_X86_64 && SYS_X86_64_AVX2 */

#endif /* MLKEM_X86_64_NATIVE_H */
