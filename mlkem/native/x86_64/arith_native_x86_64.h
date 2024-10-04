// SPDX-License-Identifier: Apache-2.0
#ifndef MLKEM_AARCH64_NATIVE_H
#define MLKEM_AARCH64_NATIVE_H

#include <stdint.h>
#include "config.h"
#include "fips202.h"
#include "params.h"

#ifdef MLKEM_USE_NATIVE_X86_64

#define REJ_UNIFORM_AVX_NBLOCKS \
  ((12 * KYBER_N / 8 * (1 << 12) / KYBER_Q + SHAKE128_RATE) / SHAKE128_RATE)
#define REJ_UNIFORM_AVX_BUFLEN (REJ_UNIFORM_AVX_NBLOCKS * SHAKE128_RATE)

// TODO: Document buffer constraints
unsigned int rej_uniform_avx2(int16_t *r, const uint8_t *buf);

#endif /* MLKEM_USE_NATIVE_X86_64 */
#endif /* MLKEM_AARCH64_NATIVE_H */
