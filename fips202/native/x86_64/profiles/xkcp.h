// SPDX-License-Identifier: Apache-2.0

// Default FIPS202 assembly profile for AArch64 systems

#ifdef FIPS202_NATIVE_PROFILE_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define FIPS202_NATIVE_PROFILE_H

#include "../fips202_native_x86_64.h"

#if defined(MLKEM_USE_NATIVE_X86_64) && defined(SYS_X86_64_AVX2)

#include <string.h>

static void keccakx4_zip(uint64_t *state) {
  uint64_t tmp[4 * 25] ALIGN;
  for (unsigned i = 0; i < 4; i++)
    for (unsigned j = 0; j < 25; j++) {
      tmp[4 * j + i] = state[25 * i + j];
    }

  memcpy(state, tmp, sizeof(tmp));
}

static void keccakx4_unzip(uint64_t *state) {
  uint64_t tmp[4 * 25] ALIGN;
  for (unsigned i = 0; i < 4; i++)
    for (unsigned j = 0; j < 25; j++) {
      tmp[25 * i + j] = state[4 * j + i];
    }

  memcpy(state, tmp, sizeof(tmp));
}

#define MLKEM_USE_FIPS202_X4_NATIVE
static inline void keccak_f1600_x4_native(uint64_t *state) {
  // TODO: The de-interleaving should be implemented in ASM/intrinsics
  // or be hoisted into the XKCP code itself. As it stands, it's pretty
  // inefficient
  keccakx4_zip(state);
  KeccakP1600times4_PermuteAll_24rounds(state);
  keccakx4_unzip(state);
}

#endif /* MLKEM_USE_NATIVE_X86_64 && SYS_X86_64_AVX2 */

#endif /* FIPS202_NATIVE_PROFILE_H */
