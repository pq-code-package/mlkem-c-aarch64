/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* Default FIPS202 assembly profile for AArch64 systems */

#ifdef FIPS202_NATIVE_PROFILE_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define FIPS202_NATIVE_PROFILE_H

#include "../fips202_native_x86_64.h"

#if defined(MLKEM_USE_NATIVE_X86_64) && defined(SYS_X86_64_AVX2)

#define MLKEM_USE_FIPS202_X4_NATIVE
static INLINE void keccak_f1600_x4_native(uint64_t *state)
{
  KeccakP1600times4_PermuteAll_24rounds(state);
}

#endif /* MLKEM_USE_NATIVE_X86_64 && SYS_X86_64_AVX2 */

#endif /* FIPS202_NATIVE_PROFILE_H */
