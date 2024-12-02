/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* FIPS202 assembly profile targeting Cortex-A55 */

#ifdef FIPS202_NATIVE_PROFILE_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define FIPS202_NATIVE_PROFILE_H

#include "../fips202_native_aarch64.h"

/*
 * On Cortex-A55, we use lazy rotation assembly for Keccak-x1,
 * but no batched assembly implementation.
 */
#define MLKEM_USE_FIPS202_X1_NATIVE
static inline void keccak_f1600_x1_native(uint64_t *state)
{
  keccak_f1600_x1_scalar_asm_opt(state);
}

#endif /* FIPS202_NATIVE_PROFILE_H */
