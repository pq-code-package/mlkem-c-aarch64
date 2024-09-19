// SPDX-License-Identifier: Apache-2.0
#ifndef ASM_H
#define ASM_H

#include <stdint.h>
#include "params.h"
#include "config.h"

#ifdef MLKEM_USE_AARCH64_ASM
void keccak_f1600_x1_scalar_slothy_opt_a55(uint64_t *state);
void keccak_f1600_x2_v84a_asm_clean(uint64_t *state);

#define keccak_f1600_x1_asm keccak_f1600_x1_scalar_slothy_opt_a55
#define keccak_f1600_x2_asm keccak_f1600_x2_v84a_asm_clean

/*
 * Logic to decide which implementation to use
 */

#if !defined(MLKEM_USE_FIPS202_ASM_FORCE)

// TODO: Allow to overwrite this logic through CFLAGS

// If v8.4-A is implemented, use basic implementation using SHA3 instructions
// from [1].
//
// [1]: Hybrid scalar/vector implementations of Keccak and SPHINCS+ on AArch64
//      https://eprint.iacr.org/2022/1243.
//
// TODO: This needs replacing with a scalar/vector hybrid on non-Apple
// systems pre Cortex-X4, as those don't have enough SIMD units implementing
// SHA3 instructions to make them worthwhile on their own.
#if defined(__ARM_FEATURE_SHA3)

#define MLKEM_USE_FIPS202_X1_ASM
#define MLKEM_USE_FIPS202_X2_ASM

// Add this if the assembly implementation expects interleaved lanes
// #define MLKEM_USE_FIPS202_X2_ASM_ZIPPED

#elif 1
// TODO: This should exclude CPUs with faster Barrel shift,
//       notably excluding Cortex-A72.

#define MLKEM_USE_FIPS202_X1_ASM

#endif /* !__ARM_FEATURE_SHA3 */

#endif /* !MLKEM_USE_FIPS202_ASM_FORCE */

#endif /* MLKEM_USE_AARCH64_ASM */

#endif
