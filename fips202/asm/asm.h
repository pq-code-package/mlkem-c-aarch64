// SPDX-License-Identifier: Apache-2.0
#ifndef ASM_H
#define ASM_H

#include <stdint.h>
#include "params.h"
#include "config.h"

#ifdef MLKEM_USE_AARCH64_ASM
void keccak_f1600_x1_scalar_slothy_opt_a55(uint64_t *state);
void keccak_f1600_x2_v84a_asm_clean(uint64_t *state);
void keccak_f1600_x2_v8a_v84a_asm_hybrid(uint64_t *state);

/*
 * Logic to decide which implementation to use.
 *
 * Source of implementations:
 * [1]: Hybrid scalar/vector implementations of Keccak and SPHINCS+ on AArch64
 *      https://eprint.iacr.org/2022/1243.
 */

#if !defined(MLKEM_USE_FIPS202_ASM_FORCE)

// We use lazy-rotation assembly from [1] for CPUs implementing v8.2A+
// or later. The code itself is v8A-Neon, but lazy rotation is only beneficial
// for fast Barrel shifters. Cortex-A72, which is v8.0-A, has slow Barrel
// shifters, while Cortex-A76, which is v8.2-A, has fast Barrel shifters.
// As an approximation, we thus pick the lazy rotation assembly v8.2A+.
// If this happens to exclude CPUs with fast Barrel shifting (Cortex-A53 maybe?)
// this logic needs refining.
#if defined(__ARM_ARCH) && __ARM_ARCH >= 802
#define MLKEM_USE_FIPS202_X1_ASM
#define keccak_f1600_x1_asm keccak_f1600_x1_scalar_slothy_opt_a55
#endif /* __ARM_ARCH >= 802 */

// If v8.4-A is implemented, leverage SHA3 instructions.
//
// The optimal implementation is highly CPU-specific; see [1].
#if defined(__ARM_FEATURE_SHA3)
// For Apple-M cores, we use a plain implementation leveraging SHA3
// instructions only.
#if defined(__APPLE__)
#define MLKEM_USE_FIPS202_X2_ASM
#define keccak_f1600_x2_asm keccak_f1600_x2_v84a_asm_clean
#else /* __APPLE__ */
// Non Apple-M cores (pre Cortex-X4 at least) tend to implement SHA3
// instructions on a subset of Neon units only, in which case a hybrid
// Neon implementation is needed.
#define MLKEM_USE_FIPS202_X2_ASM
#define keccak_f1600_x2_asm keccak_f1600_x2_v8a_v84a_asm_hybrid
#endif /* __APPLE__ */

#endif /* __ARM_FEATURE_SHA3 */

#endif /* !MLKEM_USE_FIPS202_ASM_FORCE */
#endif /* MLKEM_USE_AARCH64_ASM */

#endif
