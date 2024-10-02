// SPDX-License-Identifier: Apache-2.0
#ifndef ASM_H
#define ASM_H

#include <stdint.h>
#include "params.h"
#include "config.h"

#ifdef MLKEM_USE_AARCH64_ASM
void keccak_f1600_x1_scalar_slothy_opt_a55(uint64_t *state);
void keccak_f1600_x1_v84a_asm_clean(uint64_t *state);
void keccak_f1600_x2_v84a_asm_clean(uint64_t *state);
void keccak_f1600_x2_v8a_v84a_asm_hybrid(uint64_t *state);
void keccak_f1600_x4_scalar_v8a_asm_hybrid(uint64_t *state);
void keccak_f1600_x4_scalar_v84a_asm_hybrid(uint64_t *state);
void keccak_f1600_x4_scalar_v8a_v84a_asm_hybrid(uint64_t *state);

/*
 * Logic to decide which implementation to use.
 *
 * Source of implementations:
 * [1]: Hybrid scalar/vector implementations of Keccak and SPHINCS+ on AArch64
 *      https://eprint.iacr.org/2022/1243.
 */

#if !defined(MLKEM_USE_FIPS202_ASM_FORCE)

// Keccak-f1600
//
// - On Arm-based Apple CPUs, we pick a pure Neon implementation.
// - Otherwise, unless SYS_AARCH64_SLOW_BARREL_SHIFTER is set,
//   we use lazy-rotation scalar assembly from [1].
// - Otherwise, if SYS_AARCH64_SLOW_BARREL_SHIFTER is set, we
//   fall back to the standard C implementation.
#if defined(__ARM_FEATURE_SHA3) && defined(__APPLE__)
#define MLKEM_USE_FIPS202_X1_ASM
#define keccak_f1600_x1_asm keccak_f1600_x1_v84a_asm_clean
#elif !defined(SYS_AARCH64_SLOW_BARREL_SHIFTER)
#define MLKEM_USE_FIPS202_X1_ASM
#define keccak_f1600_x1_asm keccak_f1600_x1_scalar_slothy_opt_a55
#endif /* !SYS_AARCH64_SLOW_BARREL_SHIFTER */

// Keccak-f1600x2/x4
//
// The optimal implementation is highly CPU-specific; see [1].
//
// For now, if v8.4-A is not implemented, we fall back to Keccak-f1600.
// If v8.4-A is implemented and we are on an Apple CPU, we use a plain
// Neon-based implementation.
// If v8.4-A is implemented and we are not on an Apple CPU, we use a
// Neon/Neon hybrid.
// The reason for this distinction is that Apple CPUs appear to implement
// the SHA3 instructions on all SIMD units, while Arm CPUs prior to Cortex-X4
// don't, and ordinary Neon instructions are still needed.
#if defined(__ARM_FEATURE_SHA3)
// For Apple-M cores, we use a plain implementation leveraging SHA3
// instructions only.
#if defined(__APPLE__)
#define MLKEM_USE_FIPS202_X2_ASM
#define keccak_f1600_x2_asm keccak_f1600_x2_v84a_asm_clean
#else /* __APPLE__ */
#define MLKEM_USE_FIPS202_X4_ASM
#define keccak_f1600_x4_asm keccak_f1600_x4_scalar_v8a_v84a_asm_hybrid
#endif /* __APPLE__ */

#else /* __ARM_FEATURE_SHA3 */

#define MLKEM_USE_FIPS202_X4_ASM
#define keccak_f1600_x4_asm keccak_f1600_x4_scalar_v8a_asm_hybrid

#endif /* __ARM_FEATURE_SHA3 */

#endif /* !MLKEM_USE_FIPS202_ASM_FORCE */
#endif /* MLKEM_USE_AARCH64_ASM */

#endif
