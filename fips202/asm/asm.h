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
// For now, we only use this implementation on Apple M-series, as other
// CPUs (pre Cortex-X4) tend to implement SHA3 instructions on a subset
// of Neon units only, in which case a hybrid or the scalar implementation
// should be used. As we don't yet have the hybrid here, we fall back to
// scalar.
#if defined(__ARM_FEATURE_SHA3) && defined(__APPLE__)

#define MLKEM_USE_FIPS202_X1_ASM
#define MLKEM_USE_FIPS202_X2_ASM

// Add this if the assembly implementation expects interleaved lanes
// #define MLKEM_USE_FIPS202_X2_ASM_ZIPPED

// We use lazy-rotation assembly from [1] for CPUs implementing v8.2A+
// or later. The code itself is v8A-Neon, but lazy rotation is only beneficial
// for fast Barrel shifters. Cortex-A72, which is v8.0-A, has slow Barrel
// shifters, while Cortex-A76, which is v8.2-A, has fast Barrel shifters.
// As an approximation, we thus pick the lazy rotation assembly v8.2A+.
// If this happens to exclude CPUs with fast Barrel shifting (Cortex-A53 maybe?)
// this logic needs refining.
#elif defined(__ARM_ARCH) && __ARM_ARCH >= 802

#define MLKEM_USE_FIPS202_X1_ASM

#endif /* !__ARM_FEATURE_SHA3 && __ARM_ARCH >= 802 */

#endif /* !MLKEM_USE_FIPS202_ASM_FORCE */

#endif /* MLKEM_USE_AARCH64_ASM */

#endif
