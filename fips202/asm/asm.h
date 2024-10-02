// SPDX-License-Identifier: Apache-2.0
#ifndef FIPS202_ASM_H
#define FIPS202_ASM_H

#include <stdint.h>
#include "params.h"
#include "config.h"

#ifdef MLKEM_USE_AARCH64_ASM
void keccak_f1600_x1_scalar_slothy_opt_a55(uint64_t *state);
void keccak_f1600_x1_v84a_asm_clean(uint64_t *state);
void keccak_f1600_x2_v84a_asm_clean(uint64_t *state);
void keccak_f1600_x2_v8a_v84a_asm_hybrid(uint64_t *state);
void keccak_f1600_x4_scalar_v8a_asm_hybrid_opt(uint64_t *state);
void keccak_f1600_x4_scalar_v84a_asm_hybrid_opt(uint64_t *state);
void keccak_f1600_x4_scalar_v8a_v84a_asm_hybrid_opt(uint64_t *state);
#endif /* MLKEM_USE_AARCH64_ASM */

/*
 * The FIPS202 ASM profile decides which implementation(s) of FIPS202 to use.
 *
 * If you don't change anything, the default profile will be used. This profile
 * picks implementations based on characteristics of your system visible to
 * the compiler.
 *
 * The default logic is not perfect, and you may want to pick a specific
 * profile for your target. There are three ways to do so, in descending
 * order of convenience to the user:
 * 1. Pick one of the profiles shipped with this repository.
 * 2. Provide your own profile and register it via FIPS202_ASM_PROFILE
 *    (which must be the profile's path relative to this directoru).
 * 3. Set FIPS202_ASM_MANUAL and use an adhoc profile specified via CFLAGS.
 */

// Option 2: Manually written profile
#if defined(FIPS202_ASM_PROFILE)

#define STRINGIFY_(x) #x
#define STRINGIFY(x) STRINGIFY_(x)
#include STRINGIFY(FIPS202_ASM_PROFILE)

// Option 1: Choose from shipped list of profiles
#elif !defined(FIPS202_ASM_MANUAL)

// Pick exactly one profile from the following list
#include "profiles/default.h"

#else /* !FIPS202_ASM_PROFILE && FIPS202_ASM_MANUAL */

/* Option 3: Build your own profile here, or via CFLAGS */

#endif /* !FIPS202_ASM_PROFILE && !FIPS202_ASM_MANUAL */

#endif /* FIPS202_ASM_H */
