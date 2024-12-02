/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef FIPS202_NATIVE_H
#define FIPS202_NATIVE_H

#include <stdint.h>
#include "config.h"
#include "params.h"

#if defined(MLKEM_USE_NATIVE)

/*
 * FIPS202 native profile
 *
 * The profile decides which implementation(s) of FIPS202 to use.
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
 * 3. Set FIPS202_NATIVE_MANUAL and use an adhoc profile specified via CFLAGS.
 */

/* Option 2: Manually written profile */
#if defined(FIPS202_NATIVE_PROFILE)

#define STRINGIFY_(x) #x
#define STRINGIFY(x) STRINGIFY_(x)
#include STRINGIFY(FIPS202_NATIVE_PROFILE)

/* Option 1: Choose from shipped list of profiles */
#elif !defined(FIPS202_NATIVE_MANUAL)

#ifdef SYS_AARCH64
/* Pick exactly one profile from the following list */
#include "aarch64/profiles/default.h"
/* #include "aarch64/profiles/cortex_a55.h" */
#endif

#if defined(SYS_X86_64) && defined(SYS_X86_64_AVX2)
#include "x86_64/profiles/xkcp.h"
#endif

#else /* !FIPS202_NATIVE_PROFILE && FIPS202_NATIVE_MANUAL */

/* Option 3: Build your own profile here, or via CFLAGS */

#endif /* !FIPS202_NATIVE_PROFILE && !FIPS202_NATIVE_MANUAL */

/*
 * FIPS202 native interface
 */

/*
 * Those functions are meant to be trivial wrappers around
 *  the chosen native implementation. The are static inline
 * to avoid unnecessary calls.
 * The macro before each declaration controls whether a native
 * implementation is present.
 */

#if defined(MLKEM_USE_FIPS202_X1_NATIVE)
static inline void keccak_f1600_x1_native(uint64_t *state);
#endif
#if defined(MLKEM_USE_FIPS202_X2_NATIVE)
static inline void keccak_f1600_x2_native(uint64_t *state);
#endif
#if defined(MLKEM_USE_FIPS202_X4_NATIVE)
static inline void keccak_f1600_x4_native(uint64_t *state);
#endif

#endif /* MLKEM_USE_NATIVE */
#endif /* FIPS202_NATIVE_H */
