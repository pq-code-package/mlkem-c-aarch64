// SPDX-License-Identifier: Apache-2.0
#ifndef MLKEM_ARITH_NATIVE_PROFILE_CHOICE_H
#define MLKEM_ARITH_NATIVE_PROFILE_CHOICE_H

#include <stdint.h>
#include "config.h"
#include "params.h"

#if defined(MLKEM_USE_NATIVE)
#include "poly.h"
#include "polyvec.h"

/*
 * MLKEM native arithmetic profile
 *
 * The profile decides which implementation(s) of the arithmetic backend to use.
 *
 * If you don't change anything, the default profile will be used. This profile
 * picks implementations based on characteristics of your system visible to
 * the compiler.
 *
 * If you want to pick a specific profile for your target, there are three ways
 * to do so, in descending order of convenience to the user:
 * 1. Pick one of the profiles shipped with this repository.
 * 2. Provide your own profile and register it via MLKEM_ARITH_NATIVE_PROFILE
 *    (which must be the profile's path relative to this directoru).
 * 3. Set MLKEM_ARITH_NATIVE_MANUAL and use an adhoc profile specified via
 * CFLAGS.
 */

// Option 2: Manually written profile
#if defined(MLKEM_ARITH_NATIVE_PROFILE)

#define STRINGIFY_(x) #x
#define STRINGIFY(x) STRINGIFY_(x)
#include STRINGIFY(MLKEM_ARITH_NATIVE_PROFILE)

// Option 1: Choose from shipped list of profiles
#elif !defined(MLKEM_ARITH_NATIVE_MANUAL)

#ifdef SYS_AARCH64
// For now, we only have clean and opt profiles.
// In the future, this is likely to branch further depending
// on the microarchitecture.
#if defined(MLKEM_USE_NATIVE_AARCH64_CLEAN)
#include "aarch64/profiles/clean.h"
#else /* MLKEM_USE_NATIVE_AARCH64_CLEAN */
#include "aarch64/profiles/opt.h"
#endif /* !MLKEM_USE_NATIVE_AARCH64_CLEAN */
#endif /* SYS_AARCH64 */

#ifdef SYS_X86_64_AVX2
// For now, there's only one x86_64 profile, which is essentially
// the AVX2 code from the Kyber repository
// https://github.com/pq-crystals/kyber
#include "x86_64/profiles/default.h"
#endif /* SYS_X86_64 */

#else /* !MLKEM_ARITH_NATIVE_PROFILE && MLKEM_ARITH_NATIVE_MANUAL */

/* Option 3: Build your own profile here, or via CFLAGS */

#endif /* !MLKEM_ARITH_NATIVE_PROFILE && !MLKEM_ARITH_NATIVE_MANUAL */

#endif /* MLKEM_USE_NATIVE */
#endif /* MLKEM_ARITH_NATIVE_PROFILE_CHOICE_H */
