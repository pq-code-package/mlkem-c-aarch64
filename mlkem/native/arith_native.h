// SPDX-License-Identifier: Apache-2.0
#ifndef MLKEM_ARITH_NATIVE_H
#define MLKEM_ARITH_NATIVE_H

#include <stdint.h>
#include "config.h"
#include "params.h"

#if defined(MLKEM_USE_NATIVE)

#include "poly.h"
#include "polyvec.h"

/*
 * MLKEM native arithmetic profile
 *
 * The profile decides which implementation(s) of FIPS202 to use.
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

#else /* !MLKEM_ARITH_NATIVE_PROFILE && MLKEM_ARITH_NATIVE_MANUAL */

/* Option 3: Build your own profile here, or via CFLAGS */

#endif /* !MLKEM_ARITH_NATIVE_PROFILE && !MLKEM_ARITH_NATIVE_MANUAL */

/*
 * MLKEM native arithmetic interface
 */

// Those functions are meant to be trivial wrappers around
// the chosen native implementation. The are static inline
// to avoid unnecessary calls.
//
// The macro before each declaration controls whether a native
// implementation is present.

#if defined(MLKEM_USE_NATIVE_NTT)
static inline void ntt_native(poly *);
#endif
#if defined(MLKEM_USE_NATIVE_INTT)
static inline void intt_native(poly *);
#endif
#if defined(MLKEM_USE_NATIVE_POLY_REDUCE)
static inline void poly_reduce_native(poly *);
#endif
#if defined(MLKEM_USE_NATIVE_POLY_TOMONT)
static inline void poly_tomont_native(poly *);
#endif
#if defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
static inline void poly_mulcache_compute_native(poly_mulcache *, const poly *,
                                                const int16_t *,
                                                const int16_t *);
#endif
#if defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
static inline void polyvec_basemul_acc_montgomery_cached_native(
    poly *r, const polyvec *a, const polyvec *b,
    const polyvec_mulcache *b_cache);
#endif

#if defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
static inline void poly_tobytes_native(uint8_t r[KYBER_POLYBYTES],
                                       const poly *a);
#endif

#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
static inline unsigned int rej_uniform_native(int16_t *r, unsigned int len,
                                              const uint8_t *buf,
                                              unsigned int *buf_consumed,
                                              unsigned int buflen);
#endif

#endif /* MLKEM_USE_NATIVE */
#endif /* MLKEM_ARITH_NATIVE_H */
