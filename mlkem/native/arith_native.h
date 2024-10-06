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

#ifdef SYS_X86_64_AVX2
// For now, there's only one x86_64 profile, which is essentially
// the AVX2 code from the Kyber repository
// https://github.com/pq-crystals/kyber
#include "x86_64/profiles/default.h"
#endif /* SYS_X86_64 */

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
/*************************************************
 * Name:        ntt_native
 *
 * Description: Computes negacyclic number-theoretic transform (NTT) of
 *              a polynomial in place;
 *              inputs assumed to be in normal order, output in bitreversed
 *              order
 *
 * Arguments:   - poly *p: pointer to in/output polynomial
 **************************************************/
static inline void ntt_native(poly *);
#endif /* MLKEM_USE_NATIVE_NTT */

#if defined(MLKEM_USE_NATIVE_INTT)
/*************************************************
 * Name:        intt_native
 *
 * Description: Computes inverse of negacyclic number-theoretic transform (NTT)
 *              of a polynomial in place;
 *              inputs assumed to be in bitreversed order, output in normal
 *              order.
 *
 * Arguments:   - uint16_t *a: pointer to in/output polynomial
 **************************************************/
static inline void intt_native(poly *);
#endif /* MLKEM_USE_NATIVE_INTT */

#if defined(MLKEM_USE_NATIVE_POLY_REDUCE)
/*************************************************
 * Name:        poly_reduce_native
 *
 * Description: Applies modular reduction to all coefficients of a polynomial.
 *
 * Arguments:   - poly *r: pointer to input/output polynomial
 **************************************************/
static inline void poly_reduce_native(poly *);
#endif /* MLKEM_USE_NATIVE_POLY_REDUCE */

#if defined(MLKEM_USE_NATIVE_POLY_TOMONT)
/*************************************************
 * Name:        poly_tomont_native
 *
 * Description: Inplace conversion of all coefficients of a polynomial
 *              from normal domain to Montgomery domain
 *
 * Arguments:   - poly *r: pointer to input/output polynomial
 **************************************************/
static inline void poly_tomont_native(poly *);
#endif /* MLKEM_USE_NATIVE_POLY_TOMONT */

#if defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
/*************************************************
 * Name:        poly_mulcache_compute_native
 *
 * Description: Compute multiplication cache for a polynomial.
 *              The purpose of the multiplication cache is to
 *              cache repeated computations required during a
 *              base multiplication of polynomials in NTT form.
 *              The structure of the multiplication-cache is
 *              implementation defined.
 *
 * Arguments:   INPUT:
 *              - poly: const pointer to input polynomial.
 *              OUTPUT
 *              - cache: pointer to multiplication cache
 **************************************************/
static inline void poly_mulcache_compute_native(poly_mulcache *cache,
                                                const poly *poly);
#endif /* MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE */

#if defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
static inline void polyvec_basemul_acc_montgomery_cached_native(
    poly *r, const polyvec *a, const polyvec *b,
    const polyvec_mulcache *b_cache);
#endif

#if defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
/*************************************************
 * Name:        poly_tobytes_native
 *
 * Description: Serialization of a polynomial.
 *              Signed coefficients are converted to
 *              unsigned form before serialization.
 *
 * Arguments:   INPUT:
 *              - a: const pointer to input polynomial,
 *                with each coefficient in the range -Q+1 .. Q-1
 *              OUTPUT
 *              - r: pointer to output byte array
 *                   (of KYBER_POLYBYTES bytes)
 **************************************************/
static inline void poly_tobytes_native(uint8_t r[KYBER_POLYBYTES],
                                       const poly *a);
#endif /* MLKEM_USE_NATIVE_POLY_TOBYTES */

#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
/*************************************************
 * Name:        rej_uniform_native
 *
 * Description: Run rejection sampling on uniform random bytes to generate
 *              uniform random integers mod q
 *
 * Arguments:   - int16_t *r:          pointer to output buffer
 *              - unsigned int len:    requested number of 16-bit integers
 *                                     (uniform mod q).
 *              - const uint8_t *buf:  pointer to input buffer
 *                                     (assumed to be uniform random bytes)
 *              - unsigned int buflen: length of input buffer in bytes.
 *
 * Return -1 if the native implementation does not support the input lengths.
 * Otherwise, returns non-negative number of sampled 16-bit integers (at most
 *len).
 **************************************************/
static inline int rej_uniform_native(int16_t *r, unsigned int len,
                                     const uint8_t *buf, unsigned int buflen);
#endif /* MLKEM_USE_NATIVE_REJ_UNIFORM */

#endif /* MLKEM_USE_NATIVE */
#endif /* MLKEM_ARITH_NATIVE_H */
