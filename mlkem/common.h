/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef COMMON_H
#define COMMON_H


/*
 * C90 does not have the inline compiler directive yet.
 * We don't use it in C90 builds.
 * However, in that case the compiler warns about some inline functions in
 * header files not being used in every compilation unit that includes that
 * header. To work around it we silence that warning in that case using
 * __attribute__((unused)).
 */

/* Do not use inline for C90 builds*/
#if !defined(inline)
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L
#define INLINE inline
#define ALWAYS_INLINE __attribute__((always_inline))
#elif defined(_MSC_VER)
#define INLINE __inline
#define ALWAYS_INLINE __forceinline
#else
#define INLINE __attribute__((unused))
#define ALWAYS_INLINE
#endif

#else
#define INLINE inline
#define ALWAYS_INLINE __attribute__((always_inline))
#endif

#define DEFAULT_ALIGN 32
#if defined(_WIN32)
#define ALIGN __declspec(align(DEFAULT_ALIGN))
#define asm __asm
#else
#define asm __asm__
#define ALIGN __attribute__((aligned(DEFAULT_ALIGN)))
#endif

#define MLKEM_CONCAT_(left, right) left##right
#define MLKEM_CONCAT(left, right) MLKEM_CONCAT_(left, right)

#endif
