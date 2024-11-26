// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#ifndef COMMON_H
#define COMMON_H

#define DEFAULT_ALIGN 32
#if defined(_WIN32)
#define ALIGN __declspec(align(DEFAULT_ALIGN))
#define ALWAYS_INLINE __forceinline
#else
#define ALIGN __attribute__((aligned(DEFAULT_ALIGN)))
#define ALWAYS_INLINE __attribute__((always_inline))
#endif

#define asm __asm__

#define MLKEM_CONCAT_(left, right) left##right
#define MLKEM_CONCAT(left, right) MLKEM_CONCAT_(left, right)

#endif
