/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef FIPS202_NATIVE_H
#define FIPS202_NATIVE_H

#include <stdint.h>
#include "common.h"

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
static INLINE void keccak_f1600_x1_native(uint64_t *state);
#endif
#if defined(MLKEM_USE_FIPS202_X2_NATIVE)
static INLINE void keccak_f1600_x2_native(uint64_t *state);
#endif
#if defined(MLKEM_USE_FIPS202_X4_NATIVE)
static INLINE void keccak_f1600_x4_native(uint64_t *state);
#endif

#endif /* FIPS202_NATIVE_H */
