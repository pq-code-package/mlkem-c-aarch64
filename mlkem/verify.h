// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#ifndef VERIFY_H
#define VERIFY_H

#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include "arith_native.h"
#include "cbmc.h"
#include "params.h"

// If a native backend is used, we include the native implementations from the
// backend as those are using inline assembly. This guarantees that these
// gadgets are constant-time, but also allows the compiler to inline them.
// Otherwise, we use the reference code (verify.c) in a separate compilation
// unit.
#if defined(MLKEM_USE_NATIVE_VERIFY)
#include "cpucap.h"

#if defined(SYS_AARCH64)
#include "verify-aarch64.h"
#endif /* SYS_AARCH64 */

#if defined(SYS_X86_64)
#include "verify-x86_64.h"
#endif /* SYS_X86_64 */
#endif


#define verify MLKEM_NAMESPACE(verify)
/*************************************************
 * Name:        verify
 *
 * Description: Compare two arrays for equality in constant time.
 *
 * Arguments:   const uint8_t *a: pointer to first byte array
 *              const uint8_t *b: pointer to second byte array
 *              size_t len:       length of the byte arrays
 *
 * Returns 0 if the byte arrays are equal, 1 otherwise
 **************************************************/
#if !defined(MLKEM_USE_NATIVE_VERIFY)
int verify(const uint8_t *a, const uint8_t *b, const size_t len)
__contract__(
  requires(memory_no_alias(a, len))
  requires(memory_no_alias(b, len))
  requires(len <= INT_MAX)
  ensures(return_value == (1 - forall(int, i, 0, ((int)len - 1), (a[i] == b[i]))))
);
#else  /* MLKEM_USE_NATIVE_VERIFY */
static inline int verify(const uint8_t *a, const uint8_t *b, const size_t len)
{
  return verify_native(a, b, len);
}
#endif /* MLKEM_USE_NATIVE_VERIFY */

#define cmov MLKEM_NAMESPACE(cmov)
/*************************************************
 * Name:        cmov
 *
 * Description: Copy len bytes from x to r if b is 1;
 *              don't modify x if b is 0. Requires b to be in {0,1};
 *              assumes two's complement representation of negative integers.
 *              Runs in constant time.
 *
 * Arguments:   uint8_t *r:       pointer to output byte array
 *              const uint8_t *x: pointer to input byte array
 *              size_t len:       Amount of bytes to be copied
 *              uint8_t b:        Condition bit; has to be in {0,1}
 **************************************************/
#if !defined(MLKEM_USE_NATIVE_VERIFY)
void cmov(uint8_t *r, const uint8_t *x, size_t len, uint8_t b)
__contract__(
  requires(memory_no_alias(r, len))
  requires(memory_no_alias(x, len))
  requires(b == 0 || b == 1)
  assigns(memory_slice(r, len))
);
#else  /* MLKEM_USE_NATIVE_VERIFY */
static inline void cmov(uint8_t *r, const uint8_t *x, size_t len, uint8_t b)
{
  cmov_native(r, x, len, b);
}
#endif /* MLKEM_USE_NATIVE_VERIFY */

#define cmov_int16 MLKEM_NAMESPACE(cmov_int16)
/*************************************************
 * Name:        cmov_int16
 *
 * Description: Copy input v to *r if b is 1, don't modify *r if b is 0.
 *              Requires b to be in {0,1};
 *              Runs in constant time.
 *
 * Arguments:   int16_t *r:       pointer to output int16_t
 *              int16_t v:        input int16_t. Must not be NULL
 *              uint16_t b:       Condition bit; has to be in {0,1}
 **************************************************/
#if !defined(MLKEM_USE_NATIVE_VERIFY)
void cmov_int16(int16_t *r, const int16_t v, const uint16_t b)
__contract__(
  requires(b == 0 || b == 1)
  requires(memory_no_alias(r, sizeof(int16_t)))
  assigns(memory_slice(r, sizeof(int16_t)))
  ensures(*r == (b ? v : old(*r)))
);
#else  /* MLKEM_USE_NATIVE_VERIFY */
static inline void cmov_int16(int16_t *r, const int16_t v, const uint16_t b)
{
  cmov_int16_native(r, v, b);
}
#endif /* MLKEM_USE_NATIVE_VERIFY */

#endif
