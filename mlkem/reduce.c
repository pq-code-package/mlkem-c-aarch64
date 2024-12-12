/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "reduce.h"
#include <stdint.h>
#include "params.h"

/* QINV == -3327 converted to uint16_t == -3327 + 65536 == 62209 */
static const uint32_t QINV = 62209; /* q^-1 mod 2^16 */

/*************************************************
 * Name:        cast_uint16_to_int16
 *
 * Description: Cast uint16 value to int16
 *
 * Returns:
 *   input x in     0 .. 32767: returns value unchanged
 *   input x in 32768 .. 65535: returns (x - 65536)
 **************************************************/
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "conversion"
#endif
static INLINE int16_t cast_uint16_to_int16(uint16_t x)
{
  /*
   * PORTABILITY: This relies on uint16_t -> int16_t
   * being implemented as the inverse of int16_t -> uint16_t,
   * which is implementation-defined (C99 6.3.1.3 (3))
   * CBMC (correctly) fails to prove this conversion is OK,
   * so we have to suppress that check here
   */
  return (int16_t)x;
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/*************************************************
 * Name:        montgomery_reduce_generic
 *
 * Description: Generic Montgomery reduction; given a 32-bit integer a, computes
 *              16-bit integer congruent to a * R^-1 mod q, where R=2^16
 *
 * Arguments:   - int32_t a: input integer to be reduced
 *
 * Returns:     integer congruent to a * R^-1 modulo q, with absolute value
 *                <= ceil(|a| / 2^16) + (MLKEM_Q + 1)/2
 *
 **************************************************/
ALWAYS_INLINE
static INLINE int16_t montgomery_reduce_generic(int32_t a)
{
  /*  Compute a*q^{-1} mod 2^16 in unsigned representatives */
  const uint16_t a_reduced = a & UINT16_MAX;
  const uint16_t a_inverted = (a_reduced * QINV) & UINT16_MAX;

  /* Lift to signed canonical representative mod 2^16. */
  const int16_t t = cast_uint16_to_int16(a_inverted);

  int32_t r = a - ((int32_t)t * MLKEM_Q);
  /* Bounds: |r| <= |a| + 2^15 * MLKEM_Q */

  /*
   * PORTABILITY: Right-shift on a signed integer is, strictly-speaking,
   * implementation-defined for negative left argument. Here,
   * we assume it's sign-preserving "arithmetic" shift right. (C99 6.5.7 (5))
   */
  r = r >> 16;
  /* Bounds: |r >> 16| <= ceil(|r| / 2^16)
   *                   <= ceil(|a| / 2^16 + MLKEM_Q / 2)
   *                   <= ceil(|a| / 2^16) + (MLKEM_Q + 1) / 2
   *
   * (Note that |a >> n| = ceil(|a| / 2^16) for negative a)
   */

  return (int16_t)r;
}

int16_t montgomery_reduce(int32_t a)
{
  int16_t res;
  SCALAR_BOUND(a, 2 * UINT12_MAX * 32768, "montgomery_reduce input");

  res = montgomery_reduce_generic(a);
  /* Bounds:
   * |res| <= ceil(|a| / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil(2 * UINT12_MAX * 32768 / 65536) + (MLKEM_Q + 1) / 2
   *       <= UINT12_MAX + (MLKEM_Q + 1) / 2
   *        < 2 * MLKEM_Q */

  SCALAR_BOUND(res, 2 * MLKEM_Q, "montgomery_reduce output");
  return res;
}

int16_t fqmul(int16_t a, int16_t b)
{
  int16_t res;
  SCALAR_BOUND(b, HALF_Q, "fqmul input");

  res = montgomery_reduce((int32_t)a * (int32_t)b);
  /* Bounds:
   * |res| <= ceil(|a| * |b| / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil(2^15 * ((MLKEM_Q - 1)/2) / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil((MLKEM_Q - 1) / 4) + (MLKEM_Q + 1) / 2
   *        < MLKEM_Q
   */

  SCALAR_BOUND(res, MLKEM_Q, "fqmul output");
  return res;
}

/*
 * To divide by MLKEM_Q using Barrett multiplication, the "magic number"
 * multiplier is round_to_nearest(2**26/MLKEM_Q)
 */
#define BPOWER 26
static const int32_t barrett_multiplier =
    ((1 << BPOWER) + MLKEM_Q / 2) / MLKEM_Q;

int16_t barrett_reduce(int16_t a)
{
  /*
   * Compute round_to_nearest(a/MLKEM_Q) using the multiplier
   * above and shift by BPOWER places.
   * PORTABILITY: Right-shift on a signed integer is, strictly-speaking,
   * implementation-defined for negative left argument. Here,
   * we assume it's sign-preserving "arithmetic" shift right. (C99 6.5.7 (5))
   */
  const int32_t t = (barrett_multiplier * a + (1 << (BPOWER - 1))) >> BPOWER;

  /*
   * t is in -10 .. +10, so we need 32-bit math to
   * evaluate t * MLKEM_Q and the subsequent subtraction
   */
  return (int16_t)(a - t * MLKEM_Q);
}
