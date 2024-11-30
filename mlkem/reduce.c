// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#include "reduce.h"
#include <stdint.h>
#include "params.h"

// QINV == -3327 converted to uint16_t == -3327 + 65536 == 62209
static const uint32_t QINV = 62209;  // q^-1 mod 2^16

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
static inline int16_t cast_uint16_to_int16(uint16_t x)
{
  // PORTABILITY: This relies on uint16_t -> int16_t
  // being implemented as the inverse of int16_t -> uint16_t,
  // which is implementation-defined (C99 6.3.1.3 (3))
  //
  // CBMC (correctly) fails to prove this conversion is OK,
  // so we have to suppress that check here
  return (int16_t)x;
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

int16_t montgomery_reduce(int32_t a)
{
  SCALAR_BOUND(a, 2 * MLKEM_Q * 32768, "montgomery_reduce input");

  // Bounds on paper
  //
  // - Case |a| < q * C, for some C
  //
  // |t| <= |a|/2^16 + |t|*q/2^16
  //      < q * C / 2^16 + q/2
  //      = q (C/2^16 + 1/2)
  //
  // - Case |a| < (q/2) * C * q, for some C
  //
  // Replace C -> C * q in the above and estimate
  // q / 2^17 < 0.0254.

  //  Compute a*q^{-1} mod 2^16 in unsigned representatives
  const uint16_t a_reduced = a & UINT16_MAX;
  const uint16_t a_inverted = (a_reduced * QINV) & UINT16_MAX;

  // Lift to signed canonical representative mod 2^16.
  const int16_t t = cast_uint16_to_int16(a_inverted);

  int32_t r = a - ((int32_t)t * MLKEM_Q);

  // PORTABILITY: Right-shift on a signed integer is, strictly-speaking,
  // implementation-defined for negative left argument. Here,
  // we assume it's sign-preserving "arithmetic" shift right. (C99 6.5.7 (5))
  r = r >> 16;

  SCALAR_BOUND(r, (3 * (MLKEM_Q + 1)) / 2, "montgomery_reduce output");
  return r;
}

int16_t fqmul(int16_t a, int16_t b, uint16_t b_twisted)
{
  SCALAR_BOUND(b, HALF_Q, "fqmul input");

  const int16_t low = cast_uint16_to_int16(a * b_twisted);

  int16_t r = ((int32_t)a * b) >> 16;
  int16_t t = ((int32_t)low * MLKEM_Q) >> 16;
  r -= t;

  SCALAR_BOUND(r, MLKEM_Q, "fqmul output");
  return r;
}

// To divide by MLKEM_Q using Barrett multiplication, the "magic number"
// multiplier is round_to_nearest(2**26/MLKEM_Q)
#define BPOWER 26
static const int32_t barrett_multiplier =
    ((1 << BPOWER) + MLKEM_Q / 2) / MLKEM_Q;

/*************************************************
 * Name:        barrett_reduce
 *
 * Description: Barrett reduction; given a 16-bit integer a, computes
 *              centered representative congruent to a mod q in
 *              {-(q-1)/2,...,(q-1)/2}
 *
 * Arguments:   - int16_t a: input integer to be reduced
 *
 * Returns:     integer in {-(q-1)/2,...,(q-1)/2} congruent to a modulo q.
 **************************************************/
int16_t barrett_reduce(int16_t a)
{
  // Compute round_to_nearest(a/MLKEM_Q) using the multiplier
  // above and shift by BPOWER places.
  //
  // PORTABILITY: Right-shift on a signed integer is, strictly-speaking,
  // implementation-defined for negative left argument. Here,
  // we assume it's sign-preserving "arithmetic" shift right. (C99 6.5.7 (5))
  const int32_t t = (barrett_multiplier * a + (1 << (BPOWER - 1))) >> BPOWER;

  // t is in -10 .. +10, so we need 32-bit math to
  // evaluate t * MLKEM_Q and the subsequent subtraction
  return (int16_t)(a - t * MLKEM_Q);
}
