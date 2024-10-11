// SPDX-License-Identifier: Apache-2.0
#include "reduce.h"
#include <stdint.h>
#include "params.h"

/*************************************************
 * Name:        montgomery_reduce
 *
 * Description: Montgomery reduction; given a 32-bit integer a, computes
 *              16-bit integer congruent to a * R^-1 mod q, where R=2^16
 *
 * Arguments:   - int32_t a: input integer to be reduced
 *
 * Returns:     integer congruent to a * R^-1 modulo q
 *
 *              Bounds: For any C such that |a| < q * C, the return value
 *              has absolute value < q (C/2^16 + 1/2).
 *
 *              Notable special cases:
 *              - The Montgomery multiplication of a value of absolute value
 *                < q * C with a signed-canonical value ( < q/2 ) has
 *                absolute value q * (0.0254 * C + 1/2).
 *              - The Montgomery multiplication of a value of absolute value
 *                < q * C with a value t of |t| < q has absolute value
 *                < q * (0.0508 * C + 1/2).
 *              - The Montgomery multiplication of a value of absolute value
 *                < C with a value of abs < q has absolute value
 *                < q (C/2^16 + 1/2).
 **************************************************/
int16_t montgomery_reduce(int32_t a) {
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

  uint16_t u;
  int16_t t;
  // Compute a*q^{-1} mod 2^16 in unsigned representatives
  u = (uint16_t)a * QINV;
  // Lift to signed canonical representative mod 2^16.
  // PORTABILITY: This relies on uint16_t -> int16_t
  // being implemented as the inverse of int16_t -> uint16_t,
  // which is not mandated by the standard.
  t = (int16_t)u;
  // By construction, the LHS is divisible by 2^16
  t = (a - (int32_t)t * KYBER_Q) >> 16;
  return t;
}

/*************************************************
 * Name:        barrett_reduce
 *
 * Description: Barrett reduction; given a 16-bit integer a, computes
 *              centered representative congruent to a mod q in
 *{-(q-1)/2,...,(q-1)/2}
 *
 * Arguments:   - int16_t a: input integer to be reduced
 *
 * Returns:     integer in {-(q-1)/2,...,(q-1)/2} congruent to a modulo q.
 **************************************************/
int16_t barrett_reduce(int16_t a) {
  int16_t t;
  const int16_t v = ((1 << 26) + KYBER_Q / 2) / KYBER_Q;

  t = ((int32_t)v * a + (1 << 25)) >> 26;
  t *= KYBER_Q;
  return a - t;
}
