// SPDX-License-Identifier: Apache-2.0
#ifndef REDUCE_H
#define REDUCE_H

#include <stdint.h>
#include "cbmc.h"
#include "params.h"

#define MONT -1044                  // 2^16 mod q
#define HALF_Q ((MLKEM_Q - 1) / 2)  // 1664

#define montgomery_reduce MLKEM_NAMESPACE(montgomery_reduce)
int16_t montgomery_reduce(int32_t a)
    // clang-format off
REQUIRES(a >= INT32_MIN + (32768 * MLKEM_Q))
REQUIRES(a <= INT32_MAX - (32768 * MLKEM_Q))
ENSURES(RETURN_VALUE >= INT16_MIN && RETURN_VALUE <= INT16_MAX);
// clang-format on

#define barrett_reduce MLKEM_NAMESPACE(barrett_reduce)
int16_t barrett_reduce(int16_t a)
    // clang-format off
ENSURES(RETURN_VALUE >= -HALF_Q && RETURN_VALUE <= HALF_Q);
// clang-format on

/*************************************************
 * Name:        fqmul
 *
 * Description: Multiplication followed by Montgomery reduction
 *
 * Arguments:   - int16_t a: first factor
 *              - int16_t b: second factor
 *
 * Returns 16-bit integer congruent to a*b*R^{-1} mod q
 *
 * If one input is < |q|/2 in absolute value (which is given
 * in the common case of multiplication with constants), the
 * return value is < |q| in absolute value.
 *
 **************************************************/
static inline int16_t fqmul(int16_t a, int16_t b) {
  return montgomery_reduce((int32_t)a * (int32_t)b);
}

#endif
