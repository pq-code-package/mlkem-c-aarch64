// SPDX-License-Identifier: Apache-2.0
#ifndef REDUCE_H
#define REDUCE_H

#include <stdint.h>
#include "cbmc.h"
#include "debug/debug.h"
#include "params.h"

#define MONT -1044                  // 2^16 mod q
#define HALF_Q ((MLKEM_Q + 1) / 2)  // 1665

/*************************************************
 * Name:        montgomery_reduce
 *
 * Description: Montgomery reduction
 *
 * Arguments:   - int32_t a: input integer to be reduced
 *                  Must be smaller than 2 * q * 2^15 in absolute value.
 *
 * Returns:     integer congruent to a * R^-1 modulo q,
 *              smaller than 3/2 q in absolute value.
 **************************************************/
#define montgomery_reduce MLKEM_NAMESPACE(montgomery_reduce)
int16_t montgomery_reduce(int32_t a)
    // clang-format off
REQUIRES(a > -(2 * MLKEM_Q * 32768))
REQUIRES(a <  (2 * MLKEM_Q * 32768))
ENSURES(RETURN_VALUE > -(3 * HALF_Q) && RETURN_VALUE < (3 * HALF_Q));
// clang-format on

#define barrett_reduce MLKEM_NAMESPACE(barrett_reduce)
int16_t barrett_reduce(int16_t a)
    // clang-format off
ENSURES(RETURN_VALUE > -HALF_Q && RETURN_VALUE < HALF_Q);
// clang-format on

/*************************************************
 * Name:        fqmul
 *
 * Description: Montgomery multiplication modulo q=3329
 *
 * Arguments:   - int16_t a: first factor
 *                  Can be any int16_t.
 *              - int16_t b: second factor.
 *                  Must be signed canonical (abs value <(q+1)/2)
 *
 * Returns 16-bit integer congruent to a*b*R^{-1} mod q, and
 * smaller than q in absolute value.
 *
 **************************************************/
#define fqmul MLKEM_NAMESPACE(fqmul)
int16_t fqmul(int16_t a, int16_t b)
    // clang-format off
REQUIRES(b > -HALF_Q)
REQUIRES(b < HALF_Q)
ENSURES(RETURN_VALUE > -MLKEM_Q && RETURN_VALUE < MLKEM_Q);
// clang-format on


#endif
