/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef REDUCE_H
#define REDUCE_H

#include <stdint.h>
#include "cbmc.h"
#include "debug/debug.h"
#include "params.h"

#define MONT -1044                 /* 2^16 mod q */
#define HALF_Q ((MLKEM_Q + 1) / 2) /* 1665 */

#define montgomery_reduce MLKEM_NAMESPACE(montgomery_reduce)
/*************************************************
 * Name:        montgomery_reduce
 *
 * Description: Montgomery reduction
 *
 * Arguments:   - int32_t a: input integer to be reduced
 *                  Must be smaller than 2 * 2^12 * 2^15 in absolute value.
 *
 * Returns:     integer congruent to a * R^-1 modulo q,
 *              smaller than 2 * q in absolute value.
 **************************************************/
int16_t montgomery_reduce(int32_t a)
__contract__(
  requires(a > -(2 * 4096 * 32768))
  requires(a <  (2 * 4096 * 32768))
  ensures(return_value > -2 * MLKEM_Q && return_value < 2 * MLKEM_Q)
);

#define barrett_reduce MLKEM_NAMESPACE(barrett_reduce)
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
__contract__(
  ensures(return_value > -HALF_Q && return_value < HALF_Q)
);

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
__contract__(
  requires(b > -HALF_Q)
  requires(b < HALF_Q)
  ensures(return_value > -MLKEM_Q && return_value < MLKEM_Q)
);


#endif
