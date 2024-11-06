// SPDX-License-Identifier: Apache-2.0
#ifndef REJ_UNIFORM_H
#define REJ_UNIFORM_H

#include <stdint.h>
#include <stdlib.h>
#include "cbmc.h"
#include "params.h"

#define rej_uniform MLKEM_NAMESPACE(rej_uniform)
/*************************************************
 * Name:        rej_uniform
 *
 * Description: Run rejection sampling on uniform random bytes to generate
 *              uniform random integers mod q
 *
 * Arguments:   - int16_t *r:          pointer to output buffer
 *              - unsigned int target: requested number of 16-bit integers
 *                                     (uniform mod q).
 *                                     Must be <= 4096.
 *              - unsigned int offset: number of 16-bit integers that have
 *                                     already been sampled.
 *                                     Must be <= target.
 *              - const uint8_t *buf:  pointer to input buffer
 *                                     (assumed to be uniform random bytes)
 *              - unsigned int buflen: length of input buffer in bytes
 *                                     Must be <= 4096.
 *                                     Must be a multiple of 3.
 *
 * Note: Strictly speaking, only a few values of buflen near UINT_MAX need
 * excluding. The limit of 4096 is somewhat arbitary but sufficient for all
 * uses of this function. Similarly, the actual limit for target is UINT_MAX/2.
 *
 * Returns the new offset of sampled 16-bit integers, at most target,
 * and at least the initial offset.
 * If the new offset is strictly less than len, all of the input buffers
 * is guaranteed to have been consumed. If it is equal to len, no information
 * is provided on how many bytes of the input buffer have been consumed.
 **************************************************/

// REF-CHANGE: The signature differs from the Kyber reference implementation
// in that it adds the offset and always expects the base of the target
// buffer. This avoids shifting the buffer base in the caller, which appears
// tricky to reason about.
unsigned int rej_uniform(int16_t *r, unsigned int target, unsigned int offset,
                         const uint8_t *buf,
                         unsigned int buflen)  // clang-format off
REQUIRES(offset <= target && target <= 4096 && buflen <= 4096 && buflen % 3 == 0)
REQUIRES(IS_FRESH(r, sizeof(int16_t) * target))
REQUIRES(IS_FRESH(buf, buflen))
REQUIRES(offset > 0 ==> ARRAY_IN_BOUNDS(int, k, 0, offset - 1, r, 0, (MLKEM_Q - 1)))
ASSIGNS(OBJECT_UPTO(r, sizeof(int16_t) * target))
ENSURES(offset <= RETURN_VALUE && RETURN_VALUE <= target)
ENSURES(RETURN_VALUE > 0 ==> ARRAY_IN_BOUNDS(int, k, 0, RETURN_VALUE - 1, r, 0, (MLKEM_Q - 1)));
// clang-format on
#endif
