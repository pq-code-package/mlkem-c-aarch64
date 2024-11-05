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
 *              - unsigned int len:    requested number of 16-bit integers
 *                                     (uniform mod q).
 *              - const uint8_t *buf:  pointer to input buffer
 *                                     (assumed to be uniform random bytes)
 *              - unsigned int buflen: length of input buffer in bytes
 *                                     Must be a multiple of 3.
 *                                     Must be <= 4096.
 *
 * Note: Strictly speaking, only a few values of buflen near UINT_MAX need
 * excluding. The limit of 4096 is somewhat arbitary but sufficient for all
 * uses of this function.
 *
 * Returns the number of sampled 16-bit integers, at most len.
 * If it is strictly less than len, all of the input buffers is
 * guaranteed to have been consumed. If it is equal to len, no
 * information is provided on how many bytes of the input buffer
 * have been consumed.
 **************************************************/
unsigned int rej_uniform(int16_t *r, unsigned int len, const uint8_t *buf,
                         unsigned int buflen)  // clang-format off
REQUIRES(buflen <= 4096 && buflen % 3 == 0)
REQUIRES(IS_FRESH(r, sizeof(int16_t) * len))
REQUIRES(IS_FRESH(buf, buflen))
ASSIGNS(OBJECT_UPTO(r, len * sizeof(int16_t)))
ENSURES(RETURN_VALUE <= len &&
        (RETURN_VALUE > 0 ==> ARRAY_IN_BOUNDS(int, k, 0, RETURN_VALUE - 1, r, 0, (MLKEM_Q - 1))));
// clang-format on
#endif
