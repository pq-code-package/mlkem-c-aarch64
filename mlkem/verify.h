// SPDX-License-Identifier: Apache-2.0
#ifndef VERIFY_H
#define VERIFY_H

#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include "cbmc.h"
#include "params.h"

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
int verify(const uint8_t *a, const uint8_t *b,
           const size_t len)  // clang-format off
REQUIRES(IS_FRESH(a, len))
REQUIRES(IS_FRESH(b, len))
REQUIRES(len <= INT_MAX)
ENSURES(RETURN_VALUE == (1 - FORALL(int, i, 0, ((int)len - 1), (a[i] == b[i]))));
// clang-format on

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
void cmov(uint8_t *r, const uint8_t *x, size_t len,
          uint8_t b)  // clang-format on
    REQUIRES(IS_FRESH(r, len)) REQUIRES(IS_FRESH(x, len))
        REQUIRES(b == 0 || b == 1) ASSIGNS(OBJECT_UPTO(r, len));
// clang-format off

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

void cmov_int16(int16_t *r, const int16_t v,
                const uint16_t b)  // clang-format off
REQUIRES(b == 0 || b == 1)
REQUIRES(IS_FRESH(r, sizeof(int16_t)))
ASSIGNS(OBJECT_UPTO(r, sizeof(int16_t)))
ENSURES(*r == (b ? v : OLD(*r)));
// clang-format on

#endif
