// SPDX-License-Identifier: Apache-2.0
#ifndef VERIFY_H
#define VERIFY_H

#include <stddef.h>
#include <stdint.h>
#include "cbmc.h"
#include "params.h"

#define verify MLKEM_NAMESPACE(verify)
int verify(const uint8_t *a, const uint8_t *b, size_t len);

#define cmov MLKEM_NAMESPACE(cmov)
void cmov(uint8_t *r, const uint8_t *x, size_t len, uint8_t b);

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
void cmov_int16(int16_t *r, const int16_t v, const uint16_t b)
    // clang-format off
REQUIRES(b == 0 || b == 1)
REQUIRES(IS_FRESH(r, sizeof(int16_t)))
ASSIGNS(OBJECT_WHOLE(r))
ENSURES(*r == (b ? v : OLD(*r)));
// clang-format on
#endif
