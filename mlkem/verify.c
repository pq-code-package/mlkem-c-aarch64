// SPDX-License-Identifier: Apache-2.0
#include "verify.h"
#include <stddef.h>
#include <stdint.h>

int verify(const uint8_t *a, const uint8_t *b, size_t len) {
  size_t i;
  uint8_t r = 0;

  for (i = 0; i < len; i++)  // clang-format off
    ASSIGNS(i, r)
    INVARIANT(i <= len)
    // clang-format on
    {
      r |= a[i] ^ b[i];
    }

    // Our CBMC setup rejects the conversion of negative signed
    // numbers to unsigned numbers, even though it's fully defined
    // by the standard. Disable the check for this check which
    // requires signed-to-unsigned conversion.
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "conversion"
#endif
  int res = (((uint64_t)-r) >> 63);
#ifdef CBMC
#pragma CPROVER check pop
#endif
  ASSERT((r != 0) == (res == 1), "verify bitfiddling gone wrong");
  ASSERT((r == 0) == (res == 0), "verify bitfiddling gone wrong");
  return res;
}

void cmov(uint8_t *r, const uint8_t *x, size_t len, uint8_t b) {
  size_t i;

  b = (-b) & 0xFF;
  for (i = 0; i < len; i++)  // clang-format off
    ASSIGNS(i, OBJECT_UPTO(r, len))
    INVARIANT(i <= len)
    // clang-format on
    {
      r[i] ^= b & (r[i] ^ x[i]);
    }
}

/*************************************************
 * Note:
 *
 * Constant-time implementation. Relies on basic
 * properties of bitwise ^ or and &.
 **************************************************/
void cmov_int16(int16_t *r, const int16_t v, const uint16_t b) {
// CBMC issues false alarms here for the implicit conversions between
// uint16_t and int, so disable "conversion-check" here for now.
#pragma CPROVER check push
#pragma CPROVER check disable "conversion"

  // b == 0 => mask = 0x0000
  // b == 1 => mask = 0xFFFF
  const uint16_t mask = -b;

  // mask == 0x0000 => *r == (*r ^ 0x0000) == *r
  // mask == 0xFFFF => *r == (*r ^ (*r ^ v)) == (*r ^ *r) ^ v == 0 ^ v == v
  *r ^= mask & ((*r) ^ v);
#pragma CPROVER check pop
}
