// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#ifndef VERIFY_AARCH64_H
#define VERIFY_AARCH64_H

#include <stddef.h>
#include <stdint.h>

static inline int verify_native(const uint8_t *a, const uint8_t *b,
                                const size_t len)
{
  // TODO: replace this with inline asm
  uint8_t r = 0;
  uint64_t u;

  // Switch to a _signed_ ilen value, so that our loop counter
  // can also be signed, and thus (i - 1) in the loop invariant
  // can yield -1 as required.
  const int ilen = (int)len;

  for (int i = 0; i < ilen; i++)
  {
    r |= a[i] ^ b[i];
  }

  u = (-(uint64_t)r) >> 63;
  return (int)u;
}

static inline void cmov_native(uint8_t *r, const uint8_t *x, size_t len,
                               uint8_t b)
{
  // TODO: replace this with inline asm
  size_t i;

  b = (-b) & 0xFF;
  for (i = 0; i < len; i++)
  {
    r[i] ^= b & (r[i] ^ x[i]);
  }
}

static inline void cmov_int16_native(int16_t *r, const int16_t v,
                                     const uint16_t b)
{
  // TODO: replace this with inline asm
  // b == 0 => mask = 0x0000
  // b == 1 => mask = 0xFFFF
  const uint16_t mask = -b;

  // mask == 0x0000 => *r == (*r ^ 0x0000) == *r
  // mask == 0xFFFF => *r == (*r ^ (*r ^ v)) == (*r ^ *r) ^ v == 0 ^ v == v
  *r ^= mask & ((*r) ^ v);
}

#endif /* VERIFY_AARCH64_H */
