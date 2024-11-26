// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#ifndef VERIFY_AARCH64_H
#define VERIFY_AARCH64_H

#include <stddef.h>
#include <stdint.h>

static inline int verify_native(const uint8_t *a, const uint8_t *b,
                                const size_t len)
{
  uint8_t r = 0;
  int res;

  for (size_t i = 0; i < len; i++)
  {
    r |= a[i] ^ b[i];
  }

  // Use inline assembly to evaluate b != 0 to avoid
  // the compiler messing with it and potentially realizing
  // that, functionally, the above loop can be aborted as
  // soon as r != 0.
  asm("cmp %w[r], #0; \n\t"
      "cset %w[res], ne"  // res = (b != 0)
      : [res] "=r"(res)
      : [r] "r"(r)
      : "cc" /* the flag register is clobbered */);
  return res;
}

static inline uint8_t csel_uint8(uint8_t a, uint8_t b, const uint8_t cond)
{
  // Writing `cond ? a : b` in assembly to prevent
  // the compiler generating a branch.
  //
  // Using inline assembly to avoid function call overheads
  // and give the compiler more flexibility in scheduling.
  uint8_t res;
  asm("cmp %w[cond], #0; \n\t"
      "csel %w[res], %w[a], %w[b], ne"  // res = (cond != 0) ? a : b
      : [res] "=r"(res)
      : [a] "r"(a), [b] "r"(b), [cond] "r"(cond)
      : "cc" /* the flag register is clobbered */);
  return res;
}

static inline void cmov_native(uint8_t *r, const uint8_t *x, size_t len,
                               uint8_t b)
{
  size_t i;
  for (i = 0; i < len; i++)
  {
    r[i] = csel_uint8(x[i], r[i], b);
  }
}

static inline int16_t csel_int16(int16_t a, int16_t b, const uint16_t cond)
{
  // Writing `cond ? a : b` in assembly to prevent
  // the compiler generating a branch.
  //
  // Using inline assembly to avoid function call overheads
  // and give the compiler more flexibility in scheduling.
  int16_t res;
  asm("cmp %w[cond], #0; \n\t"
      "csel %w[res], %w[a], %w[b], ne"  // res = (cond != 0) ? a : b
      : [res] "=r"(res)
      : [a] "r"(a), [b] "r"(b), [cond] "r"(cond)
      : "cc" /* the flag register is clobbered */);
  return res;
}

static inline void cmov_int16_native(int16_t *r, const int16_t v,
                                     const uint16_t b)
{
  *r = csel_int16(v, *r, b);
}

#endif /* VERIFY_AARCH64_H */
