/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "debug.h"

#if defined(MLKEM_DEBUG)

static char debug_buf[256];

void mlkem_debug_assert(const char *file, int line, const char *description,
                        const int val)
{
  if (val == 0)
  {
    snprintf(debug_buf, sizeof(debug_buf), "Assertion failed: %s (value %d)",
             description, val);
    mlkem_debug_print_error(file, line, debug_buf);
    exit(1);
  }
}
void mlkem_debug_check_bounds(const char *file, int line,
                              const char *description, const int16_t *ptr,
                              unsigned len, int lower_bound_exclusive,
                              int upper_bound_exclusive)
{
  int err = 0;
  unsigned i;
  for (i = 0; i < len; i++)
  {
    int16_t val = ptr[i];
    if (!(val > lower_bound_exclusive && val < upper_bound_exclusive))
    {
      snprintf(debug_buf, sizeof(debug_buf),
               "%s, index %u, value %d out of bounds (%d,%d)", description, i,
               (int)val, lower_bound_exclusive, upper_bound_exclusive);
      mlkem_debug_print_error(file, line, debug_buf);
      err = 1;
    }
  }

  if (err == 1)
    exit(1);
}

void mlkem_debug_print_error(const char *file, int line, const char *msg)
{
  fprintf(stderr, "[ERROR:%s:%04d] %s\n", file, line, msg);
  fflush(stderr);
}

#else /* MLKEM_DEBUG */

int empty_cu_debug;

#endif /* MLKEM_DEBUG */
