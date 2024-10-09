// SPDX-License-Identifier: Apache-2.0
#ifndef MLKEM_DEBUG_H
#define MLKEM_DEBUG_H

#if defined(MLKEM_DEBUG)
#include <stdio.h>
#include <stdlib.h>

void mlkem_debug_check_bounds(const char *file, int line,
                              const char *description, const int16_t *ptr,
                              unsigned len, int16_t lower_bound_inclusive,
                              int16_t upper_bound_inclusive);

void mlkem_debug_print_error(const char *file, int line, const char *msg);

#define BOUND(ptr, len, abs_bound, msg)                                   \
  do {                                                                    \
    mlkem_debug_check_bounds(__FILE__, __LINE__, (msg), (int16_t *)(ptr), \
                             (len), -((abs_bound)-1), ((abs_bound)-1));   \
  } while (0)

#define POLY_BOUND_MSG(ptr, abs_bound, msg) \
  BOUND((ptr)->coeffs, (KYBER_N), (abs_bound), msg)

#define POLY_BOUND(ptr, abs_bound) \
  POLY_BOUND_MSG((ptr), (abs_bound), "poly bound for " #ptr)

#define POLYVEC_BOUND(ptr, abs_bound)                                    \
  do {                                                                   \
    for (unsigned _debug_polyvec_bound_idx = 0;                          \
         _debug_polyvec_bound_idx < KYBER_K; _debug_polyvec_bound_idx++) \
      POLY_BOUND_MSG(&(ptr)->vec[_debug_polyvec_bound_idx], (abs_bound), \
                     "polyvec bound for " #ptr ".vec[i]");               \
  } while (0)

// Following AWS-LC to define a C99-compliant static assert
#define MLKEM_CONCAT(left, right) left##right
#define MLKEM_STATIC_ASSERT_DEFINE(cond, msg)                            \
  typedef struct {                                                       \
    unsigned int MLKEM_CONCAT(static_assertion_, msg) : (cond) ? 1 : -1; \
  } MLKEM_CONCAT(static_assertion_, msg) __attribute__((unused));

#define MLKEM_STATIC_ASSERT_ADD_LINE0(cond, suffix) \
  MLKEM_STATIC_ASSERT_DEFINE(cond, MLKEM_CONCAT(at_line_, suffix))
#define MLKEM_STATIC_ASSERT_ADD_LINE1(cond, line, suffix) \
  MLKEM_STATIC_ASSERT_ADD_LINE0(cond, MLKEM_CONCAT(line, suffix))
#define MLKEM_STATIC_ASSERT_ADD_LINE2(cond, suffix) \
  MLKEM_STATIC_ASSERT_ADD_LINE1(cond, __LINE__, suffix)
#define MLKEM_STATIC_ASSERT_ADD_ERROR(cond, suffix) \
  MLKEM_STATIC_ASSERT_ADD_LINE2(cond, MLKEM_CONCAT(_error_is_, suffix))
#define STATIC_ASSERT(cond, error) MLKEM_STATIC_ASSERT_ADD_ERROR(cond, error)

#else /* MLKEM_DEBUG */

#define BOUND(...) \
  do {             \
  } while (0)
#define POLY_BOUND(...) \
  do {                  \
  } while (0)
#define POLYVEC_BOUND(...) \
  do {                     \
  } while (0)
#define POLY_BOUND_MSG(...) \
  do {                      \
  } while (0)
#define STATIC_ASSERT(...)

#endif /* MLKEM_DEBUG */

#endif /* MLKEM_DEBUG_H */
