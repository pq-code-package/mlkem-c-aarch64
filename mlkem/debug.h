#ifndef DEBUG_H
#define DEBUG_H

#if defined(MLKEM_DEBUG)
#include <stdlib.h>
#include <stdio.h>

void mlkem_debug_check_bounds(const char *file, int line,
                              const char *description,
                              const int16_t *ptr, unsigned len,
                              int16_t lower_bound_inclusive,
                              int16_t upper_bound_inclusive);

void mlkem_debug_print_error(const char *file, int line, const char *msg);

#define MLKEM_DEBUG_ASSERT_COND(cond, msg)             \
    do { if((cond)) { MLKEM_FAIL((msg)); } } while(0)

#define MLKEM_DEBUG_ASSERT_BOUND(ptr,len,lower_inclusive,upper_inclusive,msg) \
    do {                                                                      \
        mlkem_debug_check_bounds(__FILE__,__LINE__,(msg),(int16_t*)(ptr),(len), \
                                 (lower_inclusive),(upper_inclusive));        \
    } while(0)

#else  /* MLKEM_DEBUG */

#define MLKEM_DEBUG_ASSERT_COND(cond) do {} while(0)
#define MLKEM_DEBUG_ASSERT_BOUND(ptr,len,lower_inclusive,upper_inclusive) do {} while(0)

#endif /* MLKEM_DEBUG */

#endif /* DEBUG_H */
