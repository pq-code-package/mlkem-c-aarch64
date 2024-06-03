// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file scalar_compress_q_32_harness.c
 * @brief Implements the proof harness for scalar_compress_q_32 function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <poly.h>

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
    int32_t u;

    __CPROVER_assume(0 <= u && u < KYBER_Q);
    uint32_t d = scalar_compress_q_32(u);
    __CPROVER_assert(d < 32, "compression bound failed");
    __CPROVER_assert(d == (((uint32_t) u * 32 + KYBER_Q / 2) / KYBER_Q) % 32,
                     "compression expression failed");
}
