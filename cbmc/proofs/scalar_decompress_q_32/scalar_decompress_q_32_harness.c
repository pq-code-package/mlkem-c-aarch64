// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file scalar_decompress_q_32_harness.c
 * @brief Implements the proof harness for scalar_decompress_q_32 function.
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
    // Check that decompression followed by compression is the identity
    uint32_t c0, c1, d;

    d = scalar_decompress_q_32(c0);
    c1 = scalar_compress_q_32(d);
    __CPROVER_assert(c0 == c1, "scalar_compress_q_32 o scalar_decompress_q_32 != id");
}
