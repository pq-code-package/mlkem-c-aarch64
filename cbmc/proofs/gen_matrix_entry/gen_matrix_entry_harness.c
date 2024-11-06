// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file rej_uniform_harness.c
 * @brief Implements the proof harness for rej_uniform function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <stdint.h>
#include "poly.h"

// declare here since it's static in non-CBMC builds
void gen_matrix_entry(poly *entry, uint8_t seed[MLKEM_SYMBYTES + 16]);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  poly *out;
  uint8_t *seed;
  gen_matrix_entry(out, seed);
}
