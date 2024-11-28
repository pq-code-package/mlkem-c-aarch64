// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file gen_matrix_entry_x4_harness.c
 * @brief Implements the proof harness for gen_matrix_entry_x4 function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <stdint.h>
#include "poly.h"

// declare here since it's static in non-CBMC builds
void gen_matrix_entry_x4(poly vec[4], uint8_t *seed[4]);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
  poly out[4];
  uint8_t *seed[4];
  gen_matrix_entry_x4(out, seed);
}
