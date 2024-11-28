// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file gen_matrix_harness.c
 * @brief Implements the proof harness for gen_matrix function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <stdint.h>
#include "indcpa.h"

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
  polyvec *a;
  uint8_t *seed;
  int transposed;
  gen_matrix(a, seed, transposed);
}
