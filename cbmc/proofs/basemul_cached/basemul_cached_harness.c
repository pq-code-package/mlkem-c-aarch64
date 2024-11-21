// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file basemul_cached_harness.c
 * @brief Implements the proof harness for basemul_cached function.
 */
#include "ntt.h"
#include "reduce.h"

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  int16_t *a, *b, *r, b_cached;

  basemul_cached(r, a, b, b_cached);
}
