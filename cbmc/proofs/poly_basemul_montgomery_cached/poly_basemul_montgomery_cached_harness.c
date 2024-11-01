// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file poly_basemul_montgomery_cached_harness.c
 * @brief Implements the proof harness for basemul_cached function.
 */
#include "poly.h"

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
  poly r, a, b;
  poly_mulcache b_cached;

  poly_basemul_montgomery_cached(&r, &a, &b, &b_cached);
}
