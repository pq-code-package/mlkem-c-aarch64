// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file poly_mulcache_compute_harness.c
 * @brief Implements the proof harness for poly_mulcache_compute function.
 */
#include "ntt.h"
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
  poly_mulcache *x;
  poly *a;

  poly_mulcache_compute(x, a);
}
