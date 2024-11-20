// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file poly_compress_dv_harness.c
 * @brief Implements the proof harness for poly_compress_dv function.
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
  poly *r;
  uint8_t *a;

  poly_compress_dv(a, r);
}
