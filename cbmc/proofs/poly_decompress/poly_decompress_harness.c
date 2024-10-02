// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file poly_decompress_harness.c
 * @brief Implements the proof harness for poly_decompress function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include "poly.h"

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  poly r;
  uint8_t a[KYBER_POLYCOMPRESSEDBYTES];

  poly_decompress(&r, a);
}
