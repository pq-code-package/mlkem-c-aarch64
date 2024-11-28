// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file poly_decompress_dv_harness.c
 * @brief Implements the proof harness for poly_decompress_dv function.
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
void harness(void)
{
  poly *r;
  uint8_t *a;

  poly_decompress_dv(r, a);
}
