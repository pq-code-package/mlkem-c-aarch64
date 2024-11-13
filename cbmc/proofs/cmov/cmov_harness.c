// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file cmov_harness.c
 * @brief Implements the proof harness for cmov function.
 */
#include "verify.h"

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
  uint8_t *x, *y;
  size_t len;
  uint8_t b;
  cmov(x, y, len, b);
}
