// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file verify_harness.c
 * @brief Implements the proof harness for verify function.
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
  uint8_t *a;
  uint8_t *b;
  size_t len;
  int r;
  r = verify(a, b, len);
}
