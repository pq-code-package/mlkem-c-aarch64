// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file polyvec_frombytes_harness.c
 * @brief Implements the proof harness for polyvec_frombytes function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <polyvec.h>

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  polyvec *a;
  uint8_t *r;
  polyvec_frombytes(a, r);
}
