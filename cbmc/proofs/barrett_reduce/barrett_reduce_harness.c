// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file barrett_reduce_harness.c
 * @brief Implements the proof harness for barrett_reduce function.
 */
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
  int16_t a;
  int16_t r;

  r = barrett_reduce(a);
}
