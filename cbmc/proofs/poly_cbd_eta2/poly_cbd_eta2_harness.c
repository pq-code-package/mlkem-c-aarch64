// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file poly_cbd_eta2_harness.c
 * @brief Implements the proof harness for poly_cbd_eta2 function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <cbd.h>

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  uint8_t buf[MLKEM_ETA2 * MLKEM_N / 4];
  poly a;

  poly_cbd_eta2(&a, buf);
}
