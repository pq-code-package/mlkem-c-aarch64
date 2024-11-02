// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file poly_getnoise_eta1_4x_harness.c
 * @brief Implements the proof harness for poly_getnoise_eta1_4x function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <poly.h>

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  uint8_t seed[MLKEM_SYMBYTES];
  poly r0, r1, r2, r3;
  uint8_t nonce0, nonce1, nonce2, nonce3;

  poly_getnoise_eta1_4x(&r0, &r1, &r2, &r3, seed, nonce0, nonce1, nonce2,
                        nonce3);
}
