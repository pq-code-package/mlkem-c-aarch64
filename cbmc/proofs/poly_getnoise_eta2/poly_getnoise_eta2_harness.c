// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file poly_getnoise_eta2_harness.c
 * @brief Implements the proof harness for poly_getnoise_eta2 function.
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
  uint8_t *seed;
  poly *r;
  uint8_t nonce;

  poly_getnoise_eta2(r, seed, nonce);
}
