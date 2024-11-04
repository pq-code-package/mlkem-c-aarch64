// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file rej_uniform_harness.c
 * @brief Implements the proof harness for rej_uniform function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include "cbmc.h"
#include "rej_uniform.h"

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  unsigned int outlen, inlen;
  int16_t *r;
  uint8_t *buf;

  rej_uniform(r, outlen, buf, inlen);
}
