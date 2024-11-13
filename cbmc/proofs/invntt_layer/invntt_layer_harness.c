// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file invntt_layer_harness.c
 * @brief Implements the proof harness for invntt_layer function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <stdint.h>
void invntt_layer(int16_t *p, int len, int layer);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  int16_t *a;
  int len, layer;
  invntt_layer(a, len, layer);
}
