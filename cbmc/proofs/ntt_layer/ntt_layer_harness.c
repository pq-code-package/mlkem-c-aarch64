// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file poly_ntt_harness.c
 * @brief Implements the proof harness for poly_ntt function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include "poly.h"
void ntt_layer(int16_t *p, int len, int layer);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
  int16_t *a;
  int len, layer;
  ntt_layer(a, len, layer);
}
