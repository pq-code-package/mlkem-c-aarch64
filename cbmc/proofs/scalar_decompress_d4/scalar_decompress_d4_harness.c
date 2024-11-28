// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file scalar_decompress_d4_harness.c
 * @brief Implements the proof harness for scalar_decompress_d4 function.
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
void harness(void)
{
  uint32_t u;
  uint16_t d;
  d = scalar_decompress_d4(u);
}
