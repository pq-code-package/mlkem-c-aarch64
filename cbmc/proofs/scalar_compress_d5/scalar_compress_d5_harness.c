// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file scalar_compress_d5_harness.c
 * @brief Implements the proof harness for scalar_compress_d5 function.
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
  uint16_t u;

  /* Contracts for this function are in poly.h */
  uint32_t d = scalar_compress_d5(u);
}
