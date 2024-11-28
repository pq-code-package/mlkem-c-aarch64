// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file indcpa_dec_harness.c
 * @brief Implements the proof harness for indcpa_dec function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <indcpa.h>
#include <poly.h>

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
  uint8_t *m, *c, *sk;
  indcpa_dec(m, c, sk);
}
