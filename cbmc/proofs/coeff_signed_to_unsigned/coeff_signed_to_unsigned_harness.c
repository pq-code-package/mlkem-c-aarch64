// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file coeff_signed_to_unsigned.c
 * @brief Implements the proof harness for coeff_signed_to_unsigned function.
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
    int16_t u;

    /* Contracts for this function are in poly.h */
    uint16_t d = coeff_signed_to_unsigned(u);
}
