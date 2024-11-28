// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file ntt_butterfly_block_harness.c
 * @brief Implements the proof harness for ntt_butterfly_block function.
 */
#include <stdint.h>
void ntt_butterfly_block(int16_t *r, int16_t root, int start, int len,
                         int bound);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
  int16_t *r, root;
  int start, stride, bound;
  ntt_butterfly_block(r, root, start, stride, bound);
}
