// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */


/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <stdint.h>
#include "symmetric.h"

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
  uint8_t *out;
  size_t outlen;
  uint8_t *key;
  uint8_t nonce;
  mlkem_shake256_prf(out, outlen, key, nonce);
}
