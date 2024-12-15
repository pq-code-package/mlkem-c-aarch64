// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly.h>

void harness(void)
{
  uint8_t *seed;
  poly *r;
  uint8_t nonce;

  poly_getnoise_eta2(r, seed, nonce);
}
