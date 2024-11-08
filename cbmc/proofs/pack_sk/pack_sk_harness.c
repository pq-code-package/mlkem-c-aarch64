// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include <stdint.h>
#include "polyvec.h"

void pack_sk(uint8_t r[MLKEM_INDCPA_SECRETKEYBYTES], polyvec *sk);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  polyvec *sk;
  uint8_t *r;

  pack_sk(r, sk);
}
