// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include <stdint.h>
#include "polyvec.h"

void unpack_sk(polyvec *sk,
               const uint8_t packedsk[MLKEM_INDCPA_SECRETKEYBYTES]);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  polyvec *sk;
  uint8_t *packedsk;

  unpack_sk(sk, packedsk);
}
