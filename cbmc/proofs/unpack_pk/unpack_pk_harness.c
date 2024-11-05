// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include <stdint.h>
#include "polyvec.h"

void unpack_pk(polyvec *pk, uint8_t seed[MLKEM_SYMBYTES],
               const uint8_t packedpk[MLKEM_INDCPA_PUBLICKEYBYTES]);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  polyvec *pk;
  uint8_t *packedpk, *seed;

  unpack_pk(pk, seed, packedpk);
}
