// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include <stdint.h>
#include "polyvec.h"

void pack_pk(uint8_t r[MLKEM_INDCPA_PUBLICKEYBYTES], polyvec *pk,
             const uint8_t seed[MLKEM_SYMBYTES]);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  polyvec *pk;
  uint8_t *r, *seed;

  pack_pk(r, pk, seed);
}
