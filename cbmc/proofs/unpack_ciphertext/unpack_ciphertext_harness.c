// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include <stdint.h>
#include "polyvec.h"

void unpack_ciphertext(polyvec *b, poly *v,
                       const uint8_t c[MLKEM_INDCPA_BYTES]);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  polyvec *b;
  poly *v;
  uint8_t *c;

  unpack_ciphertext(b, v, c);
}
