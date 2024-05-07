// SPDX-License-Identifier: Apache-2.0

#ifndef RANDOMBYTES_H
#define RANDOMBYTES_H

#include <stdint.h>
#include "aes.h"

void randombytes(uint8_t *buf, size_t n);

void nist_kat_init(unsigned char entropy_input[AES256_KEYBYTES + AES_BLOCKBYTES], const unsigned char personalization_string[AES256_KEYBYTES + AES_BLOCKBYTES], int security_strength);

#endif
