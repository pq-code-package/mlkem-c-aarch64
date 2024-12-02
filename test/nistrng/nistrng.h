/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef NISTRNG_H
#define NISTRNG_H

#include "aes.h"
#include "randombytes.h"

void nist_kat_init(
    unsigned char entropy_input[AES256_KEYBYTES + AES_BLOCKBYTES],
    const unsigned char
        personalization_string[AES256_KEYBYTES + AES_BLOCKBYTES],
    int security_strength);

#endif
