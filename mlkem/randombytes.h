// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#ifndef RANDOMBYTES_H
#define RANDOMBYTES_H

#include <stddef.h>
#include <stdint.h>

#include "cbmc.h"

void randombytes(uint8_t *out, size_t outlen)  // clang-format off
REQUIRES(IS_FRESH(out, outlen))
ASSIGNS(OBJECT_UPTO(out, outlen));
// clang-format on

#endif
