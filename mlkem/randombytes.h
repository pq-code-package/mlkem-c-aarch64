// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#ifndef RANDOMBYTES_H
#define RANDOMBYTES_H

#include <stddef.h>
#include <stdint.h>

#include "cbmc.h"

void randombytes(uint8_t *out, size_t outlen)
__contract__(
  requires(is_fresh(out, outlen))
  assigns(object_upto(out, outlen))
);

#endif
