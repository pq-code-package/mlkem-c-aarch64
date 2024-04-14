// SPDX-License-Identifier: Apache-2.0
#ifndef RNG_H
#define RNG_H

#include <stddef.h>
#include <stdint.h>

void randombytes(uint8_t *out, size_t outlen);

void nist_kat_init(uint8_t *entropy_input, const uint8_t *personalization_string, int security_strength);

#endif
