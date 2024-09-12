// SPDX-License-Identifier: Apache-2.0
#ifndef ASM_H
#define ASM_H

#include <stdint.h>
#include "params.h"
#include "config.h"

#ifdef MLKEM_USE_AARCH64_ASM
void ntt_kyber_123_4567(int16_t *);
void intt_kyber_123_4567(int16_t *);
#endif /* MLKEM_USE_AARCH64_ASM */

#endif
