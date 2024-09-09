// SPDX-License-Identifier: Apache-2.0
#ifndef ASM_H
#define ASM_H

#include <stdint.h>
#include "params.h"

#ifdef MLKEM_OPT_AARCH64
void ntt_kyber_123_4567(int16_t *);
void intt_kyber_123_4567(int16_t *);
#endif

#endif
