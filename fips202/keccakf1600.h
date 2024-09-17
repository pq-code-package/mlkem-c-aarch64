// SPDX-License-Identifier: CC0-1.0
#ifndef KECCAKF1600_H
#define KECCAKF1600_H

#include "asm/asm.h"
#include <stdint.h>

void KeccakF1600_StateExtractBytes(uint64_t *state, unsigned char *data, unsigned int offset, unsigned int length);
void KeccakF1600_StateXORBytes(uint64_t *state, const unsigned char *data, unsigned int offset, unsigned int length);

#if !defined(MLKEM_USE_AARCH64_ASM)
void KeccakF1600_StatePermute(uint64_t *state);
#else
#define KeccakF1600_StatePermute keccak_f1600_x1_asm
#endif

#endif
