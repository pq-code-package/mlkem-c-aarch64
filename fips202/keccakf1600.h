// SPDX-License-Identifier: CC0-1.0
#ifndef KECCAKF1600_H
#define KECCAKF1600_H

#include <stdint.h>
#include "asm/asm.h"

#define KECCAK_WAY 4
#define KECCAK_LANES 25

// WARNING:
//
// The contents of this structure, including the placement
// and interleaving of Keccak lanes, are IMPLEMENTATION-DEFINED.
//
// The struct is only exposed here to allow its construction on the stack.
//
typedef uint64_t keccakx4_state[KECCAK_WAY * KECCAK_LANES];

void KeccakF1600_StateExtractBytes(uint64_t *state, unsigned char *data,
                                   unsigned int offset, unsigned int length);
void KeccakF1600_StateXORBytes(uint64_t *state, const unsigned char *data,
                               unsigned int offset, unsigned int length);

void KeccakF1600x4_StateExtractBytes(uint64_t *state, unsigned char *data0,
                                     unsigned char *data1, unsigned char *data2,
                                     unsigned char *data3, unsigned int offset,
                                     unsigned int length);
void KeccakF1600x4_StateXORBytes(uint64_t *state, const unsigned char *data0,
                                 const unsigned char *data1,
                                 const unsigned char *data2,
                                 const unsigned char *data3,
                                 unsigned int offset, unsigned int length);

void KeccakF1600x4_StatePermute(uint64_t *state);

#if !defined(MLKEM_USE_FIPS202_X1_ASM)
void KeccakF1600_StatePermute(uint64_t *state);
#else
#define KeccakF1600_StatePermute keccak_f1600_x1_asm
#endif

#endif
