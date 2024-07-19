// SPDX-License-Identifier: Apache-2.0
#ifndef FIPS_202X4_H
#define FIPS_202X4_H

#ifndef KECCAK_WAY
#define KECCAK_WAY 4
#endif

#include <stdint.h>

typedef struct
{
    uint64_t ctx[25 * KECCAK_WAY];
} keccakx4_state;

uint64_t *keccakx_get_lane_state(keccakx4_state *state, size_t index);

void shake128x4_absorb(keccakx4_state *state,
                       const uint8_t *in0,
                       const uint8_t *in1,
                       const uint8_t *in2,
                       const uint8_t *in3,
                       size_t inlen);

void shake256x4_absorb(keccakx4_state *state,
                       const uint8_t *in0,
                       const uint8_t *in1,
                       const uint8_t *in2,
                       const uint8_t *in3,
                       size_t inlen);


void shake128x4_squeezeblocks(uint8_t *out0,
                              uint8_t *out1,
                              uint8_t *out2,
                              uint8_t *out3,
                              size_t nblocks,
                              keccakx4_state *state);

void shake256x4_squeezeblocks(uint8_t *out0,
                              uint8_t *out1,
                              uint8_t *out2,
                              uint8_t *out3,
                              size_t nblocks,
                              keccakx4_state *state);

/*
 * Squeezes a single lane in Keccak 4-way
 */
void shake256x4_squeezeblocks_single(uint8_t *out,
                                     size_t nblocks,
                                     size_t index,
                                     keccakx4_state *state);

void shake256x4(uint8_t *out0,
                uint8_t *out1,
                uint8_t *out2,
                uint8_t *out3,
                size_t outlen,
                uint8_t *in0,
                uint8_t *in1,
                uint8_t *in2,
                uint8_t *in3,
                size_t inlen);

#endif
