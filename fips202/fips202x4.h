// SPDX-License-Identifier: Apache-2.0
#ifndef FIPS_202X4_H
#define FIPS_202X4_H

#ifndef KECCAK_WAY
#define KECCAK_WAY 4
#endif

#include <stdint.h>

// WARNING:
//
// The contents of this structure, including the placement
// and interleaving of Keccak lanes, are IMPLEMENTATION-DEFINED.
//
// The struct is only exposed here to allow its construction on the stack.
//
typedef uint8_t shakex4_state[KECCAK_WAY * 25 * 8];

void shake128x4_absorb(shakex4_state *state,
                       const uint8_t *in0,
                       const uint8_t *in1,
                       const uint8_t *in2,
                       const uint8_t *in3,
                       size_t inlen);

void shake256x4_absorb(shakex4_state *state,
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
                              shakex4_state *state);

void shake256x4_squeezeblocks(uint8_t *out0,
                              uint8_t *out1,
                              uint8_t *out2,
                              uint8_t *out3,
                              size_t nblocks,
                              shakex4_state *state);


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
