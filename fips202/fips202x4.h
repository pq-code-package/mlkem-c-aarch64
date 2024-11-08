// SPDX-License-Identifier: Apache-2.0
#ifndef FIPS_202X4_H
#define FIPS_202X4_H

#include <stddef.h>
#include <stdint.h>
#include "fips202.h"
#include "keccakf1600.h"
#include "namespace.h"

#include "cbmc.h"

#define shake128x4_absorb FIPS202_NAMESPACE(shake128x4_absorb)
void shake128x4_absorb(keccakx4_state *state, const uint8_t *in0,
                       const uint8_t *in1, const uint8_t *in2,
                       const uint8_t *in3, size_t inlen);

// clang-format off
#define shake256x4_absorb FIPS202_NAMESPACE(shake256x4_absorb)
void shake256x4_absorb(keccakx4_state *state, const uint8_t *in0,
                       const uint8_t *in1, const uint8_t *in2,
                       const uint8_t *in3, size_t inlen)
REQUIRES(IS_FRESH(state, sizeof(keccakx4_state)))
REQUIRES(IS_FRESH(in0, inlen))
REQUIRES(IS_FRESH(in1, inlen))
REQUIRES(IS_FRESH(in2, inlen))
REQUIRES(IS_FRESH(in3, inlen))
ASSIGNS(OBJECT_WHOLE(state));
// clang-format on

// clang-format off
#define shake128x4_squeezeblocks FIPS202_NAMESPACE(shake128x4_squeezeblocks)
void shake128x4_squeezeblocks(uint8_t *out0, uint8_t *out1, uint8_t *out2,
                              uint8_t *out3, size_t nblocks,
                              keccakx4_state *state)
REQUIRES(IS_FRESH(state, sizeof(keccakx4_state)))
REQUIRES(IS_FRESH(out0, nblocks * SHAKE128_RATE))
REQUIRES(IS_FRESH(out1, nblocks * SHAKE128_RATE))
REQUIRES(IS_FRESH(out2, nblocks * SHAKE128_RATE))
REQUIRES(IS_FRESH(out3, nblocks * SHAKE128_RATE))
ASSIGNS(OBJECT_UPTO(out0, nblocks * SHAKE128_RATE),
  OBJECT_UPTO(out1, nblocks * SHAKE128_RATE),
  OBJECT_UPTO(out2, nblocks * SHAKE128_RATE),
  OBJECT_UPTO(out3, nblocks * SHAKE128_RATE),
  OBJECT_WHOLE(state));
// clang-format on

#define shake256x4_squeezeblocks FIPS202_NAMESPACE(shake256x4_squeezeblocks)
void shake256x4_squeezeblocks(uint8_t *out0, uint8_t *out1, uint8_t *out2,
                              uint8_t *out3, size_t nblocks,
                              keccakx4_state *state);

#define shake128x4_ctx_release FIPS202_NAMESPACE(shake128x4_ctx_release)
void shake128x4_ctx_release(keccakx4_state *state);

#define shake256x4_ctx_release FIPS202_NAMESPACE(shake256x4_ctx_release)
void shake256x4_ctx_release(keccakx4_state *state);

#define shake256x4 FIPS202_NAMESPACE(shake256x4)
void shake256x4(uint8_t *out0, uint8_t *out1, uint8_t *out2, uint8_t *out3,
                size_t outlen, uint8_t *in0, uint8_t *in1, uint8_t *in2,
                uint8_t *in3, size_t inlen)  // clang-format off
// Refine +prove this spec, e.g. add disjointness constraints?
REQUIRES(READABLE(in0, inlen))
REQUIRES(READABLE(in1, inlen))
REQUIRES(READABLE(in2, inlen))
REQUIRES(READABLE(in3, inlen))
REQUIRES(WRITEABLE(out0, outlen))
REQUIRES(WRITEABLE(out1, outlen))
REQUIRES(WRITEABLE(out2, outlen))
REQUIRES(WRITEABLE(out3, outlen))
ASSIGNS(OBJECT_UPTO(out0, outlen))
ASSIGNS(OBJECT_UPTO(out1, outlen))
ASSIGNS(OBJECT_UPTO(out2, outlen))
ASSIGNS(OBJECT_UPTO(out3, outlen));
// clang-format on

#endif
