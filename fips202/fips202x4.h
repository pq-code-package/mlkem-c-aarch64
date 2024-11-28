// Copyright (c) 2024 The mlkem-native project authors
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


#define shake256x4_absorb FIPS202_NAMESPACE(shake256x4_absorb)
void shake256x4_absorb(keccakx4_state *state, const uint8_t *in0,
                       const uint8_t *in1, const uint8_t *in2,
                       const uint8_t *in3, size_t inlen)
__contract__(
  requires(is_fresh(state, sizeof(keccakx4_state)))
  requires(is_fresh(in0, inlen))
  requires(is_fresh(in1, inlen))
  requires(is_fresh(in2, inlen))
  requires(is_fresh(in3, inlen))
  assigns(object_whole(state))
);

#define shake128x4_squeezeblocks FIPS202_NAMESPACE(shake128x4_squeezeblocks)
void shake128x4_squeezeblocks(uint8_t *out0, uint8_t *out1, uint8_t *out2,
                              uint8_t *out3, size_t nblocks,
                              keccakx4_state *state)
__contract__(
  requires(is_fresh(state, sizeof(keccakx4_state)))
  requires(is_fresh(out0, nblocks * SHAKE128_RATE))
  requires(is_fresh(out1, nblocks * SHAKE128_RATE))
  requires(is_fresh(out2, nblocks * SHAKE128_RATE))
  requires(is_fresh(out3, nblocks * SHAKE128_RATE))
  assigns(object_upto(out0, nblocks * SHAKE128_RATE),
  object_upto(out1, nblocks * SHAKE128_RATE),
  object_upto(out2, nblocks * SHAKE128_RATE),
  object_upto(out3, nblocks * SHAKE128_RATE),
  object_whole(state));
);

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
                uint8_t *in3, size_t inlen)
__contract__(
// Refine +prove this spec, e.g. add disjointness constraints?
  requires(READABLE(in0, inlen))
  requires(READABLE(in1, inlen))
  requires(READABLE(in2, inlen))
  requires(READABLE(in3, inlen))
  requires(WRITEABLE(out0, outlen))
  requires(WRITEABLE(out1, outlen))
  requires(WRITEABLE(out2, outlen))
  requires(WRITEABLE(out3, outlen))
  assigns(object_upto(out0, outlen))
  assigns(object_upto(out1, outlen))
  assigns(object_upto(out2, outlen))
  assigns(object_upto(out3, outlen))
);

#endif
