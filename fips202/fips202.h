// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: CC0-1.0
#ifndef FIPS202_H
#define FIPS202_H

#include <stddef.h>
#include <stdint.h>
#include "namespace.h"

#include "cbmc.h"

#define SHAKE128_RATE 168
#define SHAKE256_RATE 136
#define SHA3_256_RATE 136
#define SHA3_384_RATE 104
#define SHA3_512_RATE 72


// Context for non-incremental API
typedef struct
{
  uint64_t ctx[25];
} shake128ctx;

// Context for incremental API
typedef struct
{
  uint64_t ctx[26];
} shake256incctx;

/* Initialize the state and absorb the provided input.
 *
 * This function does not support being called multiple times
 * with the same state.
 */
#define shake128_absorb FIPS202_NAMESPACE(shake128_absorb)
void shake128_absorb(shake128ctx *state, const uint8_t *input, size_t inlen)
__contract__(
  requires(memory_no_alias(state, sizeof(shake128ctx)))
  requires(memory_no_alias(input, inlen))
  assigns(memory_slice(state, sizeof(shake128ctx)))
);

/* Squeeze output out of the sponge.
 *
 * Supports being called multiple times
 */
#define shake128_squeezeblocks FIPS202_NAMESPACE(shake128_squeezeblocks)
void shake128_squeezeblocks(uint8_t *output, size_t nblocks, shake128ctx *state)
__contract__(
  requires(memory_no_alias(state, sizeof(shake128ctx)))
  requires(memory_no_alias(output, nblocks * SHAKE128_RATE))
  assigns(memory_slice(output, nblocks * SHAKE128_RATE), memory_slice(state, sizeof(shake128ctx)))
);

/* Free the state */
#define shake128_ctx_release FIPS202_NAMESPACE(shake128_ctx_release)
void shake128_ctx_release(shake128ctx *state);

/* Initialize incremental hashing API */
#define shake256_inc_init FIPS202_NAMESPACE(shake256_inc_init)
void shake256_inc_init(shake256incctx *state);
#define shake256_inc_absorb FIPS202_NAMESPACE(shake256_inc_absorb)
void shake256_inc_absorb(shake256incctx *state, const uint8_t *input,
                         size_t inlen);
/* Prepares for squeeze phase */
#define shake256_inc_finalize FIPS202_NAMESPACE(shake256_inc_finalize)
void shake256_inc_finalize(shake256incctx *state);

/* Squeeze output out of the sponge.
 *
 * Supports being called multiple times
 */
#define shake256_inc_squeeze FIPS202_NAMESPACE(shake256_inc_squeeze)
void shake256_inc_squeeze(uint8_t *output, size_t outlen,
                          shake256incctx *state);

/* Free the state */
#define shake256_inc_ctx_release FIPS202_NAMESPACE(shake256_inc_ctx_release)
void shake256_inc_ctx_release(shake256incctx *state);

/* One-stop SHAKE256 call. Aliasing between input and
 * output is not permitted */
#define shake256 FIPS202_NAMESPACE(shake256)
void shake256(uint8_t *output, size_t outlen, const uint8_t *input,
              size_t inlen)
__contract__(
  requires(memory_no_alias(input, inlen))
  requires(memory_no_alias(output, outlen))
  assigns(memory_slice(output, outlen))
);

/* One-stop SHA3_256 call. Aliasing between input and
 * output is not permitted */
#define SHA3_256_HASHBYTES 32
#define sha3_256 FIPS202_NAMESPACE(sha3_256)
void sha3_256(uint8_t *output, const uint8_t *input, size_t inlen)
__contract__(
  requires(memory_no_alias(input, inlen))
  requires(memory_no_alias(output, SHA3_256_HASHBYTES))
  assigns(memory_slice(output, SHA3_256_HASHBYTES))
);

/* One-stop SHA3_512 call. Aliasing between input and
 * output is not permitted */
#define SHA3_512_HASHBYTES 64
#define sha3_512 FIPS202_NAMESPACE(sha3_512)
void sha3_512(uint8_t *output, const uint8_t *input, size_t inlen)
__contract__(
  requires(memory_no_alias(input, inlen))
  requires(memory_no_alias(output, SHA3_512_HASHBYTES))
  assigns(memory_slice(output, SHA3_512_HASHBYTES))
);

#endif
