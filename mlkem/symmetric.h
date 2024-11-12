// SPDX-License-Identifier: Apache-2.0
#ifndef SYMMETRIC_H
#define SYMMETRIC_H

#include <stddef.h>
#include <stdint.h>
#include "params.h"

#include "fips202.h"

#include "cbmc.h"

#define mlkem_shake256_prf MLKEM_NAMESPACE(mlkem_shake256_prf)
/*************************************************
 * Name:        mlkem_shake256_prf
 *
 * Ref:         FIPS-203 Section 4.1. Function PRF (eq 4.3)
 *
 * Description: Usage of SHAKE256 as a PRF, concatenates secret and public input
 *              and then generates outlen bytes of SHAKE256 output
 *
 * Arguments:   - uint8_t *out: pointer to output
 *              - size_t outlen: number of requested output bytes
 *              - const uint8_t *key: pointer to the key (of length
 *                MLKEM_SYMBYTES)
 *              - uint8_t nonce: single-byte nonce (public PRF input)
 *
 *              out and key may NOT be aliased.
 **************************************************/
void mlkem_shake256_prf(uint8_t *out, size_t outlen,
                        const uint8_t key[MLKEM_SYMBYTES],
                        uint8_t nonce)  // clang-format off
REQUIRES(IS_FRESH(out, outlen))
REQUIRES(IS_FRESH(key, MLKEM_SYMBYTES))
ASSIGNS(OBJECT_UPTO(out, outlen));
// clang-format on

#define mlkem_shake256_rkprf MLKEM_NAMESPACE(mlkem_shake256_rkprf)
/*************************************************
 * Name:        mlkem_shake256_rkprf
 *
 * Ref:         FIPS-203 Section 4.1. Hash function J
 *
 * Description: Usage of SHAKE256 as a PRF, concatenates key with input
 *              and then generates MLKEM_SSBYTES bytes of SHAKE256 output
 *
 * Arguments:   - uint8_t *out: pointer to output
 *              - const uint8_t *key: pointer to the key (of length
 *                MLKEM_SYMBYTES)
 *              - const uint8_t *input: pointer to the input (of length
 *                MLKEM_CIPHERTEXTBYTES)
 *
 *              out, key, and input may NOT be aliased.
 **************************************************/
void mlkem_shake256_rkprf(
    uint8_t out[MLKEM_SSBYTES], const uint8_t key[MLKEM_SYMBYTES],
    const uint8_t input[MLKEM_CIPHERTEXTBYTES])  // clang-format off
REQUIRES(IS_FRESH(out, MLKEM_SSBYTES))
REQUIRES(IS_FRESH(key, MLKEM_SYMBYTES))
REQUIRES(IS_FRESH(input, MLKEM_CIPHERTEXTBYTES))
ASSIGNS(OBJECT_UPTO(out, MLKEM_SSBYTES));
// clang-format on


// Macros denoting FIPS-203 specific Hash functions

// Hash function H, FIPS-201 4.1 (eq 4.4)
#define hash_h(OUT, IN, INBYTES) sha3_256(OUT, IN, INBYTES)

// Hash function G, FIPS-201 4.1 (eq 4.5)
#define hash_g(OUT, IN, INBYTES) sha3_512(OUT, IN, INBYTES)

// Macros denoting FIPS-203 specific PRFs
#define prf(OUT, OUTBYTES, KEY, NONCE) \
  mlkem_shake256_prf(OUT, OUTBYTES, KEY, NONCE)
#define rkprf(OUT, KEY, INPUT) mlkem_shake256_rkprf(OUT, KEY, INPUT)

#endif /* SYMMETRIC_H */
