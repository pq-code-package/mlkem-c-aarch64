// SPDX-License-Identifier: Apache-2.0
#ifndef KEM_H
#define KEM_H

#include <stdint.h>
#include "cbmc.h"
#include "params.h"

#define CRYPTO_SECRETKEYBYTES MLKEM_SECRETKEYBYTES
#define CRYPTO_PUBLICKEYBYTES MLKEM_PUBLICKEYBYTES
#define CRYPTO_CIPHERTEXTBYTES MLKEM_CIPHERTEXTBYTES
#define CRYPTO_BYTES MLKEM_SSBYTES

#if (MLKEM_K == 2)
#define CRYPTO_ALGNAME "Kyber512"
#elif (MLKEM_K == 3)
#define CRYPTO_ALGNAME "Kyber768"
#elif (MLKEM_K == 4)
#define CRYPTO_ALGNAME "Kyber1024"
#endif

#define crypto_kem_keypair_derand MLKEM_NAMESPACE(keypair_derand)
int crypto_kem_keypair_derand(uint8_t *pk, uint8_t *sk,
                              const uint8_t *coins)  // clang-format off
REQUIRES(IS_FRESH(pk, MLKEM_PUBLICKEYBYTES))
REQUIRES(IS_FRESH(sk, MLKEM_SECRETKEYBYTES))
REQUIRES(IS_FRESH(coins, 2 * MLKEM_SYMBYTES))
ASSIGNS(OBJECT_WHOLE(pk))
ASSIGNS(OBJECT_WHOLE(sk));
// clang-format on

#define crypto_kem_keypair MLKEM_NAMESPACE(keypair)
/*************************************************
 * Name:        crypto_kem_keypair
 *
 * Description: Generates public and private key
 *              for CCA-secure ML-KEM key encapsulation mechanism
 *
 * Arguments:   - uint8_t *pk: pointer to output public key
 *                (an already allocated array of MLKEM_PUBLICKEYBYTES bytes)
 *              - uint8_t *sk: pointer to output private key
 *                (an already allocated array of MLKEM_SECRETKEYBYTES bytes)
 *
 * Returns 0 (success)
 **************************************************/
int crypto_kem_keypair(uint8_t *pk, uint8_t *sk)  // clang-format off
REQUIRES(IS_FRESH(pk, MLKEM_PUBLICKEYBYTES))
REQUIRES(IS_FRESH(sk, MLKEM_SECRETKEYBYTES))
ASSIGNS(OBJECT_WHOLE(pk))
ASSIGNS(OBJECT_WHOLE(sk));
// clang-format on

#define crypto_kem_enc_derand MLKEM_NAMESPACE(enc_derand)
/*************************************************
 * Name:        crypto_kem_enc_derand
 *
 * Description: Generates cipher text and shared
 *              secret for given public key
 *
 * Arguments:   - uint8_t *ct: pointer to output cipher text
 *                (an already allocated array of MLKEM_CIPHERTEXTBYTES bytes)
 *              - uint8_t *ss: pointer to output shared secret
 *                (an already allocated array of MLKEM_SSBYTES bytes)
 *              - const uint8_t *pk: pointer to input public key
 *                (an already allocated array of MLKEM_PUBLICKEYBYTES bytes)
 *              - const uint8_t *coins: pointer to input randomness
 *                (an already allocated array filled with MLKEM_SYMBYTES random
 *bytes)
 **
 * Returns 0 on success, and -1 if the public key modulus check (see Section 7.2
 * of FIPS203) fails.
 **************************************************/
int crypto_kem_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk,
                          const uint8_t *coins)  // clang-format off
REQUIRES(IS_FRESH(ct, MLKEM_CIPHERTEXTBYTES))
REQUIRES(IS_FRESH(ss, MLKEM_SSBYTES))
REQUIRES(IS_FRESH(pk, MLKEM_PUBLICKEYBYTES))
REQUIRES(IS_FRESH(coins, MLKEM_SYMBYTES))
ASSIGNS(OBJECT_WHOLE(ct))
ASSIGNS(OBJECT_WHOLE(ss));
// clang-format on

#define crypto_kem_enc MLKEM_NAMESPACE(enc)
/*************************************************
 * Name:        crypto_kem_enc
 *
 * Description: Generates cipher text and shared
 *              secret for given public key
 *
 * Arguments:   - uint8_t *ct: pointer to output cipher text
 *                (an already allocated array of MLKEM_CIPHERTEXTBYTES bytes)
 *              - uint8_t *ss: pointer to output shared secret
 *                (an already allocated array of MLKEM_SSBYTES bytes)
 *              - const uint8_t *pk: pointer to input public key
 *                (an already allocated array of MLKEM_PUBLICKEYBYTES bytes)
 *
 * Returns 0 on success, and -1 if the public key modulus check (see Section 7.2
 * of FIPS203) fails.
 **************************************************/
int crypto_kem_enc(uint8_t *ct, uint8_t *ss,
                   const uint8_t *pk)  // clang-format off
REQUIRES(IS_FRESH(ct, MLKEM_CIPHERTEXTBYTES))
REQUIRES(IS_FRESH(ss, MLKEM_SSBYTES))
REQUIRES(IS_FRESH(pk, MLKEM_PUBLICKEYBYTES))
ASSIGNS(OBJECT_WHOLE(ct))
ASSIGNS(OBJECT_WHOLE(ss));
// clang-format on

#define crypto_kem_dec MLKEM_NAMESPACE(dec)
/*************************************************
 * Name:        crypto_kem_dec
 *
 * Description: Generates shared secret for given
 *              cipher text and private key
 *
 * Arguments:   - uint8_t *ss: pointer to output shared secret
 *                (an already allocated array of MLKEM_SSBYTES bytes)
 *              - const uint8_t *ct: pointer to input cipher text
 *                (an already allocated array of MLKEM_CIPHERTEXTBYTES bytes)
 *              - const uint8_t *sk: pointer to input private key
 *                (an already allocated array of MLKEM_SECRETKEYBYTES bytes)
 *
 * Returns 0 on success, and -1 if the secret key hash check (see Section 7.3 of
 * FIPS203) fails.
 *
 * On failure, ss will contain a pseudo-random value.
 **************************************************/
int crypto_kem_dec(uint8_t *ss, const uint8_t *ct,
                   const uint8_t *sk)  // clang-format off
REQUIRES(IS_FRESH(ss, MLKEM_SSBYTES))
REQUIRES(IS_FRESH(ct, MLKEM_CIPHERTEXTBYTES))
REQUIRES(IS_FRESH(sk, MLKEM_SECRETKEYBYTES))
ASSIGNS(OBJECT_WHOLE(ss));
// clang-format on

#endif
