// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#ifndef INDCPA_H
#define INDCPA_H

#include <stdint.h>
#include "cbmc.h"
#include "params.h"
#include "polyvec.h"


#define gen_matrix MLKEM_NAMESPACE(gen_matrix)

void gen_matrix(polyvec *a, const uint8_t seed[MLKEM_SYMBYTES],
                int transposed)  // clang-format off
REQUIRES(IS_FRESH(a, sizeof(polyvec) * MLKEM_K))
REQUIRES(IS_FRESH(seed, MLKEM_SYMBYTES))
REQUIRES(transposed == 0 || transposed == 1)
ASSIGNS(OBJECT_WHOLE(a))
ENSURES(FORALL(int, x, 0, MLKEM_K - 1, FORALL(int, y, 0, MLKEM_K - 1,
  ARRAY_BOUND(a[x].vec[y].coeffs, 0, MLKEM_N - 1, 0, (MLKEM_Q - 1)))));
// clang-format on

#define indcpa_keypair_derand MLKEM_NAMESPACE(indcpa_keypair_derand)
void indcpa_keypair_derand(
    uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
    uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES],
    const uint8_t coins[MLKEM_SYMBYTES])  // clang-format off
REQUIRES(IS_FRESH(pk, MLKEM_INDCPA_PUBLICKEYBYTES))
REQUIRES(IS_FRESH(sk, MLKEM_INDCPA_SECRETKEYBYTES))
REQUIRES(IS_FRESH(coins, MLKEM_SYMBYTES))
ASSIGNS(OBJECT_WHOLE(pk))
ASSIGNS(OBJECT_WHOLE(sk));
// clang-format on

#define indcpa_enc MLKEM_NAMESPACE(indcpa_enc)
/*************************************************
 * Name:        indcpa_dec
 *
 * Description: Decryption function of the CPA-secure
 *              public-key encryption scheme underlying Kyber.
 *
 * Arguments:   - uint8_t *m: pointer to output decrypted message
 *                            (of length MLKEM_INDCPA_MSGBYTES)
 *              - const uint8_t *c: pointer to input ciphertext
 *                                  (of length MLKEM_INDCPA_BYTES)
 *              - const uint8_t *sk: pointer to input secret key
 *                                   (of length MLKEM_INDCPA_SECRETKEYBYTES)
 **************************************************/
void indcpa_enc(uint8_t c[MLKEM_INDCPA_BYTES],
                const uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                const uint8_t coins[MLKEM_SYMBYTES])  // clang-format off
REQUIRES(IS_FRESH(c, MLKEM_INDCPA_BYTES))
REQUIRES(IS_FRESH(m, MLKEM_INDCPA_MSGBYTES))
REQUIRES(IS_FRESH(pk, MLKEM_INDCPA_PUBLICKEYBYTES))
REQUIRES(IS_FRESH(coins, MLKEM_SYMBYTES))
ASSIGNS(OBJECT_WHOLE(c));
// clang-format on

#define indcpa_dec MLKEM_NAMESPACE(indcpa_dec)
void indcpa_dec(
    uint8_t m[MLKEM_INDCPA_MSGBYTES], const uint8_t c[MLKEM_INDCPA_BYTES],
    const uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES])  // clang-format off
REQUIRES(IS_FRESH(c, MLKEM_INDCPA_BYTES))
REQUIRES(IS_FRESH(m, MLKEM_INDCPA_MSGBYTES))
REQUIRES(IS_FRESH(sk, MLKEM_INDCPA_SECRETKEYBYTES))
ASSIGNS(OBJECT_WHOLE(m));
// clang-format on

#endif
