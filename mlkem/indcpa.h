// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#ifndef INDCPA_H
#define INDCPA_H

#include <stdint.h>
#include "cbmc.h"
#include "params.h"
#include "polyvec.h"


#define gen_matrix MLKEM_NAMESPACE(gen_matrix)

void gen_matrix(polyvec *a, const uint8_t seed[MLKEM_SYMBYTES], int transposed)
__contract__(
  requires(is_fresh(a, sizeof(polyvec) * MLKEM_K))
  requires(is_fresh(seed, MLKEM_SYMBYTES))
  requires(transposed == 0 || transposed == 1)
  assigns(object_whole(a))
  ensures(forall(int, x, 0, MLKEM_K - 1, forall(int, y, 0, MLKEM_K - 1,
  array_bound(a[x].vec[y].coeffs, 0, MLKEM_N - 1, 0, (MLKEM_Q - 1)))));
);

#define indcpa_keypair_derand MLKEM_NAMESPACE(indcpa_keypair_derand)
void indcpa_keypair_derand(uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                           uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES],
                           const uint8_t coins[MLKEM_SYMBYTES])
__contract__(
  requires(is_fresh(pk, MLKEM_INDCPA_PUBLICKEYBYTES))
  requires(is_fresh(sk, MLKEM_INDCPA_SECRETKEYBYTES))
  requires(is_fresh(coins, MLKEM_SYMBYTES))
  assigns(object_whole(pk))
  assigns(object_whole(sk))
);

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
                const uint8_t coins[MLKEM_SYMBYTES])
__contract__(
  requires(is_fresh(c, MLKEM_INDCPA_BYTES))
  requires(is_fresh(m, MLKEM_INDCPA_MSGBYTES))
  requires(is_fresh(pk, MLKEM_INDCPA_PUBLICKEYBYTES))
  requires(is_fresh(coins, MLKEM_SYMBYTES))
  assigns(object_whole(c))
);

#define indcpa_dec MLKEM_NAMESPACE(indcpa_dec)
void indcpa_dec(uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const uint8_t c[MLKEM_INDCPA_BYTES],
                const uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES])
__contract__(
  requires(is_fresh(c, MLKEM_INDCPA_BYTES))
  requires(is_fresh(m, MLKEM_INDCPA_MSGBYTES))
  requires(is_fresh(sk, MLKEM_INDCPA_SECRETKEYBYTES))
  assigns(object_whole(m))
);

#endif
