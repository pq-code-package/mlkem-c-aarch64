// SPDX-License-Identifier: Apache-2.0
#include "kem.h"
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "indcpa.h"
#include "params.h"
#include "randombytes.h"
#include "symmetric.h"
#include "verify.h"

#if defined(CBMC)
// Redeclaration with contract needed for CBMC only
int memcmp(const void *str1, const void *str2, size_t n)  // clang-format off
  REQUIRES(IS_FRESH(str1, n))
  REQUIRES(IS_FRESH(str2, n));
// clang-format on
#endif

/*************************************************
 * Name:        check_pk
 *
 * Description: Implements modulus check mandated by FIPS203,
 *              i.e., ensures that coefficients are in [0,q-1].
 *              Described in Section 7.2 of FIPS203.
 *
 * Arguments:   - const uint8_t *pk: pointer to input public key
 *                (an already allocated array of MLKEM_PUBLICKEYBYTES bytes)
 **
 * Returns 0 on success, and -1 on failure
 **************************************************/
// static int check_pk(const uint8_t pk[MLKEM_PUBLICKEYBYTES]) {
//   polyvec p;
//   uint8_t p_reencoded[MLKEM_POLYVECBYTES];
//   polyvec_frombytes(&p, pk);
//   polyvec_reduce(&p);
//   polyvec_tobytes(p_reencoded, &p);
//   // Data is public, so a variable-time memcmp() is OK
//   if (memcmp(pk, p_reencoded, MLKEM_POLYVECBYTES)) {
//     return -1;
//   }
//   return 0;
// }

/*************************************************
 * Name:        check_sk
 *
 * Description: Implements public key hash check mandated by FIPS203,
 *              i.e., ensures that
 *              sk[768𝑘+32 ∶ 768𝑘+64] = H(pk)= H(sk[384𝑘 : 768𝑘+32])
 *              Described in Section 7.3 of FIPS203.
 *
 * Arguments:   - const uint8_t *sk: pointer to input private key
 *                (an already allocated array of MLKEM_SECRETKEYBYTES bytes)
 *
 * Returns 0 on success, and -1 on failure
 **************************************************/
// static int check_sk(const uint8_t sk[MLKEM_SECRETKEYBYTES]) {
//   uint8_t test[MLKEM_SYMBYTES];
//   // The parts of `sk` being hashed and compared here are public, so
//   // no public information is leaked through the runtime or the return value
//   // of this function.
//   hash_h(test, sk + MLKEM_INDCPA_SECRETKEYBYTES, MLKEM_PUBLICKEYBYTES);
//   if (memcmp(sk + MLKEM_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES, test,
//              MLKEM_SYMBYTES)) {
//     return -1;
//   }
//   return 0;
// }

/*************************************************
 * Name:        crypto_kem_keypair_derand
 *
 * Description: Generates public and private key
 *              for CCA-secure ML-KEM key encapsulation mechanism
 *
 * Arguments:   - uint8_t *pk: pointer to output public key
 *                (an already allocated array of MLKEM_PUBLICKEYBYTES bytes)
 *              - uint8_t *sk: pointer to output private key
 *                (an already allocated array of MLKEM_SECRETKEYBYTES bytes)
 *              - uint8_t *coins: pointer to input randomness
 *                (an already allocated array filled with 2*MLKEM_SYMBYTES
 *random bytes)
 **
 * Returns 0 (success)
 **************************************************/
int crypto_kem_keypair_derand(uint8_t *pk, uint8_t *sk, const uint8_t *coins) {
  indcpa_keypair_derand(pk, sk, coins);
  memcpy(sk + MLKEM_INDCPA_SECRETKEYBYTES, pk, MLKEM_PUBLICKEYBYTES);
  hash_h(sk + MLKEM_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES, pk,
         MLKEM_PUBLICKEYBYTES);
  /* Value z for pseudo-random output on reject */
  memcpy(sk + MLKEM_SECRETKEYBYTES - MLKEM_SYMBYTES, coins + MLKEM_SYMBYTES,
         MLKEM_SYMBYTES);
  return 0;
}

int crypto_kem_keypair(uint8_t *pk, uint8_t *sk) {
  ALIGN uint8_t coins[2 * MLKEM_SYMBYTES];
  randombytes(coins, 2 * MLKEM_SYMBYTES);
  crypto_kem_keypair_derand(pk, sk, coins);
  return 0;
}

int crypto_kem_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk,
                          const uint8_t *coins) {
  ALIGN uint8_t buf[2 * MLKEM_SYMBYTES];
  /* Will contain key, coins */
  ALIGN uint8_t kr[2 * MLKEM_SYMBYTES];

  // if (check_pk(pk)) {
    // return -1;
  // }

  memcpy(buf, coins, MLKEM_SYMBYTES);

  /* Multitarget countermeasure for coins + contributory KEM */
  hash_h(buf + MLKEM_SYMBYTES, pk, MLKEM_PUBLICKEYBYTES);
  hash_g(kr, buf, 2 * MLKEM_SYMBYTES);

  /* coins are in kr+MLKEM_SYMBYTES */
  indcpa_enc(ct, buf, pk, kr + MLKEM_SYMBYTES);

  memcpy(ss, kr, MLKEM_SYMBYTES);
  return 0;
}

int crypto_kem_enc(uint8_t *ct, uint8_t *ss, const uint8_t *pk) {
  ALIGN uint8_t coins[MLKEM_SYMBYTES];
  randombytes(coins, MLKEM_SYMBYTES);
  return crypto_kem_enc_derand(ct, ss, pk, coins);
}

int crypto_kem_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk) {
  int fail;
  ALIGN uint8_t buf[2 * MLKEM_SYMBYTES];
  /* Will contain key, coins */
  ALIGN uint8_t kr[2 * MLKEM_SYMBYTES];
  ALIGN uint8_t cmp[MLKEM_CIPHERTEXTBYTES + MLKEM_SYMBYTES];
  const uint8_t *pk = sk + MLKEM_INDCPA_SECRETKEYBYTES;

  // if (check_sk(sk)) {
  //   return -1;
  // }

  indcpa_dec(buf, ct, sk);

  /* Multitarget countermeasure for coins + contributory KEM */
  memcpy(buf + MLKEM_SYMBYTES, sk + MLKEM_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES,
         MLKEM_SYMBYTES);
  hash_g(kr, buf, 2 * MLKEM_SYMBYTES);

  /* coins are in kr+MLKEM_SYMBYTES */
  indcpa_enc(cmp, buf, pk, kr + MLKEM_SYMBYTES);

  fail = verify(ct, cmp, MLKEM_CIPHERTEXTBYTES);

  /* Compute rejection key */
  rkprf(ss, sk + MLKEM_SECRETKEYBYTES - MLKEM_SYMBYTES, ct);

  /* Copy true key to return buffer if fail is false */
  cmov(ss, kr, MLKEM_SYMBYTES, !fail);

  return 0;
}
