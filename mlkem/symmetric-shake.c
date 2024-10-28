// SPDX-License-Identifier: Apache-2.0
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "fips202.h"
#include "params.h"
#include "symmetric.h"

/*************************************************
 * Name:        mlkem_shake256_prf
 *
 * Description: Usage of SHAKE256 as a PRF, concatenates secret and public input
 *              and then generates outlen bytes of SHAKE256 output
 *
 * Arguments:   - uint8_t *out: pointer to output
 *              - size_t outlen: number of requested output bytes
 *              - const uint8_t *key: pointer to the key (of length
 *MLKEM_SYMBYTES)
 *              - uint8_t nonce: single-byte nonce (public PRF input)
 **************************************************/
void mlkem_shake256_prf(uint8_t *out, size_t outlen,
                        const uint8_t key[MLKEM_SYMBYTES], uint8_t nonce) {
  uint8_t extkey[MLKEM_SYMBYTES + 1];

  memcpy(extkey, key, MLKEM_SYMBYTES);
  extkey[MLKEM_SYMBYTES] = nonce;

  shake256(out, outlen, extkey, sizeof(extkey));
}

/*************************************************
 * Name:        mlkem_shake256_rkprf
 *
 * Description: Usage of SHAKE256 as a PRF, concatenates secret and public input
 *              and then generates outlen bytes of SHAKE256 output
 *
 * Arguments:   - uint8_t *out: pointer to output
 *              - size_t outlen: number of requested output bytes
 *              - const uint8_t *key: pointer to the key (of length
 *MLKEM_SYMBYTES)
 *              - uint8_t nonce: single-byte nonce (public PRF input)
 **************************************************/
void mlkem_shake256_rkprf(uint8_t out[MLKEM_SSBYTES],
                          const uint8_t key[MLKEM_SYMBYTES],
                          const uint8_t input[MLKEM_CIPHERTEXTBYTES]) {
  shake256incctx s;

  shake256_inc_init(&s);
  shake256_inc_absorb(&s, key, MLKEM_SYMBYTES);
  shake256_inc_absorb(&s, input, MLKEM_CIPHERTEXTBYTES);
  shake256_inc_finalize(&s);
  shake256_inc_squeeze(out, MLKEM_SSBYTES, &s);
}
