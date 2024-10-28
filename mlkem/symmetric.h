// SPDX-License-Identifier: Apache-2.0
#ifndef SYMMETRIC_H
#define SYMMETRIC_H

#include <stddef.h>
#include <stdint.h>
#include "params.h"

#include "fips202.h"

#define mlkem_shake256_prf MLKEM_NAMESPACE(mlkem_shake256_prf)
void mlkem_shake256_prf(uint8_t *out, size_t outlen,
                        const uint8_t key[MLKEM_SYMBYTES], uint8_t nonce);

#define mlkem_shake256_rkprf MLKEM_NAMESPACE(mlkem_shake256_rkprf)
void mlkem_shake256_rkprf(uint8_t out[MLKEM_SSBYTES],
                          const uint8_t key[MLKEM_SYMBYTES],
                          const uint8_t input[MLKEM_CIPHERTEXTBYTES]);

#define hash_h(OUT, IN, INBYTES) sha3_256(OUT, IN, INBYTES)
#define hash_g(OUT, IN, INBYTES) sha3_512(OUT, IN, INBYTES)
#define prf(OUT, OUTBYTES, KEY, NONCE) \
  mlkem_shake256_prf(OUT, OUTBYTES, KEY, NONCE)
#define rkprf(OUT, KEY, INPUT) mlkem_shake256_rkprf(OUT, KEY, INPUT)

#endif /* SYMMETRIC_H */
