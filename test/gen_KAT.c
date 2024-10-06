// SPDX-License-Identifier: Apache-2.0
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "fips202.h"
#include "kem.h"
#include "params.h"

#define NTESTS 10000

static void print_hex(const char *label, const uint8_t *data, size_t size) {
  printf("%s = ", label);
  for (size_t i = 0; i < size; i++) {
    printf("%02x", data[i]);
  }
  printf("\n");
}

static void shake256_absorb(shake256incctx *state, const uint8_t *input,
                            size_t inlen) {
  shake256_inc_init(state);
  shake256_inc_absorb(state, input, inlen);
  shake256_inc_finalize(state);
}

int main(void) {
  uint8_t coins[3 * KYBER_SYMBYTES] ALIGN;
  uint8_t pk[CRYPTO_PUBLICKEYBYTES] ALIGN;
  uint8_t sk[CRYPTO_SECRETKEYBYTES] ALIGN;
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES] ALIGN;
  uint8_t ss1[CRYPTO_BYTES] ALIGN;
  uint8_t ss2[CRYPTO_BYTES] ALIGN;

  const uint8_t seed[64] = {
      32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
      48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
      64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
      80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
  };

  shake256incctx state;
  shake256_absorb(&state, seed, sizeof(seed));

  for (unsigned int i = 0; i < NTESTS; i++) {
    shake256_inc_squeeze(coins, sizeof(coins), &state);

    crypto_kem_keypair_derand(pk, sk, coins);
    print_hex("pk", pk, sizeof(pk));
    print_hex("sk", sk, sizeof(sk));

    crypto_kem_enc_derand(ct, ss1, pk, coins + 2 * KYBER_SYMBYTES);
    print_hex("ct", ct, sizeof(ct));

    crypto_kem_dec(ss2, ct, sk);

    if (memcmp(ss1, ss2, sizeof(ss1))) {
      fprintf(stderr, "ERROR\n");
      return -1;
    }

    print_hex("ss", ss1, sizeof(ss1));
  }

  return 0;
}
