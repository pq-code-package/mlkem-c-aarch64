// SPDX-License-Identifier: Apache-2.0
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "hal.h"
#include "kem.h"
#include "randombytes.h"

#define NWARMUP 50
#define NITERERATIONS 300
#define NTESTS 200

static int cmp_uint64_t(const void *a, const void *b) {
  return (int)((*((const uint64_t *)a)) - (*((const uint64_t *)b)));
}

static int bench(void) {
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  unsigned char kg_rand[2 * CRYPTO_BYTES], enc_rand[CRYPTO_BYTES];
  uint64_t cycles_kg[NTESTS], cycles_enc[NTESTS], cycles_dec[NTESTS];

  unsigned int i, j;
  uint64_t t0, t1;


  for (i = 0; i < NTESTS; i++) {
    randombytes(kg_rand, 2 * CRYPTO_BYTES);
    randombytes(enc_rand, CRYPTO_BYTES);

    // Key-pair generation
    for (j = 0; j < NWARMUP; j++) {
      crypto_kem_keypair_derand(pk, sk, kg_rand);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERERATIONS; j++) {
      crypto_kem_keypair_derand(pk, sk, kg_rand);
    }
    t1 = get_cyclecounter();
    cycles_kg[i] = t1 - t0;


    // Encapsulation
    for (j = 0; j < NWARMUP; j++) {
      crypto_kem_enc_derand(ct, key_a, pk, enc_rand);
    }
    t0 = get_cyclecounter();
    for (j = 0; j < NITERERATIONS; j++) {
      crypto_kem_enc_derand(ct, key_a, pk, enc_rand);
    }
    t1 = get_cyclecounter();
    cycles_enc[i] = t1 - t0;

    // Decapsulation
    for (j = 0; j < NWARMUP; j++) {
      crypto_kem_dec(key_b, ct, sk);
    }
    t0 = get_cyclecounter();
    for (j = 0; j < NITERERATIONS; j++) {
      crypto_kem_dec(key_b, ct, sk);
    }
    t1 = get_cyclecounter();
    cycles_dec[i] = t1 - t0;


    if (memcmp(key_a, key_b, CRYPTO_BYTES)) {
      printf("ERROR keys\n");
      return 1;
    }
  }

  qsort(cycles_kg, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_enc, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_dec, NTESTS, sizeof(uint64_t), cmp_uint64_t);

  printf("keypair cycles=%" PRIu64 "\n",
         cycles_kg[NTESTS >> 1] / NITERERATIONS);
  printf("encaps cycles=%" PRIu64 "\n",
         cycles_enc[NTESTS >> 1] / NITERERATIONS);
  printf("decaps cycles=%" PRIu64 "\n",
         cycles_dec[NTESTS >> 1] / NITERERATIONS);

  return 0;
}

int main(void) {
  enable_cyclecounter();
  bench();
  disable_cyclecounter();

  printf("CRYPTO_SECRETKEYBYTES:  %d\n", CRYPTO_SECRETKEYBYTES);
  printf("CRYPTO_PUBLICKEYBYTES:  %d\n", CRYPTO_PUBLICKEYBYTES);
  printf("CRYPTO_CIPHERTEXTBYTES: %d\n", CRYPTO_CIPHERTEXTBYTES);

  return 0;
}
