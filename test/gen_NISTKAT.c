// SPDX-License-Identifier: Apache-2.0

#include <stdio.h>
#include <string.h>

#include "kem.h"
#include "randombytes.h"

static void fprintBstr(FILE *fp, const char *S, const uint8_t *A, size_t L) {
  size_t i;
  fprintf(fp, "%s", S);
  for (i = 0; i < L; i++) {
    fprintf(fp, "%02X", A[i]);
  }
  if (L == 0) {
    fprintf(fp, "00");
  }
  fprintf(fp, "\n");
}

static void randombytes_nth(uint8_t *seed, size_t nth, size_t len) {
  uint8_t entropy_input[48] = {0,  1,  2,  3,  4,  5,  6,  7,  8,  9,  10, 11,
                               12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                               24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
                               36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47};
  nist_kat_init(entropy_input, NULL, 256);

  for (size_t i = 0; i < nth + 1; i++) {
    randombytes(seed, len);
  }
}

int main(void) {
  uint8_t seed[48] ALIGN;
  FILE *fh = stdout;
  uint8_t public_key[CRYPTO_PUBLICKEYBYTES] ALIGN;
  uint8_t secret_key[CRYPTO_SECRETKEYBYTES] ALIGN;
  uint8_t ciphertext[CRYPTO_CIPHERTEXTBYTES] ALIGN;
  uint8_t shared_secret_e[CRYPTO_BYTES] ALIGN;
  uint8_t shared_secret_d[CRYPTO_BYTES] ALIGN;
  int rc;

  int count = 0;

  fprintf(fh, "# %s\n\n", CRYPTO_ALGNAME);

  do {
    fprintf(fh, "count = %d\n", count);
    randombytes_nth(seed, count, 48);
    fprintBstr(fh, "seed = ", seed, 48);

    nist_kat_init(seed, NULL, 256);

    rc = crypto_kem_keypair(public_key, secret_key);
    if (rc != 0) {
      fprintf(stderr, "[kat_kem] %s ERROR: crypto_kem_keypair failed!\n",
              CRYPTO_ALGNAME);
      return -1;
    }
    fprintBstr(fh, "pk = ", public_key, CRYPTO_PUBLICKEYBYTES);
    fprintBstr(fh, "sk = ", secret_key, CRYPTO_SECRETKEYBYTES);

    rc = crypto_kem_enc(ciphertext, shared_secret_e, public_key);
    if (rc != 0) {
      fprintf(stderr, "[kat_kem] %s ERROR: crypto_kem_enc failed!\n",
              CRYPTO_ALGNAME);
      return -2;
    }
    fprintBstr(fh, "ct = ", ciphertext, CRYPTO_CIPHERTEXTBYTES);
    fprintBstr(fh, "ss = ", shared_secret_e, CRYPTO_BYTES);
    fprintf(fh, "\n");

    rc = crypto_kem_dec(shared_secret_d, ciphertext, secret_key);
    if (rc != 0) {
      fprintf(stderr, "[kat_kem] %s ERROR: crypto_kem_dec failed!\n",
              CRYPTO_ALGNAME);
      return -3;
    }

    rc = memcmp(shared_secret_e, shared_secret_d, CRYPTO_BYTES);
    if (rc != 0) {
      fprintf(stderr, "[kat_kem] %s ERROR: shared secrets are not equal\n",
              CRYPTO_ALGNAME);
      return -4;
    }
    count++;
  } while (count < 100);

  return 0;
}
