// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "kem.h"
#include "randombytes.h"

#define USAGE \
  "acvp_mlkem{lvl} [encapDecap|keyGen] [AFT|VAL] {test specific arguments}"
#define ENCAPS_USAGE "acvp_mlkem{lvl} encapDecap AFT encaps ek=HEX m=HEX"
#define DECAPS_USAGE "acvp_mlkem{lvl} encapDecap VAL decaps dk=HEX c=HEX"
#define KEYGEN_USAGE "acvp_mlkem{lvl} keyGen AFT z=HEX d=HEX"

typedef enum
{
  encapDecap,
  keyGen
} acvp_mode;

typedef enum
{
  AFT,
  VAL
} acvp_type;

typedef enum
{
  encapsulation,
  decapsulation
} acvp_encapDecap_function;

/* Decode hex character [0-9A-Fa-f] into 0-15 */
static unsigned char decode_hex_char(char hex)
{
  if (hex >= '0' && hex <= '9')
  {
    return (unsigned char)(hex - '0');
  }
  else if (hex >= 'A' && hex <= 'F')
  {
    return 10 + (unsigned char)(hex - 'A');
  }
  else if (hex >= 'a' && hex <= 'f')
  {
    return 10 + (unsigned char)(hex - 'a');
  }
  else
  {
    return 0xFF;
  }
}

static int decode_hex(const char *prefix, unsigned char *out, size_t out_len,
                      const char *hex)
{
  size_t hex_len = strlen(hex);
  size_t prefix_len = strlen(prefix);

  // Check that hex starts with `prefix=`
  // Use memcmp, not strcmp
  if (hex_len < prefix_len + 1 || memcmp(prefix, hex, prefix_len) != 0 ||
      hex[prefix_len] != '=')
  {
    goto hex_usage;
  }

  hex += prefix_len + 1;
  hex_len -= prefix_len + 1;

  if (hex_len != 2 * out_len)
  {
    goto hex_usage;
  }

  for (size_t i = 0; i < out_len; i++, hex += 2, out++)
  {
    unsigned hex0 = decode_hex_char(hex[0]);
    unsigned hex1 = decode_hex_char(hex[1]);
    if (hex0 == 0xFF || hex1 == 0xFF)
    {
      goto hex_usage;
    }

    *out = (hex0 << 4) | hex1;
  }

  return 0;

hex_usage:
  fprintf(stderr,
          "Argument %s invalid: Expected argument of the form '%s=HEX' with "
          "HEX being a hex encoding of %u bytes\n",
          hex, prefix, (unsigned)out_len);
  return 1;
}

static void print_hex(const char *name, const unsigned char *raw, size_t len)
{
  if (name != NULL)
  {
    printf("%s=", name);
  }
  for (; len > 0; len--, raw++)
  {
    printf("%02X", *raw);
  }
  printf("\n");
}

static void acvp_mlkem_encapDecp_AFT_encapsulation(
    unsigned char const ek[MLKEM_INDCPA_PUBLICKEYBYTES],
    unsigned char const m[MLKEM_SYMBYTES])
{
  unsigned char ct[MLKEM_CIPHERTEXTBYTES];
  unsigned char ss[MLKEM_SSBYTES];

  crypto_kem_enc_derand(ct, ss, ek, m);

  print_hex("c", ct, sizeof(ct));
  print_hex("k", ss, sizeof(ss));
}

static void acvp_mlkem_encapDecp_VAL_decapsulation(
    unsigned char const dk[MLKEM_SECRETKEYBYTES],
    unsigned char const c[MLKEM_CIPHERTEXTBYTES])
{
  unsigned char ss[MLKEM_SSBYTES];

  crypto_kem_dec(ss, c, dk);

  print_hex("k", ss, sizeof(ss));
}

static void acvp_mlkem_keyGen_AFT(unsigned char const z[MLKEM_SYMBYTES],
                                  unsigned char const d[MLKEM_SYMBYTES])
{
  unsigned char ek[MLKEM_INDCPA_PUBLICKEYBYTES];
  unsigned char dk[MLKEM_SECRETKEYBYTES];

  unsigned char zd[2 * MLKEM_SYMBYTES];
  memcpy(zd, d, MLKEM_SYMBYTES);
  memcpy(zd + MLKEM_SYMBYTES, z, MLKEM_SYMBYTES);

  crypto_kem_keypair_derand(ek, dk, zd);

  print_hex("ek", ek, sizeof(ek));
  print_hex("dk", dk, sizeof(dk));
}

int main(int argc, char *argv[])
{
  if (argc == 0)
  {
    goto usage;
  }
  argc--, argv++;

  /* Parse mode: "encapDecap" or "keyGen" */
  if (argc == 0)
  {
    goto usage;
  }
  acvp_mode mode;

  if (strcmp(*argv, "encapDecap") == 0)
  {
    mode = encapDecap;
  }
  else if (strcmp(*argv, "keyGen") == 0)
  {
    mode = keyGen;
  }
  else
  {
    goto usage;
  }
  argc--, argv++;

  /* Parse test type: "AFT" (Algorithm Functional Test) or "VAL" (Validation) */
  if (argc == 0)
  {
    goto usage;
  }
  acvp_type type;

  if (strcmp(*argv, "AFT") == 0)
  {
    type = AFT;
  }
  else if (strcmp(*argv, "VAL") == 0)
  {
    type = VAL;
  }
  else
  {
    goto usage;
  }
  argc--, argv++;

  /* Case: encapDecap */
  switch (mode)
  {
    case encapDecap:
    {
      /* Parse function: "encapsulation" or "decapsulation" */
      if (argc == 0)
      {
        goto usage;
      }
      acvp_encapDecap_function encapDecap_function;

      if (strcmp(*argv, "encapsulation") == 0)
      {
        encapDecap_function = encapsulation;
      }
      else if (strcmp(*argv, "decapsulation") == 0)
      {
        encapDecap_function = decapsulation;
      }
      else
      {
        goto usage;
      }
      argc--, argv++;

      switch (encapDecap_function)
      {
        case encapsulation:
        {
          /* Encapsulation only for "AFT" */
          if (type != AFT)
          {
            goto encaps_usage;
          }

          /* Parse ek */
          unsigned char ek[MLKEM_INDCPA_PUBLICKEYBYTES];
          if (argc == 0 || decode_hex("ek", ek, sizeof(ek), *argv) != 0)
          {
            goto encaps_usage;
          }
          argc--, argv++;

          /* Parse m */
          unsigned char m[MLKEM_SYMBYTES];
          if (argc == 0 || decode_hex("m", m, sizeof(m), *argv) != 0)
          {
            goto encaps_usage;
          }
          argc--, argv++;

          /* Call function under test */
          acvp_mlkem_encapDecp_AFT_encapsulation(ek, m);
          break;
        }
        case decapsulation:
        {
          /* Decapsulation only for "VAL" */
          if (type != VAL)
          {
            goto decaps_usage;
          }

          /* Parse dk */
          unsigned char dk[MLKEM_SECRETKEYBYTES];
          if (argc == 0 || decode_hex("dk", dk, sizeof(dk), *argv) != 0)
          {
            goto decaps_usage;
          }
          argc--, argv++;

          /* Parse c */
          unsigned char c[MLKEM_CIPHERTEXTBYTES];
          if (argc == 0 || decode_hex("c", c, sizeof(c), *argv) != 0)
          {
            goto decaps_usage;
          }
          argc--, argv++;

          /* Call function under test */
          acvp_mlkem_encapDecp_VAL_decapsulation(dk, c);
          break;
        }
      }
      break;
    }
    case keyGen:
    {
      /* keyGen only for "AFT" */
      if (type != AFT)
      {
        goto keygen_usage;
      }

      /* Parse z */
      unsigned char z[MLKEM_SYMBYTES];
      if (argc == 0 || decode_hex("z", z, sizeof(z), *argv) != 0)
      {
        goto keygen_usage;
      }
      argc--, argv++;

      /* Parse d */
      unsigned char d[MLKEM_SYMBYTES];
      if (argc == 0 || decode_hex("d", d, sizeof(d), *argv) != 0)
      {
        goto keygen_usage;
      }
      argc--, argv++;

      /* Call function under test */
      acvp_mlkem_keyGen_AFT(z, d);
      break;
    }
  }

  ((void)type);

  return (0);

usage:
  fprintf(stderr, USAGE "\n");
  return (1);

encaps_usage:
  fprintf(stderr, ENCAPS_USAGE "\n");
  return (1);

decaps_usage:
  fprintf(stderr, DECAPS_USAGE "\n");
  return (1);

keygen_usage:
  fprintf(stderr, KEYGEN_USAGE "\n");
  return (1);
}
