/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef API_H
#define API_H

#include <stdint.h>

#define PQCP_MLKEM_NATIVE_MLKEM512_SECRETKEYBYTES 1632
#define PQCP_MLKEM_NATIVE_MLKEM512_PUBLICKEYBYTES 800
#define PQCP_MLKEM_NATIVE_MLKEM512_CIPHERTEXTBYTES 768
#define PQCP_MLKEM_NATIVE_MLKEM512_KEYPAIRCOINBYTES 64
#define PQCP_MLKEM_NATIVE_MLKEM512_ENCCOINBYTES 32
#define PQCP_MLKEM_NATIVE_MLKEM512_BYTES 32

int PQCP_MLKEM_NATIVE_MLKEM512_keypair_derand(uint8_t *pk, uint8_t *sk,
                                              const uint8_t *coins);
int PQCP_MLKEM_NATIVE_MLKEM512_keypair(uint8_t *pk, uint8_t *sk);
int PQCP_MLKEM_NATIVE_MLKEM512_enc_derand(uint8_t *ct, uint8_t *ss,
                                          const uint8_t *pk,
                                          const uint8_t *coins);
int PQCP_MLKEM_NATIVE_MLKEM512_enc(uint8_t *ct, uint8_t *ss, const uint8_t *pk);
int PQCP_MLKEM_NATIVE_MLKEM512_dec(uint8_t *ss, const uint8_t *ct,
                                   const uint8_t *sk);

#define PQCP_MLKEM_NATIVE_MLKEM768_SECRETKEYBYTES 2400
#define PQCP_MLKEM_NATIVE_MLKEM768_PUBLICKEYBYTES 1184
#define PQCP_MLKEM_NATIVE_MLKEM768_CIPHERTEXTBYTES 1088
#define PQCP_MLKEM_NATIVE_MLKEM768_KEYPAIRCOINBYTES 64
#define PQCP_MLKEM_NATIVE_MLKEM768_ENCCOINBYTES 32
#define PQCP_MLKEM_NATIVE_MLKEM768_BYTES 32

int PQCP_MLKEM_NATIVE_MLKEM768_keypair_derand(uint8_t *pk, uint8_t *sk,
                                              const uint8_t *coins);
int PQCP_MLKEM_NATIVE_MLKEM768_keypair(uint8_t *pk, uint8_t *sk);
int PQCP_MLKEM_NATIVE_MLKEM768_enc_derand(uint8_t *ct, uint8_t *ss,
                                          const uint8_t *pk,
                                          const uint8_t *coins);
int PQCP_MLKEM_NATIVE_MLKEM768_enc(uint8_t *ct, uint8_t *ss, const uint8_t *pk);
int PQCP_MLKEM_NATIVE_MLKEM768_dec(uint8_t *ss, const uint8_t *ct,
                                   const uint8_t *sk);

#define PQCP_MLKEM_NATIVE_MLKEM1024_SECRETKEYBYTES 3168
#define PQCP_MLKEM_NATIVE_MLKEM1024_PUBLICKEYBYTES 1568
#define PQCP_MLKEM_NATIVE_MLKEM1024_CIPHERTEXTBYTES 1568
#define PQCP_MLKEM_NATIVE_MLKEM1024_KEYPAIRCOINBYTES 64
#define PQCP_MLKEM_NATIVE_MLKEM1024_ENCCOINBYTES 32
#define PQCP_MLKEM_NATIVE_MLKEM1024_BYTES 32

int PQCP_MLKEM_NATIVE_MLKEM1024_keypair_derand(uint8_t *pk, uint8_t *sk,
                                               const uint8_t *coins);
int PQCP_MLKEM_NATIVE_MLKEM1024_keypair(uint8_t *pk, uint8_t *sk);
int PQCP_MLKEM_NATIVE_MLKEM1024_enc_derand(uint8_t *ct, uint8_t *ss,
                                           const uint8_t *pk,
                                           const uint8_t *coins);
int PQCP_MLKEM_NATIVE_MLKEM1024_enc(uint8_t *ct, uint8_t *ss,
                                    const uint8_t *pk);
int PQCP_MLKEM_NATIVE_MLKEM1024_dec(uint8_t *ss, const uint8_t *ct,
                                    const uint8_t *sk);

#endif
