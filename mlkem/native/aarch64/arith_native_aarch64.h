// SPDX-License-Identifier: Apache-2.0
#ifndef MLKEM_AARCH64_NATIVE_H
#define MLKEM_AARCH64_NATIVE_H

#include <stdint.h>
#include "config.h"
#include "params.h"

#ifdef MLKEM_USE_NATIVE_AARCH64

void ntt_asm_clean(int16_t *);
void ntt_asm_opt(int16_t *);
void intt_asm_clean(int16_t *);
void intt_asm_opt(int16_t *);

unsigned int rej_uniform_asm_clean(int16_t *r, unsigned int len,
                                   const uint8_t *buf,
                                   unsigned int *buf_consumed,
                                   unsigned int buflen);

void poly_reduce_asm_clean(int16_t *);
void poly_reduce_asm_opt(int16_t *);

void poly_tomont_asm_clean(int16_t *);
void poly_tomont_asm_opt(int16_t *);

void poly_mulcache_compute_asm_clean(int16_t *, const int16_t *,
                                     const int16_t *, const int16_t *);
void poly_mulcache_compute_asm_opt(int16_t *, const int16_t *, const int16_t *,
                                   const int16_t *);

void poly_tobytes_asm_clean(uint8_t *r, const int16_t *a);

void polyvec_basemul_acc_montgomery_cached_asm_k2_clean(int16_t *r,
                                                        const int16_t *a,
                                                        const int16_t *b,
                                                        const int16_t *b_cache);
void polyvec_basemul_acc_montgomery_cached_asm_k3_clean(int16_t *r,
                                                        const int16_t *a,
                                                        const int16_t *b,
                                                        const int16_t *b_cache);
void polyvec_basemul_acc_montgomery_cached_asm_k4_clean(int16_t *r,
                                                        const int16_t *a,
                                                        const int16_t *b,
                                                        const int16_t *b_cache);

void polyvec_basemul_acc_montgomery_cached_asm_k2_opt(int16_t *r,
                                                      const int16_t *a,
                                                      const int16_t *b,
                                                      const int16_t *b_cache);
void polyvec_basemul_acc_montgomery_cached_asm_k3_opt(int16_t *r,
                                                      const int16_t *a,
                                                      const int16_t *b,
                                                      const int16_t *b_cache);
void polyvec_basemul_acc_montgomery_cached_asm_k4_opt(int16_t *r,
                                                      const int16_t *a,
                                                      const int16_t *b,
                                                      const int16_t *b_cache);

#define _polyvec_basemul_acc_montgomery_cached_asm_clean_name(k) \
  polyvec_basemul_acc_montgomery_cached_asm_k##k##_clean
#define polyvec_basemul_acc_montgomery_cached_asm_clean_name(k) \
  _polyvec_basemul_acc_montgomery_cached_asm_clean_name(k)

#define _polyvec_basemul_acc_montgomery_cached_asm_opt_name(k) \
  polyvec_basemul_acc_montgomery_cached_asm_k##k##_opt
#define polyvec_basemul_acc_montgomery_cached_asm_opt_name(k) \
  _polyvec_basemul_acc_montgomery_cached_asm_opt_name(k)

#endif /* MLKEM_USE_NATIVE_AARCH64 */
#endif /* MLKEM_AARCH64_NATIVE_H */
