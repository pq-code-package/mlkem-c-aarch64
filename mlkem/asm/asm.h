// SPDX-License-Identifier: Apache-2.0
#ifndef MLKEM_ASM_H
#define MLKEM_ASM_H

#include <stdint.h>
#include "params.h"
#include "config.h"

#ifdef MLKEM_USE_AARCH64_ASM
void ntt_asm_clean(int16_t *);
void ntt_asm_opt(int16_t *);
void intt_asm_clean(int16_t *);
void intt_asm_opt(int16_t *);
#endif /* MLKEM_USE_AARCH64_ASM */

void poly_reduce_asm_clean(int16_t *);
void poly_reduce_asm_opt(int16_t *);

void poly_tomont_asm_clean(int16_t *);
void poly_tomont_asm_opt(int16_t *);

void poly_mulcache_compute_asm_clean(int16_t *, int16_t *, int16_t *, int16_t *);
void poly_mulcache_compute_asm_opt(int16_t *, int16_t *, int16_t *, int16_t *);

void poly_tobytes_asm_clean(uint8_t *r, const int16_t *a);

void polyvec_basemul_acc_montgomery_cached_asm_k2_clean(
    int16_t *r, const int16_t *a, const int16_t *b, const int16_t *b_cache);
void polyvec_basemul_acc_montgomery_cached_asm_k3_clean(
    int16_t *r, const int16_t *a, const int16_t *b, const int16_t *b_cache);
void polyvec_basemul_acc_montgomery_cached_asm_k4_clean(
    int16_t *r, const int16_t *a, const int16_t *b, const int16_t *b_cache);

void polyvec_basemul_acc_montgomery_cached_asm_k2_opt(
    int16_t *r, const int16_t *a, const int16_t *b, const int16_t *b_cache);
void polyvec_basemul_acc_montgomery_cached_asm_k3_opt(
    int16_t *r, const int16_t *a, const int16_t *b, const int16_t *b_cache);
void polyvec_basemul_acc_montgomery_cached_asm_k4_opt(
    int16_t *r, const int16_t *a, const int16_t *b, const int16_t *b_cache);

#define _polyvec_basemul_acc_montgomery_cached_asm_clean_name(k) \
    polyvec_basemul_acc_montgomery_cached_asm_k ## k ## _clean
#define polyvec_basemul_acc_montgomery_cached_asm_clean_name(k) \
    _polyvec_basemul_acc_montgomery_cached_asm_clean_name(k)

#define _polyvec_basemul_acc_montgomery_cached_asm_opt_name(k) \
    polyvec_basemul_acc_montgomery_cached_asm_k ## k ## _opt
#define polyvec_basemul_acc_montgomery_cached_asm_opt_name(k) \
    _polyvec_basemul_acc_montgomery_cached_asm_opt_name(k)

#if !defined(MLKEM_USE_NTT_ASM_FORCE)

#if defined(MLKEM_USE_NTT_ASM_CLEAN)
#define ntt_asm ntt_asm_clean
#define intt_asm intt_asm_clean
#define poly_reduce_asm poly_reduce_asm_clean
#define polyvec_basemul_acc_montgomery_cached_asm \
    polyvec_basemul_acc_montgomery_cached_asm_clean_name(KYBER_K)
#define poly_mulcache_compute_asm poly_mulcache_compute_asm_clean
#define poly_tomont_asm poly_tomont_asm_clean
#else /* MLKEM_USE_NTT_ASM_CLEAN */
#define ntt_asm ntt_asm_opt
#define intt_asm intt_asm_opt
#define poly_reduce_asm poly_reduce_asm_opt
#define polyvec_basemul_acc_montgomery_cached_asm \
    polyvec_basemul_acc_montgomery_cached_asm_opt_name(KYBER_K)
#define poly_mulcache_compute_asm poly_mulcache_compute_asm_opt
#define poly_tomont_asm poly_tomont_asm_opt
#endif /* !MLKEM_USE_NTT_ASM_CLEAN */

#define poly_tobytes_asm poly_tobytes_asm_clean

#endif /* !MLKEM_USE_NTT_ASM_FORCE */

#endif /* MLKEM_ASM_H */
