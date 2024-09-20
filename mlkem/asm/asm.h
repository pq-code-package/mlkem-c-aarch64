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

void polyvec_basemul_acc_montgomery_cached_asm_clean(int16_t *r, const int16_t *a, const int16_t *b,
        const int16_t *b_cache);

#if !defined(MLKEM_USE_NTT_ASM_FORCE)

#if defined(MLKEM_USE_NTT_ASM_CLEAN)
#define ntt_asm ntt_asm_clean
#define intt_asm intt_asm_clean
#define poly_reduce_asm poly_reduce_asm_clean
#else /* MLKEM_USE_NTT_ASM_CLEAN */
#define ntt_asm ntt_asm_opt
#define intt_asm intt_asm_opt
#define poly_reduce_asm poly_reduce_asm_opt
#endif /* !MLKEM_USE_NTT_ASM_CLEAN */

#define polyvec_basemul_acc_montgomery_cached_asm polyvec_basemul_acc_montgomery_cached_asm_clean
#endif /* !MLKEM_USE_NTT_ASM_FORCE */

#endif /* MLKEM_ASM_H */
