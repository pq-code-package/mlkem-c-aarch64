/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include "config.h"

#if defined(MLKEM_USE_NATIVE_X86_64) && defined(SYS_X86_64_AVX2)

#include "arith_native_x86_64.h"
#include "consts.h"
#include "poly.h"
#include "polyvec.h"

static void poly_basemul_montgomery_avx2(poly *r, const poly *a, const poly *b)
{
  basemul_avx2((__m256i *)r->coeffs, (const __m256i *)a->coeffs,
               (const __m256i *)b->coeffs, qdata.vec);
}

/*
 * Implementation from Kyber reference repository
 * https://github.com/pq-crystals/kyber/blob/main/avx2
 */
static void poly_add_avx2(poly *r, const poly *a, const poly *b)
{
  unsigned int i;
  __m256i f0, f1;

  for (i = 0; i < MLKEM_N; i += 16)
  {
    f0 = _mm256_load_si256((const __m256i *)&a->coeffs[i]);
    f1 = _mm256_load_si256((const __m256i *)&b->coeffs[i]);
    f0 = _mm256_add_epi16(f0, f1);
    _mm256_store_si256((__m256i *)&r->coeffs[i], f0);
  }
}

void polyvec_basemul_acc_montgomery_cached_avx2(poly *r, const polyvec *a,
                                                const polyvec *b,
                                                const polyvec_mulcache *b_cache)
{
  ((void)b_cache); /* cache unused */

  /* TODO! Think through bounds */

  unsigned int i;
  poly t;

  poly_basemul_montgomery_avx2(r, &a->vec[0], &b->vec[0]);
  for (i = 1; i < MLKEM_K; i++)
  {
    poly_basemul_montgomery_avx2(&t, &a->vec[i], &b->vec[i]);
    poly_add_avx2(r, r, &t);
  }
}

#else

/* Dummy constant to keep compiler happy despite empty CU */
int empty_cu_avx2_basemul;

#endif /* MLKEM_USE_NATIVE_X86_64 && SYS_X86_64_AVX2 */
