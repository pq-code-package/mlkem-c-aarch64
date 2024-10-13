// SPDX-License-Identifier: Apache-2.0

#include "config.h"

#if defined(MLKEM_USE_NATIVE_X86_64) && defined(SYS_X86_64_AVX2)

#include "arith_native_x86_64.h"
#include "consts.h"
#include "poly.h"
#include "polyvec.h"

static void poly_basemul_montgomery_avx2(poly *r, const poly *a,
                                         const poly *b) {
  basemul_avx2((__m256i *)r->coeffs, (const __m256i *)a->coeffs,
               (const __m256i *)b->coeffs, qdata.vec);
}

void polyvec_basemul_acc_montgomery_cached_avx2(
    poly *r, const polyvec *a, const polyvec *b,
    const polyvec_mulcache *b_cache) {
  ((void)b_cache);  // cache unused

  // TODO! Think through bounds

  unsigned int i;
  poly t;

  poly_basemul_montgomery_avx2(r, &a->vec[0], &b->vec[0]);
  for (i = 1; i < KYBER_K; i++) {
    poly_basemul_montgomery_avx2(&t, &a->vec[i], &b->vec[i]);
    poly_add(r, r, &t);
  }
}

#else

// Dummy constant to keep compiler happy despite empty CU
int empty_cu_avx2_basemul;

#endif /* MLKEM_USE_NATIVE_X86_64 && SYS_X86_64_AVX2 */
