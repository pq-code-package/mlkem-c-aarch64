/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "polyvec.h"
#include <stdint.h>
#include "arith_backend.h"
#include "config.h"
#include "ntt.h"
#include "poly.h"

#include "debug/debug.h"
void polyvec_compress_du(uint8_t r[MLKEM_POLYVECCOMPRESSEDBYTES_DU],
                         const polyvec *a)
{
  unsigned int i;
  POLYVEC_UBOUND(a, MLKEM_Q);

  for (i = 0; i < MLKEM_K; i++)
  {
    poly_compress_du(r + i * MLKEM_POLYCOMPRESSEDBYTES_DU, &a->vec[i]);
  }
}

void polyvec_decompress_du(polyvec *r,
                           const uint8_t a[MLKEM_POLYVECCOMPRESSEDBYTES_DU])
{
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_decompress_du(&r->vec[i], a + i * MLKEM_POLYCOMPRESSEDBYTES_DU);
  }

  POLYVEC_UBOUND(r, MLKEM_Q);
}

#if !defined(MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER)
STATIC_INLINE_TESTABLE
void poly_permute_bitrev_to_custom(poly *data)
__contract__(
  /* We don't specify that this should be a permutation, but only
   * that it does not change the bound established at the end of gen_matrix. */
  requires(memory_no_alias(data, sizeof(poly)))
  requires(array_bound(data->coeffs, 0, MLKEM_N - 1, 0, MLKEM_Q - 1))
  assigns(memory_slice(data, sizeof(poly)))
  ensures(array_bound(data->coeffs, 0, MLKEM_N - 1, 0, MLKEM_Q - 1))) { ((void)data); }
#endif /* MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER */

void polyvec_tobytes(uint8_t r[MLKEM_POLYVECBYTES], const polyvec *a)
{
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_permute_bitrev_to_custom((poly*)&a->vec[i]);
    poly_tobytes(r + i * MLKEM_POLYBYTES, &a->vec[i]);
  }
}

void polyvec_frombytes(polyvec *r, const uint8_t a[MLKEM_POLYVECBYTES])
{
  int i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_frombytes(&r->vec[i], a + i * MLKEM_POLYBYTES);
    poly_permute_bitrev_to_custom(&r->vec[i]);
  }
}

void polyvec_ntt(polyvec *r)
{
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_ntt(&r->vec[i]);
  }
}

void polyvec_invntt_tomont(polyvec *r)
{
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_invntt_tomont(&r->vec[i]);
  }
}

#if !defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache)
{
  int i;
  poly t;

  POLYVEC_BOUND(a, 4096);
  POLYVEC_BOUND(b, NTT_BOUND);
  POLYVEC_BOUND(b_cache, MLKEM_Q);

  poly_basemul_montgomery_cached(r, &a->vec[0], &b->vec[0], &b_cache->vec[0]);
  for (i = 1; i < MLKEM_K; i++)
  {
    poly_basemul_montgomery_cached(&t, &a->vec[i], &b->vec[i],
                                   &b_cache->vec[i]);
    poly_add(r, &t);
    /* abs bounds: < (i+1) * 3/2 * q */
  }

  /*
   * Those bounds are true for the C implementation, but not needed
   * in the higher level bounds reasoning. It is thus best to omit
   * them from the spec to not unnecessarily constraint native implementations.
   */
  cassert(
      array_abs_bound(r->coeffs, 0, MLKEM_N - 1, MLKEM_K * (2 * MLKEM_Q - 1)),
      "polyvec_basemul_acc_montgomery_cached output bounds");
  /* TODO: Integrate CBMC assertion into POLY_BOUND if CBMC is set */
  POLY_BOUND(r, MLKEM_K * 2 * MLKEM_Q);
}
#else  /* !MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache)
{
  POLYVEC_BOUND(a, 4096);
  POLYVEC_BOUND(b, NTT_BOUND);
  /* Omitting POLYVEC_BOUND(b_cache, MLKEM_Q) since native implementations may
   * decide not to use a mulcache. Note that the C backend implementation
   * of poly_basemul_montgomery_cached() does still include the check. */
  polyvec_basemul_acc_montgomery_cached_native(r, a, b, b_cache);
}
#endif /* MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */

void polyvec_basemul_acc_montgomery(poly *r, const polyvec *a, const polyvec *b)
{
  polyvec_mulcache b_cache;
  polyvec_mulcache_compute(&b_cache, b);
  polyvec_basemul_acc_montgomery_cached(r, a, b, &b_cache);
}

void polyvec_mulcache_compute(polyvec_mulcache *x, const polyvec *a)
{
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_mulcache_compute(&x->vec[i], &a->vec[i]);
  }
}

void polyvec_reduce(polyvec *r)
{
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_reduce(&r->vec[i]);
  }
}

void polyvec_add(polyvec *r, const polyvec *b)
{
  int i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_add(&r->vec[i], &b->vec[i]);
  }
}

void polyvec_tomont(polyvec *r)
{
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_tomont(&r->vec[i]);
  }
}
