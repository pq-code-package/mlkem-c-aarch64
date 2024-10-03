// SPDX-License-Identifier: Apache-2.0

// ML-KEM arithmetic native profile for clean assembly

#ifdef MLKEM_ARITH_NATIVE_PROFILE_H
#error Only one MLKEM_ARITH assembly profile can be defined -- did you include multiple profiles?
#else
#define MLKEM_ARITH_NATIVE_PROFILE_H

#include "../../arith_native.h"
#include "../arith_native_aarch64.h"

#define MLKEM_USE_NATIVE_NTT
#define MLKEM_USE_NATIVE_INTT
#define MLKEM_USE_NATIVE_POLY_REDUCE
#define MLKEM_USE_NATIVE_POLY_TOMONT
#define MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#define MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#define MLKEM_USE_NATIVE_POLY_TOBYTES
#define MLKEM_USE_NATIVE_REJ_UNIFORM

static inline void ntt_native(poly *data) { ntt_asm_opt(data->coeffs); }

static inline void intt_native(poly *data) { intt_asm_opt(data->coeffs); }

static inline void poly_reduce_native(poly *data) {
  poly_reduce_asm_opt(data->coeffs);
}
static inline void poly_tomont_native(poly *data) {
  poly_tomont_asm_opt(data->coeffs);
}

static inline void poly_mulcache_compute_native(poly_mulcache *x, const poly *y,
                                                const int16_t *z,
                                                const int16_t *r) {
  poly_mulcache_compute_asm_opt(x->coeffs, y->coeffs, z, r);
}
static inline void polyvec_basemul_acc_montgomery_cached_native(
    poly *r, const polyvec *a, const polyvec *b,
    const polyvec_mulcache *b_cache) {
  polyvec_basemul_acc_montgomery_cached_asm_opt_name(KYBER_K)(
      r->coeffs, a->vec[0].coeffs, b->vec[0].coeffs, b_cache->vec[0].coeffs);
}

static inline void poly_tobytes_native(uint8_t r[KYBER_POLYBYTES], const poly *a) {
  poly_tobytes_asm_clean(r, a->coeffs);
}

static inline unsigned int rej_uniform_native(int16_t *r, unsigned int len,
                                              const uint8_t *buf,
                                              unsigned int *buf_consumed,
                                              unsigned int buflen) {
  return rej_uniform_asm_clean(r, len, buf, buf_consumed, buflen);
}

#endif /* MLKEM_ARITH_NATIVE_PROFILE_H */
