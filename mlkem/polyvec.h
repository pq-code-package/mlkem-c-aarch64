// SPDX-License-Identifier: Apache-2.0
#ifndef POLYVEC_H
#define POLYVEC_H

#include <stdint.h>
#include "params.h"
#include "poly.h"

typedef struct {
  poly vec[MLKEM_K];
} ALIGN polyvec;

// REF-CHANGE: This struct does not exist in the reference implementation
typedef struct {
  poly_mulcache vec[MLKEM_K];
} polyvec_mulcache;

#define polyvec_compress MLKEM_NAMESPACE(polyvec_compress)
void polyvec_compress(uint8_t r[MLKEM_POLYVECCOMPRESSEDBYTES],
                      const polyvec *a);
#define polyvec_decompress MLKEM_NAMESPACE(polyvec_decompress)
void polyvec_decompress(polyvec *r,
                        const uint8_t a[MLKEM_POLYVECCOMPRESSEDBYTES]);

#define polyvec_tobytes MLKEM_NAMESPACE(polyvec_tobytes)
void polyvec_tobytes(uint8_t r[MLKEM_POLYVECBYTES], const polyvec *a);
#define polyvec_frombytes MLKEM_NAMESPACE(polyvec_frombytes)
void polyvec_frombytes(polyvec *r, const uint8_t a[MLKEM_POLYVECBYTES]);

#define polyvec_ntt MLKEM_NAMESPACE(polyvec_ntt)
void polyvec_ntt(polyvec *r);
#define polyvec_invntt_tomont MLKEM_NAMESPACE(polyvec_invntt_tomont)
void polyvec_invntt_tomont(polyvec *r);

#define polyvec_basemul_acc_montgomery \
  MLKEM_NAMESPACE(polyvec_basemul_acc_montgomery)
void polyvec_basemul_acc_montgomery(poly *r, const polyvec *a,
                                    const polyvec *b);

// REF-CHANGE: This function does not exist in the reference implementation
#define polyvec_basemul_acc_montgomery_cached \
  MLKEM_NAMESPACE(polyvec_basemul_acc_montgomery_cached)
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache);

// REF-CHANGE: This function does not exist in the reference implementation
#define polyvec_mulcache_compute MLKEM_NAMESPACE(polyvec_mulcache_compute)
void polyvec_mulcache_compute(polyvec_mulcache *x, const polyvec *a);

#define polyvec_reduce MLKEM_NAMESPACE(polyvec_reduce)
void polyvec_reduce(polyvec *r);

#define polyvec_add MLKEM_NAMESPACE(polyvec_add)
void polyvec_add(polyvec *r, const polyvec *a, const polyvec *b);

#endif
