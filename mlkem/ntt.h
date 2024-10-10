// SPDX-License-Identifier: Apache-2.0
#ifndef NTT_H
#define NTT_H

#include <stdint.h>
#include "params.h"
#include "poly.h"

#include "arith_native.h"

#define zetas KYBER_NAMESPACE(zetas)
extern const int16_t zetas[128];

#define ntt KYBER_NAMESPACE(ntt)
void poly_ntt(poly *r);

#define invntt KYBER_NAMESPACE(invntt)
void poly_invntt_tomont(poly *r);

#if !defined(MLKEM_USE_NATIVE_INTT)
#define INVNTT_BOUND (3 * KYBER_Q / 4)
#endif

#if !defined(MLKEM_USE_NATIVE_NTT)
#define NTT_BOUND 16546
#endif

#define basemul_cached KYBER_NAMESPACE(basemul_cached)
void basemul_cached(int16_t r[2], const int16_t a[2], const int16_t b[2],
                    int16_t b_cached);


#endif
