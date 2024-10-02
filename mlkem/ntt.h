// SPDX-License-Identifier: Apache-2.0
#ifndef NTT_H
#define NTT_H

#include <stdint.h>
#include "params.h"
#include "poly.h"

#define zetas KYBER_NAMESPACE(zetas)
extern const int16_t zetas[128];

#define ntt KYBER_NAMESPACE(ntt)
void poly_ntt(poly *r);

#define invntt KYBER_NAMESPACE(invntt)
void poly_invntt_tomont(poly *r);

#define basemul KYBER_NAMESPACE(basemul)
void basemul(int16_t r[2], const int16_t a[2], const int16_t b[2],
             int16_t zeta);

#define basemul_cached KYBER_NAMESPACE(basemul_cached)
void basemul_cached(int16_t r[2], const int16_t a[2], const int16_t b[2],
                    int16_t b_cached);

#endif
