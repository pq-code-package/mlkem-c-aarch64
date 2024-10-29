// SPDX-License-Identifier: Apache-2.0
#ifndef NTT_H
#define NTT_H

#include <stdint.h>
#include "params.h"
#include "poly.h"

#include "arith_native.h"

#define zetas MLKEM_NAMESPACE(zetas)
extern const int16_t zetas[128];

#define poly_ntt MLKEM_NAMESPACE(poly_ntt)
void poly_ntt(poly *r);

#define poly_invntt_tomont MLKEM_NAMESPACE(poly_invntt_tomont)
void poly_invntt_tomont(poly *r);

// Absolute exclusive upper bound for the output of the inverse NTT
#define INVNTT_BOUND 8 * MLKEM_Q

// Absolute exclusive upper bound for the output of the forward NTT
#define NTT_BOUND 8 * MLKEM_Q

#define basemul_cached MLKEM_NAMESPACE(basemul_cached)
void basemul_cached(int16_t r[2], const int16_t a[2], const int16_t b[2],
                    int16_t b_cached);


#endif
