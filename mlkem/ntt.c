// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#include "ntt.h"
#include <stdint.h>
#include "params.h"
#include "reduce.h"

#include "arith_native.h"
#include "debug/debug.h"
#include "ntt.h"

/* Code to generate zetas and zetas_inv used in the number-theoretic transform:

#define MLKEM_ROOT_OF_UNITY 17

static const uint8_t tree[128] = {
  0, 64, 32, 96, 16, 80, 48, 112, 8, 72, 40, 104, 24, 88, 56, 120,
  4, 68, 36, 100, 20, 84, 52, 116, 12, 76, 44, 108, 28, 92, 60, 124,
  2, 66, 34, 98, 18, 82, 50, 114, 10, 74, 42, 106, 26, 90, 58, 122,
  6, 70, 38, 102, 22, 86, 54, 118, 14, 78, 46, 110, 30, 94, 62, 126,
  1, 65, 33, 97, 17, 81, 49, 113, 9, 73, 41, 105, 25, 89, 57, 121,
  5, 69, 37, 101, 21, 85, 53, 117, 13, 77, 45, 109, 29, 93, 61, 125,
  3, 67, 35, 99, 19, 83, 51, 115, 11, 75, 43, 107, 27, 91, 59, 123,
  7, 71, 39, 103, 23, 87, 55, 119, 15, 79, 47, 111, 31, 95, 63, 127
};

void init_ntt() {
  unsigned int i;
  int16_t tmp[128];

  tmp[0] = MONT;
  for(i=1;i<128;i++)
    tmp[i] = fqmul(tmp[i-1],MONT*MLKEM_ROOT_OF_UNITY % MLKEM_Q);

  for(i=0;i<128;i++) {
    zetas[i] = tmp[tree[i]];
    if(zetas[i] > MLKEM_Q/2)
      zetas[i] -= MLKEM_Q;
    if(zetas[i] < -MLKEM_Q/2)
      zetas[i] += MLKEM_Q;
  }
}
*/

const int16_t zetas[128] = {
    -1044, -758,  -359,  -1517, 1493,  1422,  287,   202,  -171,  622,   1577,
    182,   962,   -1202, -1474, 1468,  573,   -1325, 264,  383,   -829,  1458,
    -1602, -130,  -681,  1017,  732,   608,   -1542, 411,  -205,  -1571, 1223,
    652,   -552,  1015,  -1293, 1491,  -282,  -1544, 516,  -8,    -320,  -666,
    -1618, -1162, 126,   1469,  -853,  -90,   -271,  830,  107,   -1421, -247,
    -951,  -398,  961,   -1508, -725,  448,   -1065, 677,  -1275, -1103, 430,
    555,   843,   -1251, 871,   1550,  105,   422,   587,  177,   -235,  -291,
    -460,  1574,  1653,  -246,  778,   1159,  -147,  -777, 1483,  -602,  1119,
    -1590, 644,   -872,  349,   418,   329,   -156,  -75,  817,   1097,  603,
    610,   1322,  -1285, -1465, 384,   -1215, -136,  1218, -1335, -874,  220,
    -1187, -1659, -1185, -1530, -1278, 794,   -1510, -854, -870,  478,   -108,
    -308,  996,   991,   958,   -1460, 1522,  1628};

#if !defined(MLKEM_USE_NATIVE_NTT)
// Computes a block CT butterflies with a fixed twiddle factor,
// using Montgomery multiplication.
//
// Parameters:
// - r: Pointer to base of polynomial (_not_ the base of butterfly block)
// - root: Twiddle factor to use for the butterfly. This must be in
//         Montgomery form and signed canonical.
// - start: Offset to the beginning of the butterfly block
// - len: Index difference between coefficients subject to a butterfly
// - bound: Ghost variable describing coefficient bound: Prior to `start`,
//          coefficients must be bound by `bound + MLKEM_Q`. Post `start`,
//          they must be bound by `bound`.
//
// When this function returns, output coefficients in the index range
// [start, start+2*len) have bound bumped to `bound + MLKEM_Q`.
//
// Example:
// - start=8, len=4
//   This would compute the following four butterflies
//
//          8     --    12
//             9    --     13
//                10   --     14
//                   11   --     15
//
// - start=4, len=2
//   This would compute the following two butterflies
//
//          4 -- 6
//             5 -- 7
//
STATIC_TESTABLE
void ntt_butterfly_block(int16_t r[MLKEM_N], int16_t zeta, int start, int len,
                         int bound)  // clang-format off
REQUIRES(0 <= start && start < MLKEM_N)
REQUIRES(1 <= len && len <= MLKEM_N / 2 && start + 2 * len <= MLKEM_N)
REQUIRES(0 <= bound && bound < INT16_MAX - MLKEM_Q)
REQUIRES(-HALF_Q < zeta && zeta < HALF_Q)
REQUIRES(IS_FRESH(r, sizeof(int16_t) * MLKEM_N))
REQUIRES(ARRAY_ABS_BOUND(r, 0, start - 1, bound + MLKEM_Q))
REQUIRES(ARRAY_ABS_BOUND(r, start, MLKEM_N - 1, bound))
ASSIGNS(OBJECT_UPTO(r, sizeof(int16_t) * MLKEM_N))
ENSURES(ARRAY_ABS_BOUND(r, 0, start + 2*len - 1, bound + MLKEM_Q))
ENSURES(ARRAY_ABS_BOUND(r, start + 2 * len, MLKEM_N - 1, bound))
// clang-format on
{
  // `bound` is a ghost variable only needed in the CBMC specification
  ((void)bound);
  for (int j = start; j < start + len; j++)  // clang-format off
    INVARIANT(start <= j && j <= start + len)
    // Coefficients are updated in strided pairs, so the bounds for the
    // intermediate states alternate twice between the old and new bound
    INVARIANT(ARRAY_ABS_BOUND(r, 0,           j - 1,           bound + MLKEM_Q))
    INVARIANT(ARRAY_ABS_BOUND(r, j,           start + len - 1, bound))
    INVARIANT(ARRAY_ABS_BOUND(r, start + len, j + len - 1,     bound + MLKEM_Q))
    INVARIANT(ARRAY_ABS_BOUND(r, j + len,     MLKEM_N - 1,     bound))
    // clang-format on
    {
      int16_t t;
      t = fqmul(r[j + len], zeta);
      r[j + len] = r[j] - t;
      r[j] = r[j] + t;
    }
}

// Compute one layer of forward NTT
//
// Parameters:
// - r: Pointer to base of polynomial
// - len: Stride of butterflies in this layer.
// - layer: Ghost variable indicating which layer is being applied.
//          Must match `len` via `len == MLKEM_N >> layer`.
//
// Note: `len` could be dropped and computed in the function, but
//   we are following the structure of the reference NTT from the
//   official Kyber implementation here, merely adding `layer` as
//   a ghost variable for the specifications.
STATIC_TESTABLE
void ntt_layer(int16_t r[MLKEM_N], int len, int layer)  // clang-format off
REQUIRES(IS_FRESH(r, sizeof(int16_t) * MLKEM_N))
REQUIRES(1 <= layer && layer <= 7 && len == (MLKEM_N >> layer))
REQUIRES(ARRAY_ABS_BOUND(r, 0, MLKEM_N - 1, layer * MLKEM_Q - 1))
ASSIGNS(OBJECT_UPTO(r, sizeof(int16_t) * MLKEM_N))
ENSURES(ARRAY_ABS_BOUND(r, 0, MLKEM_N - 1, (layer + 1) * MLKEM_Q - 1))
// clang-format on
{
  // `layer` is a ghost variable only needed in the CBMC specification
  ((void)layer);
  // Twiddle factors for layer n start at index 2^(layer-1)
  int k = MLKEM_N / (2 * len);
  for (int start = 0; start < MLKEM_N; start += 2 * len)  // clang-format off
    INVARIANT(0 <= start && start < MLKEM_N + 2 * len)
    INVARIANT(0 <= k && k <= MLKEM_N / 2 && 2 * len * k == start + MLKEM_N)
    INVARIANT(ARRAY_ABS_BOUND(r, 0, start - 1, (layer * MLKEM_Q - 1) + MLKEM_Q))
    INVARIANT(ARRAY_ABS_BOUND(r, start, MLKEM_N - 1, layer * MLKEM_Q - 1))
    // clang-format on
    {
      int16_t zeta = zetas[k++];
      ntt_butterfly_block(r, zeta, start, len, layer * MLKEM_Q - 1);
    }
}

// Compute full forward NTT
//
// NOTE: This particular implementation satisfies a much tighter
// bound on the output coefficients (5*q) than the contractual one (8*q),
// but this is not needed in the calling code. Should we change the
// base multiplication strategy to require smaller NTT output bounds,
// the proof may need strengthening.
//
// REF-CHANGE: Removed indirection poly_ntt -> ntt()
// and integrated polynomial reduction into the NTT.
void poly_ntt(poly *p) {
  POLY_BOUND_MSG(p, MLKEM_Q, "ref ntt input");
  int16_t *r = p->coeffs;

  for (int len = 128, layer = 1; len >= 2;
       len >>= 1, layer++)  // clang-format off
    INVARIANT(1 <= layer && layer <= 8 && len == (MLKEM_N >> layer))
    INVARIANT(ARRAY_ABS_BOUND(r, 0, MLKEM_N - 1, layer * MLKEM_Q - 1))
    // clang-format on
    {
      ntt_layer(r, len, layer);
    }

  // Check the stronger bound
  POLY_BOUND_MSG(p, NTT_BOUND, "ref ntt output");
}
#else  /* MLKEM_USE_NATIVE_NTT */

// Check that bound for native NTT implies contractual bound
STATIC_ASSERT(NTT_BOUND_NATIVE <= NTT_BOUND, invntt_bound)

void poly_ntt(poly *p) {
  POLY_BOUND_MSG(p, MLKEM_Q, "native ntt input");
  ntt_native(p);
  POLY_BOUND_MSG(p, NTT_BOUND_NATIVE, "native ntt output");
}
#endif /* MLKEM_USE_NATIVE_NTT */

#if !defined(MLKEM_USE_NATIVE_INTT)

// Check that bound for reference invNTT implies contractual bound
#define INVNTT_BOUND_REF (3 * MLKEM_Q / 4)
STATIC_ASSERT(INVNTT_BOUND_REF <= INVNTT_BOUND, invntt_bound)

// Compute one layer of inverse NTT
STATIC_TESTABLE
void invntt_layer(int16_t *r, int len, int layer)  // clang-format off
REQUIRES(IS_FRESH(r, sizeof(int16_t) * MLKEM_N))
REQUIRES(2 <= len && len <= 128 && 1 <= layer && layer <= 7)
REQUIRES(len == (1 << (8 - layer)))
REQUIRES(ARRAY_ABS_BOUND(r, 0, MLKEM_N - 1, MLKEM_Q))
ASSIGNS(OBJECT_UPTO(r, sizeof(int16_t) * MLKEM_N))
ENSURES(ARRAY_ABS_BOUND(r, 0, MLKEM_N - 1, MLKEM_Q))
// clang-format on
{
  // `layer` is a ghost variable used only in the specification
  ((void)layer);
  int k = MLKEM_N / len - 1;
  for (int start = 0; start < MLKEM_N; start += 2 * len)  // clang-format off
    INVARIANT(ARRAY_ABS_BOUND(r, 0, MLKEM_N - 1, MLKEM_Q))
    INVARIANT(0 <= start && start <= MLKEM_N && 0 <= k && k <= 127)
    // Normalised form of k == MLKEM_N / len - 1 - start / (2 * len)
    INVARIANT(2 * len * k + start == 2 * MLKEM_N - 2 * len)
    // clang-format on
    {
      int16_t zeta = zetas[k--];
      for (int j = start; j < start + len; j++)  // clang-format off
        INVARIANT(start <= j && j <= start + len)
        INVARIANT(0 <= start && start <= MLKEM_N && 0 <= k && k <= 127)
        INVARIANT(ARRAY_ABS_BOUND(r, 0, MLKEM_N - 1, MLKEM_Q))
        // clang-format on
        {
          int16_t t = r[j];
          r[j] = barrett_reduce(t + r[j + len]);
          r[j + len] = r[j + len] - t;
          r[j + len] = fqmul(r[j + len], zeta);
        }
    }
}

void poly_invntt_tomont(poly *p) {
  const int16_t f = 1441;  // mont^2/128
  int16_t *r = p->coeffs;

  // Scale input polynomial to account for Montgomery factor
  // and NTT twist. This also brings coefficients down to
  // absolute value < MLKEM_Q.

  for (int j = 0; j < MLKEM_N; j++)  // clang-format off
    INVARIANT(0 <= j && j <= MLKEM_N && ARRAY_ABS_BOUND(r, 0, j - 1, MLKEM_Q))
    // clang-format on
    {
      r[j] = fqmul(r[j], f);
    }

  // Run the invNTT layers
  for (int len = 2, layer = 7; len <= 128;
       len <<= 1, layer--)  // clang-format off
    INVARIANT(2 <= len && len <= 256 && 0 <= layer && layer <= 7 && len == (1 << (8 - layer)))
    INVARIANT(ARRAY_ABS_BOUND(r, 0, MLKEM_N - 1, MLKEM_Q))
    // clang-format on
    {
      invntt_layer(p->coeffs, len, layer);
    }

  POLY_BOUND_MSG(p, INVNTT_BOUND_REF, "ref intt output");
}
#else  /* MLKEM_USE_NATIVE_INTT */

// Check that bound for native invNTT implies contractual bound
STATIC_ASSERT(INVNTT_BOUND_NATIVE <= INVNTT_BOUND, invntt_bound)

void poly_invntt_tomont(poly *p) {
  intt_native(p);
  POLY_BOUND_MSG(p, INVNTT_BOUND_NATIVE, "native intt output");
}
#endif /* MLKEM_USE_NATIVE_INTT */

/*************************************************
 * Name:        basemul_cached
 *
 * Description: Multiplication of polynomials in Zq[X]/(X^2-zeta)
 *              used for multiplication of elements in Rq in NTT domain
 *
 *              Bounds:
 *              - a is assumed to be < q in absolute value.
 *              - Return value < 3/2 q in absolute value
 *
 * Arguments:   - int16_t r[2]: pointer to the output polynomial
 *              - const int16_t a[2]: pointer to the first factor
 *              - const int16_t b[2]: pointer to the second factor
 *              - int16_t b_cached: Cached precomputation of b[1] * zeta
 **************************************************/
void basemul_cached(int16_t r[2], const int16_t a[2], const int16_t b[2],
                    int16_t b_cached) {
  BOUND(a, 2, MLKEM_Q, "basemul input bound");

  int32_t t0, t1;

  t0 = (int32_t)a[1] * b_cached;
  t0 += (int32_t)a[0] * b[0];
  t1 = (int32_t)a[0] * b[1];
  t1 += (int32_t)a[1] * b[0];

  // |ti| < 2 * q * 2^15
  r[0] = montgomery_reduce(t0);
  r[1] = montgomery_reduce(t1);

  // |r[i]| < 3/2 q
  BOUND(r, 2, 3 * MLKEM_Q / 2, "basemul output bound");
}
