// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#include "ntt.h"
#include <stdint.h>
#include "params.h"
#include "reduce.h"

#include "arith_native.h"
#include "debug/debug.h"
#include "ntt.h"

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
void ntt_butterfly_block(int16_t r[MLKEM_N], int16_t zeta, int16_t zeta_twisted,
                         int start, int len, int bound)
__contract__(
  requires(0 <= start && start < MLKEM_N)
  requires(1 <= len && len <= MLKEM_N / 2 && start + 2 * len <= MLKEM_N)
  requires(0 <= bound && bound < INT16_MAX - MLKEM_Q)
  requires(-HALF_Q < zeta && zeta < HALF_Q)
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, start - 1, bound + MLKEM_Q))
  requires(array_abs_bound(r, start, MLKEM_N - 1, bound))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, start + 2*len - 1, bound + MLKEM_Q))
  ensures(array_abs_bound(r, start + 2 * len, MLKEM_N - 1, bound)))
{
  // `bound` is a ghost variable only needed in the CBMC specification
  ((void)bound);
  for (int j = start; j < start + len; j++)
  __loop__(
    invariant(start <= j && j <= start + len)
    // Coefficients are updated in strided pairs, so the bounds for the
    // intermediate states alternate twice between the old and new bound
    invariant(array_abs_bound(r, 0,           j - 1,           bound + MLKEM_Q))
    invariant(array_abs_bound(r, j,           start + len - 1, bound))
    invariant(array_abs_bound(r, start + len, j + len - 1,     bound + MLKEM_Q))
    invariant(array_abs_bound(r, j + len,     MLKEM_N - 1,     bound)))
  {
    int16_t t;
    t = fqmul_bar(r[j + len], zeta, zeta_twisted);
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
void ntt_layer(int16_t r[MLKEM_N], int len, int layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(1 <= layer && layer <= 7 && len == (MLKEM_N >> layer))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, layer * MLKEM_Q - 1))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, (layer + 1) * MLKEM_Q - 1)))
{
  // `layer` is a ghost variable only needed in the CBMC specification
  ((void)layer);
  // Twiddle factors for layer n start at index 2^(layer-1)
  int k = MLKEM_N / (2 * len);
  for (int start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(0 <= start && start < MLKEM_N + 2 * len)
    invariant(0 <= k && k <= MLKEM_N / 2 && 2 * len * k == start + MLKEM_N)
    invariant(array_abs_bound(r, 0, start - 1, (layer * MLKEM_Q - 1) + MLKEM_Q))
    invariant(array_abs_bound(r, start, MLKEM_N - 1, layer * MLKEM_Q - 1)))
  {
    int16_t zeta = zetas[k];
    uint16_t zeta_twisted = zetas_twisted[k++];
    ntt_butterfly_block(r, zeta, zeta_twisted, start, len, layer * MLKEM_Q - 1);
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
void poly_ntt(poly *p)
{
  POLY_BOUND_MSG(p, MLKEM_Q, "ref ntt input");
  int16_t *r = p->coeffs;

  for (int len = 128, layer = 1; len >= 2; len >>= 1, layer++)
  __loop__(
    invariant(1 <= layer && layer <= 8 && len == (MLKEM_N >> layer))
    invariant(array_abs_bound(r, 0, MLKEM_N - 1, layer * MLKEM_Q - 1)))
  {
    ntt_layer(r, len, layer);
  }

  // Check the stronger bound
  POLY_BOUND_MSG(p, NTT_BOUND, "ref ntt output");
}
#else  /* MLKEM_USE_NATIVE_NTT */

// Check that bound for native NTT implies contractual bound
STATIC_ASSERT(NTT_BOUND_NATIVE <= NTT_BOUND, invntt_bound)

void poly_ntt(poly *p)
{
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
void invntt_layer(int16_t *r, int len, int layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(2 <= len && len <= 128 && 1 <= layer && layer <= 7)
  requires(len == (1 << (8 - layer)))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, MLKEM_Q)))
{
  // `layer` is a ghost variable used only in the specification
  ((void)layer);
  int k = MLKEM_N / len - 1;
  for (int start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(array_abs_bound(r, 0, MLKEM_N - 1, MLKEM_Q))
    invariant(0 <= start && start <= MLKEM_N && 0 <= k && k <= 127)
    // Normalised form of k == MLKEM_N / len - 1 - start / (2 * len)
    invariant(2 * len * k + start == 2 * MLKEM_N - 2 * len))
  {
    int16_t zeta = zetas[k];
    uint16_t zeta_twisted = zetas_twisted[k--];
    for (int j = start; j < start + len; j++)
    __loop__(
      invariant(start <= j && j <= start + len)
      invariant(0 <= start && start <= MLKEM_N && 0 <= k && k <= 127)
      invariant(array_abs_bound(r, 0, MLKEM_N - 1, MLKEM_Q)))
    {
      int16_t t = r[j];
      r[j] = barrett_reduce(t + r[j + len]);
      r[j + len] = r[j + len] - t;
      r[j + len] = fqmul_bar(r[j + len], zeta, zeta_twisted);
    }
  }
}

void poly_invntt_tomont(poly *p)
{
  const int16_t f = 1441;  // mont^2/128
  int16_t *r = p->coeffs;

  // Scale input polynomial to account for Montgomery factor
  // and NTT twist. This also brings coefficients down to
  // absolute value < MLKEM_Q.

  for (int j = 0; j < MLKEM_N; j++)
  __loop__(
    invariant(0 <= j && j <= MLKEM_N)
    invariant(array_abs_bound(r, 0, j - 1, MLKEM_Q)))
  {
    r[j] = fqmul(r[j], f);
  }

  // Run the invNTT layers
  for (int len = 2, layer = 7; len <= 128; len <<= 1, layer--)
  __loop__(
    invariant(2 <= len && len <= 256 && 0 <= layer && layer <= 7 && len == (1 << (8 - layer)))
    invariant(array_abs_bound(r, 0, MLKEM_N - 1, MLKEM_Q)))
  {
    invntt_layer(p->coeffs, len, layer);
  }

  POLY_BOUND_MSG(p, INVNTT_BOUND_REF, "ref intt output");
}
#else  /* MLKEM_USE_NATIVE_INTT */

// Check that bound for native invNTT implies contractual bound
STATIC_ASSERT(INVNTT_BOUND_NATIVE <= INVNTT_BOUND, invntt_bound)

void poly_invntt_tomont(poly *p)
{
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
                    int16_t b_cached)
{
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
