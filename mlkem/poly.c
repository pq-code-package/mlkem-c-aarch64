// SPDX-License-Identifier: Apache-2.0
#include "poly.h"
#include <stdint.h>
#include <string.h>
#include "cbd.h"
#include "cbmc.h"
#include "fips202x4.h"
#include "ntt.h"
#include "params.h"
#include "reduce.h"
#include "symmetric.h"
#include "verify.h"

#include "arith_native.h"
#include "debug/debug.h"

/*************************************************
 * Name:        poly_compress
 *
 * Description: Compression and subsequent serialization of a polynomial
 *
 * Arguments:   - uint8_t *r: pointer to output byte array
 *                            (of length KYBER_POLYCOMPRESSEDBYTES)
 *              - const poly *a: pointer to input polynomial
 *                  Coefficients must be unsigned canonical,
 *                  i.e. in [0,1,..,KYBER_Q-1].
 **************************************************/
void poly_compress(uint8_t r[KYBER_POLYCOMPRESSEDBYTES], const poly *a) {
  POLY_UBOUND(a, KYBER_Q);
  uint8_t t[8] = {0};

  const int num_blocks = KYBER_N / 8;

#if (KYBER_POLYCOMPRESSEDBYTES == 128)
  for (int i = 0; i < num_blocks; i++)
      // clang-format off
        ASSIGNS(i, OBJECT_WHOLE(t), OBJECT_WHOLE(r))
        INVARIANT(i >= 0 && i <= num_blocks)
        DECREASES(num_blocks - i)
    // clang-format on
    {
      for (int j = 0; j < 8; j++)
          // clang-format off
            ASSIGNS(j, OBJECT_WHOLE(t))
            INVARIANT(i >= 0 && i <= num_blocks)
            INVARIANT(j >= 0 && j <= 8)
            INVARIANT(ARRAY_IN_BOUNDS(int, k2, 0, (j-1), t, 0, 15))
            DECREASES(8 - j)
        // clang-format on
        {
          // map to positive standard representatives
          // REF-CHANGE: Precondition change, we assume unsigned canonical data
          t[j] = scalar_compress_q_16(a->coeffs[8 * i + j]);
        }

      // REF-CHANGE: Use array indexing into
      // r rather than pointer-arithmetic to simplify verification
      r[i * 4] = t[0] | (t[1] << 4);
      r[i * 4 + 1] = t[2] | (t[3] << 4);
      r[i * 4 + 2] = t[4] | (t[5] << 4);
      r[i * 4 + 3] = t[6] | (t[7] << 4);
    }
#elif (KYBER_POLYCOMPRESSEDBYTES == 160)
  for (int i = 0; i < num_blocks; i++)
      // clang-format off
        ASSIGNS(i, OBJECT_WHOLE(t), OBJECT_WHOLE(r))
        INVARIANT(i >= 0 && i <= num_blocks)
        DECREASES(num_blocks - i)
    // clang-format on
    {
      for (int j = 0; j < 8; j++)
          // clang-format off
            ASSIGNS(j, OBJECT_WHOLE(t))
            INVARIANT(i >= 0)
            INVARIANT(i <= num_blocks)
            INVARIANT(j >= 0 && j <= 8)
            INVARIANT(ARRAY_IN_BOUNDS(int, k2, 0, (j-1), t, 0, 31))
            DECREASES(8 - j)
        // clang-format on
        {
          // map to positive standard representatives
          // REF-CHANGE: Precondition change, we assume unsigned canonical data
          t[j] = scalar_compress_q_32(a->coeffs[8 * i + j]);
        }

      // REF-CHANGE: Explicitly truncate to avoid warning about
      // implicit truncation in CBMC, and use array indexing into
      // r rather than pointer-arithmetic to simplify verification
      r[i * 5] = 0xFF & ((t[0] >> 0) | (t[1] << 5));
      r[i * 5 + 1] = 0xFF & ((t[1] >> 3) | (t[2] << 2) | (t[3] << 7));
      r[i * 5 + 2] = 0xFF & ((t[3] >> 1) | (t[4] << 4));
      r[i * 5 + 3] = 0xFF & ((t[4] >> 4) | (t[5] << 1) | (t[6] << 6));
      r[i * 5 + 4] = 0xFF & ((t[6] >> 2) | (t[7] << 3));
    }
#else
#error "KYBER_POLYCOMPRESSEDBYTES needs to be in {128, 160}"
#endif
}

/*************************************************
 * Name:        poly_decompress
 *
 * Description: De-serialization and subsequent decompression of a polynomial;
 *              approximate inverse of poly_compress
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length KYBER_POLYCOMPRESSEDBYTES bytes)
 *
 * Upon return, the coefficients of the output polynomial are unsigned-canonical
 * (non-negative and smaller than KYBER_Q).
 *
 **************************************************/
void poly_decompress(poly *r, const uint8_t a[KYBER_POLYCOMPRESSEDBYTES]) {
#if (KYBER_POLYCOMPRESSEDBYTES == 128)
  for (int i = 0; i < KYBER_N / 2; i++)
      // clang-format off
        ASSIGNS(i, OBJECT_WHOLE(r))
        INVARIANT(i >= 0)
        INVARIANT(i <= KYBER_N / 2)
        INVARIANT(ARRAY_IN_BOUNDS(int, k, 0, (2 * i - 1), r->coeffs, 0, (KYBER_Q - 1)))
        DECREASES(KYBER_N / 2 - i)
    // clang-format on
    {
      // REF-CHANGE: Hoist scalar decompression into separate function
      r->coeffs[2 * i + 0] = scalar_decompress_q_16((a[i] >> 0) & 0xF);
      r->coeffs[2 * i + 1] = scalar_decompress_q_16((a[i] >> 4) & 0xF);
    }



#elif (KYBER_POLYCOMPRESSEDBYTES == 160)
  const int num_blocks = KYBER_N / 8;
  for (int i = 0; i < num_blocks; i++)
      // clang-format off
        ASSIGNS(i, OBJECT_WHOLE(r))
        INVARIANT(i >= 0)
        INVARIANT(i <= num_blocks)
        INVARIANT(num_blocks == 32)
        INVARIANT(ARRAY_IN_BOUNDS(int, k, 0, (8 * i - 1), r->coeffs, 0, (KYBER_Q - 1)))
        DECREASES(num_blocks - i)
    // clang-format on
    {
      uint8_t t[8];
      const int offset = i * 5;
      // REF-CHANGE: Explicitly truncate to avoid warning about
      // implicit truncation in CBMC and unwind loop for ease
      // of proof.

      // Decompress 5 8-bit bytes (so 40 bits) into
      // 8 5-bit values stored in t[]
      t[0] = 0x1F & (a[offset + 0] >> 0);
      t[1] = 0x1F & ((a[offset + 0] >> 5) | (a[offset + 1] << 3));
      t[2] = 0x1F & (a[offset + 1] >> 2);
      t[3] = 0x1F & ((a[offset + 1] >> 7) | (a[offset + 2] << 1));
      t[4] = 0x1F & ((a[offset + 2] >> 4) | (a[offset + 3] << 4));
      t[5] = 0x1F & (a[offset + 3] >> 1);
      t[6] = 0x1F & ((a[offset + 3] >> 6) | (a[offset + 4] << 2));
      t[7] = 0x1F & (a[offset + 4] >> 3);

      // and copy to the correct slice in r[]
      for (int j = 0; j < 8; j++)
          // clang-format off
            ASSIGNS(j, OBJECT_WHOLE(r))
            INVARIANT(j >= 0)
            INVARIANT(j <= 8)
            INVARIANT(i >= 0)
            INVARIANT(i <= num_blocks)
            INVARIANT(ARRAY_IN_BOUNDS(int, k, 0, (8 * i + j - 1), r->coeffs, 0, (KYBER_Q - 1)))
            DECREASES(8 - j)
        // clang-format on
        {
          // REF-CHANGE: Hoist scalar decompression into separate function
          r->coeffs[8 * i + j] = scalar_decompress_q_32(t[j]);
        }
    }
#else
#error "KYBER_POLYCOMPRESSEDBYTES needs to be in {128, 160}"
#endif

  POLY_UBOUND(r, KYBER_Q);
}

/*************************************************
 * Name:        poly_tobytes
 *
 * Description: Serialization of a polynomial.
 *              Signed coefficients are converted to
 *              unsigned form before serialization.
 *
 * Arguments:   INPUT:
 *              - a: const pointer to input polynomial,
 *                with each coefficient in the range [0,1,..,Q-1]
 *              OUTPUT
 *              - r: pointer to output byte array
 *                   (of KYBER_POLYBYTES bytes)
 **************************************************/
#if !defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
void poly_tobytes(uint8_t r[KYBER_POLYBYTES], const poly *a) {
  POLY_UBOUND(a, KYBER_Q);

  for (unsigned int i = 0; i < KYBER_N / 2; i++)
      // clang-format off
  ASSIGNS(i, OBJECT_WHOLE(r))
  INVARIANT(i >= 0 && i <= KYBER_N / 2)
  DECREASES(KYBER_N / 2 - i)
    // clang-format on
    {
      const uint16_t t0 = a->coeffs[2 * i];
      const uint16_t t1 = a->coeffs[2 * i + 1];
      // REF-CHANGE: Precondition change, we assume unsigned canonical data

      // t0 and t1 are both < KYBER_Q, so contain at most 12 bits each of
      // significant data, so these can be packed into 24 bits or exactly
      // 3 bytes, as follows.

      // Least significant bits 0 - 7 of t0.
      r[3 * i + 0] = t0 & 0xFF;

      // Most significant bits 8 - 11 of t0 become the least significant
      // nibble of the second byte. The least significant 4 bits
      // of t1 become the upper nibble of the second byte.
      r[3 * i + 1] = (t0 >> 8) | ((t1 << 4) & 0xF0);

      // Bits 4 - 11 of t1 become the third byte.
      r[3 * i + 2] = t1 >> 4;
    }
}
#else  /* MLKEM_USE_NATIVE_POLY_TOBYTES */
void poly_tobytes(uint8_t r[KYBER_POLYBYTES], const poly *a) {
  POLY_UBOUND(a, KYBER_Q);
  poly_tobytes_native(r, a);
}
#endif /* MLKEM_USE_NATIVE_POLY_TOBYTES */

#if !defined(MLKEM_USE_NATIVE_POLY_FROMBYTES)
/*************************************************
 * Name:        poly_frombytes
 *
 * Description: De-serialization of a polynomial.
 *
 *              Note that this is not a strict inverse to poly_tobytes() since
 *              the latter includes normalization to unsigned coefficients.
 *
 * Arguments:   INPUT
 *              - a: pointer to input byte array
 *                   (of KYBER_POLYBYTES bytes)
 *              OUTPUT
 *              - r: pointer to output polynomial, with
 *                   each coefficient unsigned and in the range
 *                   0 .. 4095
 **************************************************/
void poly_frombytes(poly *r, const uint8_t a[KYBER_POLYBYTES]) {
  unsigned int i;
  for (i = 0; i < KYBER_N / 2; i++) {
    r->coeffs[2 * i] =
        ((a[3 * i + 0] >> 0) | ((uint16_t)a[3 * i + 1] << 8)) & 0xFFF;
    r->coeffs[2 * i + 1] =
        ((a[3 * i + 1] >> 4) | ((uint16_t)a[3 * i + 2] << 4)) & 0xFFF;
  }
}
#else  /* MLKEM_USE_NATIVE_POLY_FROMBYTES */
void poly_frombytes(poly *r, const uint8_t a[KYBER_POLYBYTES]) {
  poly_frombytes_native(r, a);
}
#endif /* MLKEM_USE_NATIVE_POLY_FROMBYTES */

/*************************************************
 * Name:        poly_frommsg
 *
 * Description: Convert 32-byte message to polynomial
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *msg: pointer to input message
 **************************************************/
void poly_frommsg(poly *r, const uint8_t msg[KYBER_INDCPA_MSGBYTES]) {
  unsigned int i, j;

#if (KYBER_INDCPA_MSGBYTES != KYBER_N / 8)
#error "KYBER_INDCPA_MSGBYTES must be equal to KYBER_N/8 bytes!"
#endif

  for (i = 0; i < KYBER_N / 8; i++) {
    for (j = 0; j < 8; j++) {
      r->coeffs[8 * i + j] = 0;
      cmov_int16(r->coeffs + 8 * i + j, ((KYBER_Q + 1) / 2), (msg[i] >> j) & 1);
    }
  }

  POLY_BOUND_MSG(r, KYBER_Q, "poly_frommsg output");
}

/*************************************************
 * Name:        poly_tomsg
 *
 * Description: Convert polynomial to 32-byte message
 *
 * Arguments:   - uint8_t *msg: pointer to output message
 *              - const poly *a: pointer to input polynomial
 *                  Coefficients must be unsigned canonical
 **************************************************/
void poly_tomsg(uint8_t msg[KYBER_INDCPA_MSGBYTES], const poly *a) {
  POLY_UBOUND(a, KYBER_Q);

  unsigned int i, j;
  uint32_t t;

  for (i = 0; i < KYBER_N / 8; i++) {
    msg[i] = 0;
    for (j = 0; j < 8; j++) {
      t = (uint32_t)a->coeffs[8 * i + j];
      // t += ((int16_t)t >> 15) & KYBER_Q;
      // t  = (((t << 1) + KYBER_Q/2)/KYBER_Q) & 1;
      t <<= 1;
      t += 1665;
      t *= 80635;
      t >>= 28;
      t &= 1;
      msg[i] |= t << j;
    }
  }
}

/*************************************************
 * Name:        poly_getnoise_eta1_4x
 *
 * Description: Batch sample four polynomials deterministically from a seed and
 *nonces, with output polynomials close to centered binomial distribution with
 *parameter KYBER_ETA1
 *
 * Arguments:   - poly *r{0,1,2,3}: pointer to output polynomial
 *              - const uint8_t *seed: pointer to input seed
 *                                     (of length KYBER_SYMBYTES bytes)
 *              - uint8_t nonce{0,1,2,3}: one-byte input nonce
 **************************************************/
void poly_getnoise_eta1_4x(poly *r0, poly *r1, poly *r2, poly *r3,
                           const uint8_t seed[KYBER_SYMBYTES], uint8_t nonce0,
                           uint8_t nonce1, uint8_t nonce2, uint8_t nonce3) {
  uint8_t buf[KECCAK_WAY][KYBER_ETA1 * KYBER_N / 4] ALIGN;
  uint8_t extkey[KECCAK_WAY][KYBER_SYMBYTES + 1] ALIGN;
  memcpy(extkey[0], seed, KYBER_SYMBYTES);
  memcpy(extkey[1], seed, KYBER_SYMBYTES);
  memcpy(extkey[2], seed, KYBER_SYMBYTES);
  memcpy(extkey[3], seed, KYBER_SYMBYTES);
  extkey[0][KYBER_SYMBYTES] = nonce0;
  extkey[1][KYBER_SYMBYTES] = nonce1;
  extkey[2][KYBER_SYMBYTES] = nonce2;
  extkey[3][KYBER_SYMBYTES] = nonce3;
  shake256x4(buf[0], buf[1], buf[2], buf[3], KYBER_ETA1 * KYBER_N / 4,
             extkey[0], extkey[1], extkey[2], extkey[3], KYBER_SYMBYTES + 1);
  poly_cbd_eta1(r0, buf[0]);
  poly_cbd_eta1(r1, buf[1]);
  poly_cbd_eta1(r2, buf[2]);
  poly_cbd_eta1(r3, buf[3]);

  POLY_BOUND_MSG(r0, KYBER_ETA1 + 1, "poly_getnoise_eta1_4x output 0");
  POLY_BOUND_MSG(r1, KYBER_ETA1 + 1, "poly_getnoise_eta1_4x output 1");
  POLY_BOUND_MSG(r2, KYBER_ETA1 + 1, "poly_getnoise_eta1_4x output 2");
  POLY_BOUND_MSG(r3, KYBER_ETA1 + 1, "poly_getnoise_eta1_4x output 3");
}

/*************************************************
 * Name:        poly_getnoise_eta2
 *
 * Description: Sample a polynomial deterministically from a seed and a nonce,
 *              with output polynomial close to centered binomial distribution
 *              with parameter KYBER_ETA2
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *seed: pointer to input seed
 *                                     (of length KYBER_SYMBYTES bytes)
 *              - uint8_t nonce: one-byte input nonce
 **************************************************/
void poly_getnoise_eta2(poly *r, const uint8_t seed[KYBER_SYMBYTES],
                        uint8_t nonce) {
  uint8_t buf[KYBER_ETA2 * KYBER_N / 4] ALIGN;
  prf(buf, sizeof(buf), seed, nonce);
  poly_cbd_eta2(r, buf);

  POLY_BOUND_MSG(r, KYBER_ETA1 + 1, "poly_getnoise_eta2 output");
}

/*************************************************
 * Name:        poly_getnoise_eta2_4x
 *
 * Description: Batch sample four polynomials deterministically from a seed and
 *nonces, with output polynomials close to centered binomial distribution with
 *parameter KYBER_ETA2
 *
 * Arguments:   - poly *r{0,1,2,3}: pointer to output polynomial
 *              - const uint8_t *seed: pointer to input seed
 *                                     (of length KYBER_SYMBYTES bytes)
 *              - uint8_t nonce{0,1,2,3}: one-byte input nonce
 **************************************************/
void poly_getnoise_eta2_4x(poly *r0, poly *r1, poly *r2, poly *r3,
                           const uint8_t seed[KYBER_SYMBYTES], uint8_t nonce0,
                           uint8_t nonce1, uint8_t nonce2, uint8_t nonce3) {
  uint8_t buf[KECCAK_WAY][KYBER_ETA2 * KYBER_N / 4] ALIGN;
  uint8_t extkey[KECCAK_WAY][KYBER_SYMBYTES + 1] ALIGN;
  memcpy(extkey[0], seed, KYBER_SYMBYTES);
  memcpy(extkey[1], seed, KYBER_SYMBYTES);
  memcpy(extkey[2], seed, KYBER_SYMBYTES);
  memcpy(extkey[3], seed, KYBER_SYMBYTES);
  extkey[0][KYBER_SYMBYTES] = nonce0;
  extkey[1][KYBER_SYMBYTES] = nonce1;
  extkey[2][KYBER_SYMBYTES] = nonce2;
  extkey[3][KYBER_SYMBYTES] = nonce3;
  shake256x4(buf[0], buf[1], buf[2], buf[3], KYBER_ETA2 * KYBER_N / 4,
             extkey[0], extkey[1], extkey[2], extkey[3], KYBER_SYMBYTES + 1);
  poly_cbd_eta2(r0, buf[0]);
  poly_cbd_eta2(r1, buf[1]);
  poly_cbd_eta2(r2, buf[2]);
  poly_cbd_eta2(r3, buf[3]);

  POLY_BOUND_MSG(r0, KYBER_ETA2 + 1, "poly_getnoise_eta2_4x output 0");
  POLY_BOUND_MSG(r1, KYBER_ETA2 + 1, "poly_getnoise_eta2_4x output 1");
  POLY_BOUND_MSG(r2, KYBER_ETA2 + 1, "poly_getnoise_eta2_4x output 2");
  POLY_BOUND_MSG(r3, KYBER_ETA2 + 1, "poly_getnoise_eta2_4x output 3");
}

/*************************************************
 * Name:        poly_getnoise_eta1122_4x
 *
 * Description: Batch sample four polynomials deterministically from a seed and
 *a nonces, with output polynomials close to centered binomial distribution with
 *parameter KYBER_ETA1 and KYBER_ETA2
 *
 * Arguments:   - poly *r{0,1,2,3}: pointer to output polynomial
 *              - const uint8_t *seed: pointer to input seed
 *                                     (of length KYBER_SYMBYTES bytes)
 *              - uint8_t nonce{0,1,2,3}: one-byte input nonce
 **************************************************/
void poly_getnoise_eta1122_4x(poly *r0, poly *r1, poly *r2, poly *r3,
                              const uint8_t seed[KYBER_SYMBYTES],
                              uint8_t nonce0, uint8_t nonce1, uint8_t nonce2,
                              uint8_t nonce3) {
  uint8_t buf1[KECCAK_WAY / 2][KYBER_ETA1 * KYBER_N / 4] ALIGN;
  uint8_t buf2[KECCAK_WAY / 2][KYBER_ETA2 * KYBER_N / 4] ALIGN;
  uint8_t extkey[KECCAK_WAY][KYBER_SYMBYTES + 1] ALIGN;
  memcpy(extkey[0], seed, KYBER_SYMBYTES);
  memcpy(extkey[1], seed, KYBER_SYMBYTES);
  memcpy(extkey[2], seed, KYBER_SYMBYTES);
  memcpy(extkey[3], seed, KYBER_SYMBYTES);
  extkey[0][KYBER_SYMBYTES] = nonce0;
  extkey[1][KYBER_SYMBYTES] = nonce1;
  extkey[2][KYBER_SYMBYTES] = nonce2;
  extkey[3][KYBER_SYMBYTES] = nonce3;

#if KYBER_ETA1 == KYBER_ETA2
  shake256x4(buf1[0], buf1[1], buf2[0], buf2[1], KYBER_ETA1 * KYBER_N / 4,
             extkey[0], extkey[1], extkey[2], extkey[3], KYBER_SYMBYTES + 1);
#else
  shake256(buf1[0], sizeof(buf1[0]), extkey[0], sizeof(extkey[0]));
  shake256(buf1[1], sizeof(buf1[1]), extkey[1], sizeof(extkey[1]));
  shake256(buf2[0], sizeof(buf2[0]), extkey[2], sizeof(extkey[2]));
  shake256(buf2[1], sizeof(buf2[1]), extkey[3], sizeof(extkey[3]));
#endif

  poly_cbd_eta1(r0, buf1[0]);
  poly_cbd_eta1(r1, buf1[1]);
  poly_cbd_eta2(r2, buf2[0]);
  poly_cbd_eta2(r3, buf2[1]);

  POLY_BOUND_MSG(r0, KYBER_ETA1 + 1, "poly_getnoise_eta1122_4x output 0");
  POLY_BOUND_MSG(r1, KYBER_ETA1 + 1, "poly_getnoise_eta1122_4x output 1");
  POLY_BOUND_MSG(r2, KYBER_ETA2 + 1, "poly_getnoise_eta1122_4x output 2");
  POLY_BOUND_MSG(r3, KYBER_ETA2 + 1, "poly_getnoise_eta1122_4x output 3");
}

/*************************************************
 * Name:        poly_basemul_montgomery_cached
 *
 * Description: Multiplication of two polynomials in NTT domain,
 *              using mulcache for second operand.
 *
 *              Bounds:
 *              - a is assumed to be coefficient-wise < q in absolute value.
 *              - b is assumed to be the output of a forward NTT and
 *                thus coefficient-wise bound by C
 *              - b_cache is assumed to be coefficient-wise bound by D.
 *
 *              The result is coefficient-wise bound by 3/2 q in absolute value.
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const poly *a: pointer to first input polynomial
 *              - const poly *b: pointer to second input polynomial
 *              - const poly_mulcache *b_cache: pointer to mulcache
 *                  for second input polynomial. Can be computed
 *                  via poly_mulcache_compute().
 **************************************************/
void poly_basemul_montgomery_cached(poly *r, const poly *a, const poly *b,
                                    const poly_mulcache *b_cache) {
  unsigned int i;
  for (i = 0; i < KYBER_N / 4; i++) {
    basemul_cached(&r->coeffs[4 * i], &a->coeffs[4 * i], &b->coeffs[4 * i],
                   b_cache->coeffs[2 * i]);
    basemul_cached(&r->coeffs[4 * i + 2], &a->coeffs[4 * i + 2],
                   &b->coeffs[4 * i + 2], b_cache->coeffs[2 * i + 1]);
  }
}

/*************************************************
 * Name:        poly_tomont
 *
 * Description: Inplace conversion of all coefficients of a polynomial
 *              from normal domain to Montgomery domain
 *
 *              Bounds: Output < q in absolute value.
 *
 * Arguments:   - poly *r: pointer to input/output polynomial
 **************************************************/
#if !defined(MLKEM_USE_NATIVE_POLY_TOMONT)
void poly_tomont(poly *r) {
  unsigned int i;
  const int16_t f = (1ULL << 32) % KYBER_Q;  // 1353
  for (i = 0; i < KYBER_N; i++) {
    r->coeffs[i] = montgomery_reduce((int32_t)r->coeffs[i] * f);
  }

  POLY_BOUND(r, KYBER_Q);
}
#else  /* MLKEM_USE_NATIVE_POLY_TOMONT */
void poly_tomont(poly *r) {
  poly_tomont_native(r);
  POLY_BOUND(r, KYBER_Q);
}
#endif /* MLKEM_USE_NATIVE_POLY_TOMONT */

/*************************************************
 * Name:        poly_reduce
 *
 * Description: Converts polynomial to _unsigned canonical_ representatives.
 *
 *              The input coefficients can be arbitrary integers in int16_t.
 *              The output coefficients are in [0,1,...,KYBER_Q-1].
 *
 * Arguments:   - poly *r: pointer to input/output polynomial
 **************************************************/
// REF-CHANGE: The semantics of poly_reduce() is different in
//             the reference implementation, which requires
//             signed canonical output data. Unsigned canonical
//             outputs are better suited to the only remaining
//             use of poly_reduce() in the context of (de)serialization.
#if !defined(MLKEM_USE_NATIVE_POLY_REDUCE)
void poly_reduce(poly *r) {
  unsigned int i;
  for (i = 0; i < KYBER_N; i++) {
    // Barrett reduction, giving signed canonical representative
    int16_t t = barrett_reduce(r->coeffs[i]);
    // Conditional addition to get unsigned canonical representative
    r->coeffs[i] = (int16_t)scalar_signed_to_unsigned_q_16(t);
  }

  POLY_UBOUND(r, KYBER_Q);
}
#else  /* MLKEM_USE_NATIVE_POLY_REDUCE */
void poly_reduce(poly *r) {
  poly_reduce_native(r);
  POLY_UBOUND(r, KYBER_Q);
}
#endif /* MLKEM_USE_NATIVE_POLY_REDUCE */

/*************************************************
 * Name:        poly_add
 *
 * Description: Add two polynomials; no modular reduction is performed
 *
 * Arguments: - poly *r: pointer to output polynomial
 *            - const poly *a: pointer to first input polynomial
 *            - const poly *b: pointer to second input polynomial
 **************************************************/
void poly_add(poly *r, const poly *a, const poly *b) {
  unsigned int i;
  for (i = 0; i < KYBER_N; i++) {
    r->coeffs[i] = a->coeffs[i] + b->coeffs[i];
  }
}

/*************************************************
 * Name:        poly_sub
 *
 * Description: Subtract two polynomials; no modular reduction is performed
 *
 * Arguments: - poly *r:       pointer to output polynomial
 *            - const poly *a: pointer to first input polynomial
 *            - const poly *b: pointer to second input polynomial
 **************************************************/
void poly_sub(poly *r, const poly *a, const poly *b) {
  unsigned int i;
  for (i = 0; i < KYBER_N; i++) {
    r->coeffs[i] = a->coeffs[i] - b->coeffs[i];
  }
}

/*************************************************
 * Name:        poly_mulcache_compute
 *
 * Description: Precompute values speeding up
 *              base multiplications of polynomials
 *              in NTT domain.
 *
 *              The coefficients in the mulcache must be
 *              bound by KYBER_Q in absolute value.
 *
 * Arguments: - poly_mulcache *x: pointer to output cache.
 *            - const poly *a: pointer to input polynomial
 **************************************************/
#if !defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
void poly_mulcache_compute(poly_mulcache *x, const poly *a) {
  unsigned int i;
  for (i = 0; i < KYBER_N / 4; i++) {
    x->coeffs[2 * i + 0] = fqmul(a->coeffs[4 * i + 1], zetas[64 + i]);
    x->coeffs[2 * i + 1] = fqmul(a->coeffs[4 * i + 3], -zetas[64 + i]);
  }

  POLY_BOUND(x, KYBER_Q);
}
#else  /* MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE */
void poly_mulcache_compute(poly_mulcache *x, const poly *a) {
  poly_mulcache_compute_native(x, a);
  POLY_BOUND(x, KYBER_Q);
}
#endif /* MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE */
