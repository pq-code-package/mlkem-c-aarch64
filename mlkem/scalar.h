// Copyright (c) 2024 The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0
#ifndef SCALAR_H
#define SCALAR_H

#include "params.h"
#include "verify.h"

#define scalar_compress_d1 MLKEM_NAMESPACE(scalar_compress_d1)
#define scalar_compress_d4 MLKEM_NAMESPACE(scalar_compress_d4)
#define scalar_compress_d5 MLKEM_NAMESPACE(scalar_compress_d5)
#define scalar_compress_d10 MLKEM_NAMESPACE(scalar_compress_d10)
#define scalar_compress_d11 MLKEM_NAMESPACE(scalar_compress_d11)
#define scalar_decompress_d4 MLKEM_NAMESPACE(scalar_decompress_d4)
#define scalar_decompress_d5 MLKEM_NAMESPACE(scalar_decompress_d5)
#define scalar_decompress_d10 MLKEM_NAMESPACE(scalar_decompress_d10)
#define scalar_decompress_d11 MLKEM_NAMESPACE(scalar_decompress_d11)
#define scalar_signed_to_unsigned_q MLKEM_NAMESPACE(scalar_signed_to_unsigned_q)

/************************************************************
 * Name: scalar_compress_d1
 *
 * Description: Computes round(u * 2 / q)
 *
 *              Implements Compress_d from FIPS203, Eq (4.7),
 *              for d = 1.
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
// The multiplication in this routine will exceed UINT32_MAX
// and wrap around for large values of u. This is expected and required.
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
static inline uint32_t scalar_compress_d1(uint16_t u)
__contract__(
  requires(u <= MLKEM_Q - 1)
  ensures(return_value < 2)
  ensures(return_value == (((uint32_t)u * 2 + MLKEM_Q / 2) / MLKEM_Q) % 2)  )
{
  uint32_t d0 = u << 1;
  d0 *= 645083;
  d0 += 1u << 30;
  d0 >>= 31;
  return d0;
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/************************************************************
 * Name: scalar_compress_d4
 *
 * Description: Computes round(u * 16 / q) % 16
 *
 *              Implements Compress_d from FIPS203, Eq (4.7),
 *              for d = 4.
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
// The multiplication in this routine will exceed UINT32_MAX
// and wrap around for large values of u. This is expected and required.
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
static inline uint32_t scalar_compress_d4(uint16_t u)
__contract__(
  requires(u <= MLKEM_Q - 1)
  ensures(return_value < 16)
  ensures(return_value == (((uint32_t)u * 16 + MLKEM_Q / 2) / MLKEM_Q) % 16))
{
  uint32_t d0 = (uint32_t)u * 1290160;  // 16 * round(2^28 / MLKEM_Q)
  return (d0 + (1u << 27)) >> 28;       // round(d0/2^28)
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/************************************************************
 * Name: scalar_decompress_d4
 *
 * Description: Computes round(u * q / 16)
 *
 *              Implements Decompress_d from FIPS203, Eq (4.8),
 *              for d = 4.
 *
 * Arguments: - u: Unsigned canonical modulus modulo 16
 *                 to be decompressed.
 ************************************************************/
static inline uint16_t scalar_decompress_d4(uint32_t u)
__contract__(
  requires(0 <= u && u < 16)
  ensures(return_value <= (MLKEM_Q - 1))
) { return ((u * MLKEM_Q) + 8) / 16; }

/************************************************************
 * Name: scalar_compress_d5
 *
 * Description: Computes round(u * 32 / q) % 32
 *
 *              Implements Compress_d from FIPS203, Eq (4.7),
 *              for d = 5.
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
// The multiplication in this routine will exceed UINT32_MAX
// and wrap around for large values of u. This is expected and required.
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
static inline uint32_t scalar_compress_d5(uint16_t u)
__contract__(
  requires(u <= MLKEM_Q - 1)
  ensures(return_value < 32)
  ensures(return_value == (((uint32_t)u * 32 + MLKEM_Q / 2) / MLKEM_Q) % 32)  )
{
  uint32_t d0 = (uint32_t)u * 1290176;  // 2^5 * round(2^27 / MLKEM_Q)
  return (d0 + (1u << 26)) >> 27;       // round(d0/2^27)
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/************************************************************
 * Name: scalar_decompress_d5
 *
 * Description: Computes round(u * q / 32)
 *
 *              Implements Decompress_d from FIPS203, Eq (4.8),
 *              for d = 5.
 *
 * Arguments: - u: Unsigned canonical modulus modulo 32
 *                 to be decompressed.
 ************************************************************/
static inline uint16_t scalar_decompress_d5(uint32_t u)
__contract__(
  requires(0 <= u && u < 32)
  ensures(return_value <= MLKEM_Q - 1)
) { return ((u * MLKEM_Q) + 16) / 32; }

/************************************************************
 * Name: scalar_compress_d10
 *
 * Description: Computes round(u * 2**10 / q) % 2**10
 *
 *              Implements Compress_d from FIPS203, Eq (4.7),
 *              for d = 10.
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
// The multiplication in this routine will exceed UINT32_MAX
// and wrap around for large values of u. This is expected and required.
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
// TODO: do the same for the other static inline functions
STATIC_INLINE_TESTABLE
uint32_t scalar_compress_d10(uint16_t u)
__contract__(
  requires(u <= MLKEM_Q - 1)
  ensures(return_value < (1u << 10))
  ensures(return_value == (((uint32_t)u * (1u << 10) + MLKEM_Q / 2) / MLKEM_Q) % (1 << 10)))
{
  uint64_t d0 = (uint64_t)u * 2642263040;  // 2^10 * round(2^32 / MLKEM_Q)
  d0 = (d0 + ((uint64_t)1u << 32)) >> 33;
  return (d0 & 0x3FF);
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/************************************************************
 * Name: scalar_decompress_d10
 *
 * Description: Computes round(u * q / 1024)
 *
 *              Implements Decompress_d from FIPS203, Eq (4.8),
 *              for d = 10.
 *
 * Arguments: - u: Unsigned canonical modulus modulo 16
 *                 to be decompressed.
 ************************************************************/
static inline uint16_t scalar_decompress_d10(uint32_t u)
__contract__(
  requires(0 <= u && u < 1024)
  ensures(return_value <= (MLKEM_Q - 1))
) { return ((u * MLKEM_Q) + 512) / 1024; }

/************************************************************
 * Name: scalar_compress_d11
 *
 * Description: Computes round(u * 2**11 / q) % 2**11
 *
 *              Implements Compress_d from FIPS203, Eq (4.7),
 *              for d = 11.
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
// The multiplication in this routine will exceed UINT32_MAX
// and wrap around for large values of u. This is expected and required.
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
STATIC_INLINE_TESTABLE
uint32_t scalar_compress_d11(uint16_t u)
__contract__(
  requires(u <= MLKEM_Q - 1)
  ensures(return_value < (1u << 11))
  ensures(return_value == (((uint32_t)u * (1u << 11) + MLKEM_Q / 2) / MLKEM_Q) % (1 << 11)))
{
  uint64_t d0 = (uint64_t)u * 5284526080;  // 2^11 * round(2^33 / MLKEM_Q)
  d0 = (d0 + ((uint64_t)1u << 32)) >> 33;
  return (d0 & 0x7FF);
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/************************************************************
 * Name: scalar_decompress_d11
 *
 * Description: Computes round(u * q / 1024)
 *
 *              Implements Decompress_d from FIPS203, Eq (4.8),
 *              for d = 10.
 *
 * Arguments: - u: Unsigned canonical modulus modulo 16
 *                 to be decompressed.
 ************************************************************/
STATIC_INLINE_TESTABLE
uint16_t scalar_decompress_d11(uint32_t u)
__contract__(
  requires(0 <= u && u < 2048)
  ensures(return_value <= (MLKEM_Q - 1))
) { return ((u * MLKEM_Q) + 1024) / 2048; }

/************************************************************
 * Name: scalar_signed_to_unsigned_q
 *
 * Description: converts signed polynomial coefficient
 *              from signed (-3328 .. 3328) form to
 *              unsigned form (0 .. 3328).
 *
 * Note: Cryptographic constant time implementation
 *
 * Examples:       0 -> 0
 *                 1 -> 1
 *              3328 -> 3328
 *                -1 -> 3328
 *                -2 -> 3327
 *             -3328 -> 1
 *
 * Arguments: c: signed coefficient to be converted
 ************************************************************/
STATIC_INLINE_TESTABLE
uint16_t scalar_signed_to_unsigned_q(int16_t c)
__contract__(
  requires(c >= -(MLKEM_Q - 1) && c <= (MLKEM_Q - 1))
  ensures(return_value >= 0 && return_value <= (MLKEM_Q - 1))
  ensures(return_value == (int32_t)c + (((int32_t)c < 0) * MLKEM_Q)))
{
  // Add Q if c is negative, but in constant time
  cmov_int16(&c, c + MLKEM_Q, c < 0);

  cassert(c >= 0, "scalar_signed_to_unsigned_q result lower bound");
  cassert(c < MLKEM_Q, "scalar_signed_to_unsigned_q result upper bound");

  // and therefore cast to uint16_t is safe.
  return (uint16_t)c;
}

#endif /* SCALAR_H */
