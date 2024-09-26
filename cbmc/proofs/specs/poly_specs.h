// SPDX-License-Identifier: Apache-2.0
#ifndef POLY_SPECS_H
#define POLY_SPECS_H

#include <stddef.h>
#include <stdint.h>
#include "params.h"
#include "cbmc.h"

/*
 * Elements of R_q = Z_q[X]/(X^n + 1). Represents polynomial
 * coeffs[0] + X*coeffs[1] + X^2*coeffs[2] + ... + X^{n-1}*coeffs[n-1]
 */
typedef struct
{
    int16_t coeffs[KYBER_N];
} ALIGN(16) poly;

/*
 * INTERNAL presentation of precomputed data speeding up
 * the base multiplication of two polynomials in NTT domain.
 */
// REF-CHANGE: This structure does not exist in the reference
// implementation.
typedef struct
{
    int16_t coeffs[KYBER_N >> 1];
} poly_mulcache;

#define scalar_compress_q_16 KYBER_NAMESPACE(scalar_compress_q_16)
#define scalar_decompress_q_16 KYBER_NAMESPACE(scalar_decompress_q_16)
#define scalar_compress_q_32 KYBER_NAMESPACE(scalar_compress_q_32)
#define scalar_decompress_q_32 KYBER_NAMESPACE(scalar_decompress_q_32)
#define scalar_signed_to_unsigned_q_16 KYBER_NAMESPACE(scalar_signed_to_unsigned_q_16)
#define poly_compress KYBER_NAMESPACE(poly_compress)
#define poly_decompress KYBER_NAMESPACE(poly_decompress)

uint32_t scalar_compress_q_16   (int32_t u)
/* INDENT-OFF */
__CPROVER_requires(0 <= u && u < KYBER_Q)
__CPROVER_ensures(__CPROVER_return_value < 16)
__CPROVER_ensures(__CPROVER_return_value == (((uint32_t) u * 16 + KYBER_Q / 2) / KYBER_Q) % 16);
/* INDENT-ON */

uint32_t scalar_decompress_q_16 (uint32_t u)
/* INDENT-OFF */
__CPROVER_requires(0 <= u && u < 16)
__CPROVER_ensures(__CPROVER_return_value < KYBER_Q);
/* INDENT-ON */

uint32_t scalar_compress_q_32   (int32_t u)
/* INDENT-OFF */
__CPROVER_requires(0 <= u && u < KYBER_Q)
__CPROVER_ensures(__CPROVER_return_value < 32)
__CPROVER_ensures(__CPROVER_return_value == (((uint32_t) u * 32 + KYBER_Q / 2) / KYBER_Q) % 32);
/* INDENT-ON */

uint32_t scalar_decompress_q_32 (uint32_t u)
/* INDENT-OFF */
__CPROVER_requires(0 <= u && u < 32)
__CPROVER_ensures(__CPROVER_return_value < KYBER_Q);
/* INDENT-ON */

uint16_t scalar_signed_to_unsigned_q_16 (int16_t c)
/* *INDENT-OFF* */
__CPROVER_requires(c > -KYBER_Q) // c >= -3328
__CPROVER_requires(c < KYBER_Q)  // c <= 3328
__CPROVER_ensures(__CPROVER_return_value >= 0)
__CPROVER_ensures(__CPROVER_return_value < KYBER_Q)
__CPROVER_ensures(__CPROVER_return_value == (int32_t) c + (((int32_t) c < 0) * KYBER_Q));
/* *INDENT-ON* */

void poly_compress(uint8_t r[KYBER_POLYCOMPRESSEDBYTES], const poly *a)
/* *INDENT-OFF* */
__CPROVER_requires(r != NULL)
__CPROVER_requires(__CPROVER_is_fresh(r, KYBER_POLYCOMPRESSEDBYTES))
__CPROVER_requires(a != NULL)
__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(poly)))
__CPROVER_requires(__CPROVER_forall { unsigned k; (k < KYBER_N) ==> ( -KYBER_Q < a->coeffs[k] && a->coeffs[k] < KYBER_Q ) })
__CPROVER_assigns(__CPROVER_object_whole(r));
/* *INDENT-ON* */

#undef scalar_compress_q_16
#undef scalar_decompress_q_16
#undef scalar_compress_q_32
#undef scalar_decompress_q_32
#undef scalar_signed_to_unsigned_q_16
#undef poly_compress
#undef poly_decompress


// Include to ensure that signature changes in poly.h are reflected here.
#include <poly.h>

#endif
