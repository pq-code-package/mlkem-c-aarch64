// SPDX-License-Identifier: Apache-2.0
#ifndef POLY_H
#define POLY_H

#include <stdint.h>
#include "params.h"

/*
 * Elements of R_q = Z_q[X]/(X^n + 1). Represents polynomial
 * coeffs[0] + X*coeffs[1] + X^2*coeffs[2] + ... + X^{n-1}*coeffs[n-1]
 */
typedef struct {
    int16_t coeffs[KYBER_N];
} poly;

#define scalar_compress_q_16   KYBER_NAMESPACE(scalar_compress_q_16)
#define scalar_decompress_q_16 KYBER_NAMESPACE(scalar_decompress_q_16)
#define scalar_compress_q_32   KYBER_NAMESPACE(scalar_compress_q_32)
#define scalar_decompress_q_32 KYBER_NAMESPACE(scalar_decompress_q_32)

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

#define poly_compress KYBER_NAMESPACE(poly_compress)
void poly_compress(uint8_t r[KYBER_POLYCOMPRESSEDBYTES], const poly *a)
/* INDENT-OFF */
__CPROVER_requires(__CPROVER_is_fresh(r, KYBER_POLYCOMPRESSEDBYTES))
__CPROVER_requires(__CPROVER_forall { unsigned i; (i < KYBER_N) ==> ( -KYBER_Q <= a->coeffs[i] && a->coeffs[i] < KYBER_Q ) })
__CPROVER_assigns(__CPROVER_object_whole(r));
/* INDENT-ON */


#define poly_decompress KYBER_NAMESPACE(poly_decompress)
void poly_decompress(poly *r, const uint8_t a[KYBER_POLYCOMPRESSEDBYTES]);

#define poly_tobytes KYBER_NAMESPACE(poly_tobytes)
void poly_tobytes(uint8_t r[KYBER_POLYBYTES], const poly *a);
#define poly_frombytes KYBER_NAMESPACE(poly_frombytes)
void poly_frombytes(poly *r, const uint8_t a[KYBER_POLYBYTES]);

#define poly_frommsg KYBER_NAMESPACE(poly_frommsg)
void poly_frommsg(poly *r, const uint8_t msg[KYBER_INDCPA_MSGBYTES]);
#define poly_tomsg KYBER_NAMESPACE(poly_tomsg)
void poly_tomsg(uint8_t msg[KYBER_INDCPA_MSGBYTES], const poly *r);

#define poly_getnoise_eta1 KYBER_NAMESPACE(poly_getnoise_eta1)
void poly_getnoise_eta1(poly *r, const uint8_t seed[KYBER_SYMBYTES], uint8_t nonce);

#define poly_getnoise_eta2 KYBER_NAMESPACE(poly_getnoise_eta2)
void poly_getnoise_eta2(poly *r, const uint8_t seed[KYBER_SYMBYTES], uint8_t nonce);

#define poly_ntt KYBER_NAMESPACE(poly_ntt)
void poly_ntt(poly *r);
#define poly_invntt_tomont KYBER_NAMESPACE(poly_invntt_tomont)
void poly_invntt_tomont(poly *r);
#define poly_basemul_montgomery KYBER_NAMESPACE(poly_basemul_montgomery)
void poly_basemul_montgomery(poly *r, const poly *a, const poly *b);
#define poly_tomont KYBER_NAMESPACE(poly_tomont)
void poly_tomont(poly *r);

#define poly_reduce KYBER_NAMESPACE(poly_reduce)
void poly_reduce(poly *r);

#define poly_add KYBER_NAMESPACE(poly_add)
void poly_add(poly *r, const poly *a, const poly *b);
#define poly_sub KYBER_NAMESPACE(poly_sub)
void poly_sub(poly *r, const poly *a, const poly *b);

#endif
