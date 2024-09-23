// SPDX-License-Identifier: Apache-2.0
#include <stdint.h>
#include "params.h"
#include "reduce.h"

/*************************************************
* Name:        montgomery_reduce
*
* Description: Montgomery reduction; given a 32-bit integer a, computes
*              16-bit integer congruent to a * R^-1 mod q, where R=2^16
*
* Arguments:   - int32_t a: input integer to be reduced;
*                           has to be in {-q2^15,...,q2^15-1}
*
* Returns:     integer in {-q+1,...,q-1} congruent to a * R^-1 modulo q.
**************************************************/

// TODO: The output bound < |q| is easier to prove for input bound < |q|*2^15.
// (no special case needed for a=-2^15*q).
int16_t montgomery_reduce(int32_t a)
{
    int16_t t;

    t = (int16_t)a * QINV;
    t = (a - (int32_t)t * KYBER_Q) >> 16;

    // |t| <= |a|/2^16 + |t|*q/2^16 <= q/2 + q/2  q.
    //
    // Equality can only be attained for a=-q*2^16. In that case:
    // - (int16_t) a = -2^15,
    // - (int16_t)a * QINV = -2^15 (in int16_t),
    // - (int32_t)((int16_t) a * QINV) = -2^15,
    // and the final result is 0.
    //
    // Thus, we always have |t| < q.
    return t;
}

/*************************************************
* Name:        barrett_reduce
*
* Description: Barrett reduction; given a 16-bit integer a, computes
*              centered representative congruent to a mod q in {-(q-1)/2,...,(q-1)/2}
*
* Arguments:   - int16_t a: input integer to be reduced
*
* Returns:     integer in {-(q-1)/2,...,(q-1)/2} congruent to a modulo q.
**************************************************/
int16_t barrett_reduce(int16_t a)
{
    int16_t t;
    const int16_t v = ((1 << 26) + KYBER_Q / 2) / KYBER_Q;

    t  = ((int32_t)v * a + (1 << 25)) >> 26;
    t *= KYBER_Q;
    return a - t;
}
