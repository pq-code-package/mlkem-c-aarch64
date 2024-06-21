// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file poly_decompress_harness.c
 * @brief Implements the proof harness for poly_decompress function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include "poly.h"

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
    poly r;
    uint8_t a[KYBER_POLYCOMPRESSEDBYTES];

    poly_decompress(&r, a);

    // TODO: We're replicating the post-condition of the function contract of
    // poly_decompress here. Ideally, we'd use CBMC's function contract mechanism
    // here, but there are still issues. cf. a similar comment in the Makefile.
    __CPROVER_assert(__CPROVER_forall
    {
        unsigned i; (i < KYBER_N) ==> ( 0 <= r.coeffs[i] && r.coeffs[i] < KYBER_Q )
    }, "failed to prove post-condition for poly_decompress");
}
