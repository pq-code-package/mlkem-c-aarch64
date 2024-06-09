// SPDX-License-Identifier: Apache-2.0
/*************************************************
* Name:        poly_frommsg_asm
*
* Description: Convert 32-byte message to polynomial
*
* Arguments:   - int16_t *coeffs: pointer to output polynomial
*              - const uint8_t *msg: pointer to input message
*              - const uint16_t *bits: pointer to bit_table
**************************************************/
.align 4
.global poly_frommsg_asm
.global _poly_frommsg_asm
poly_frommsg_asm:
_poly_frommsg_asm:

    /* Input registers */
    coeffs          .req x0
    msg             .req x1
    bit_table       .req x2

    /* Temporary registers */
    iter            .req x9
    tmp             .req w10

    /* Vector registers */
    const           .req v16
    bits            .req v17
    bitsq           .req q17
    a0              .req v18
    a0q             .req q18

    /* Vectorize code start */
    mov     tmp, #1665                // (KYBER_Q + 1) / 2
    dup     const.8h, tmp
    ldr     bitsq, [bit_table]
    mov     iter, xzr
    loop:
        ldrb    tmp, [msg, iter]
        dup     a0.8h, tmp
        and     a0.16b, a0.16b, bits.16b
        cmeq    a0.8h, a0.8h, #0
        bic     a0.16b, const.16b, a0.16b
        str     a0q, [coeffs, iter, lsl #4]
        add     iter, iter, #1
        cmp     iter, #32            // KYBER_N / 8
        b.ne    loop
    ret

    /* Input registers */
    .unreq          coeffs
    .unreq          msg
    .unreq          bit_table
    
    /* Temporary registers */
    .unreq          iter
    .unreq          tmp

    /* Vector registers */
    .unreq          const
    .unreq          bits
    .unreq          bitsq
    .unreq          a0
    .unreq          a0q
/*************************************************
* Name:        poly_tomsg_asm
*
* Description: Convert polynomial to 32-byte message
*
* Arguments:   - uint8_t *msg: pointer to output message
*              - int16_t *coeffs: pointer to input polynomial
**************************************************/
.align 4
.global poly_tomsg_asm
.global _poly_tomsg_asm
poly_tomsg_asm:
_poly_tomsg_asm:

    /* Input registers */
    msg             .req x0
    coeffs          .req x1
    position        .req x2

    /* Temporary registers */
    iter            .req x9
    tmp             .req w10
    idx_addr        .req x11

    r0              .req w12
    r1              .req w13
    r2              .req w14
    r3              .req w15

    /* Vector registers */
    vhq             .req v16
    vhqinv          .req v17
    
    a0              .req v18
    a1              .req v19
    a2              .req v20
    a3              .req v21 
    
    idx             .req v22
    idxq            .req q22

    t0              .req h23
    t1              .req h24
    t2              .req h25
    t3              .req h26

    /* Vectorize code start */

    mov     w9, #1164           // KYBER_Q / 2
    dup     vhq.8h, w9
    mov     w10, #10079         // 2^26 / KYBER_Q / 2
    dup     vhqinv.8h, w10
    ldr     idxq, [position]

    mov iter, xzr

    loop32:
        ld1     {a0.8h, a1.8h, a2.8h, a3.8h}, [x1], #64
        
        /*  t << = 1; */ 
        add     a0.8h, a0.8h, a0.8h
        add     a1.8h, a1.8h, a1.8h
        add     a2.8h, a2.8h, a2.8h
        add     a3.8h, a3.8h, a3.8h

        /* t += KYBER_Q/2 */ 
        add     a0.8h, a0.8h, vhq.8h
        add     a1.8h, a1.8h, vhq.8h
        add     a2.8h, a2.8h, vhq.8h
        add     a3.8h, a3.8h, vhq.8h

        /* 
         * t = t / KYBER_Q 
         * Instead of direct division, we multiply with inverse of KYBER_Q and utilize the sqdmulh instruction. 
         * To do so, we have a few options:
         * 80635 = round(2^28/KYBER_Q) as in the reference C implementation
         * However, we need number that fit in the range [-2^15..2^15]
         * So we pick:
         * 20159 = round(2^26/KYBER_Q)
         * Because we use sqdmulh instruction, the constant will be:
         * 10079 = round(2^26/KYBER_Q/2)
         * sqdmulh helps us shift right by 16, we need additional shift right by 10 to complete shift right by 26.
         * The other approach is to use smull/umull instructions, but they are inefficient.
         */
        sqdmulh     a0.8h, a0.8h, vhqinv.8h
        sqdmulh     a1.8h, a1.8h, vhqinv.8h
        sqdmulh     a2.8h, a2.8h, vhqinv.8h
        sqdmulh     a3.8h, a3.8h, vhqinv.8h

        ushr        a0.8h, a0.8h, #10
        ushr        a1.8h, a1.8h, #10
        ushr        a2.8h, a2.8h, #10
        ushr        a3.8h, a3.8h, #10

        /* t = t & 1 */

        bic         a0.8h, #62
        bic         a1.8h, #62
        bic         a2.8h, #62
        bic         a3.8h, #62

        /* Position the bits */
        ushl        a0.8h, a0.8h, idx.8h
        ushl        a1.8h, a1.8h, idx.8h
        ushl        a2.8h, a2.8h, idx.8h
        ushl        a3.8h, a3.8h, idx.8h

        /* Extract the result */
        addv        t0, a0.8h
        addv        t1, a1.8h
        addv        t2, a2.8h
        addv        t3, a3.8h

        fmov        r0, t0
        fmov        r1, t1
        fmov        r2, t2
        fmov        r3, t3

        strb        r0, [x0], #1
        strb        r1, [x0], #1
        strb        r2, [x0], #1
        strb        r3, [x0], #1

        add         iter, iter, #4
        cmp         iter, #32
        b.ne        loop32

    ret

    /* Input registers */
    .unreq msg
    .unreq coeffs
    .unreq position

    /* Temporary registers */
    .unreq iter
    .unreq tmp
    .unreq idx_addr

    .unreq r0
    .unreq r1
    .unreq r2
    .unreq r3

    /* Vector registers */
    .unreq vhq
    .unreq vhqinv
    
    .unreq a0
    .unreq a1
    .unreq a2
    .unreq a3
    
    .unreq idx
    .unreq idxq

    .unreq t0
    .unreq t1
    .unreq t2
    .unreq t3
