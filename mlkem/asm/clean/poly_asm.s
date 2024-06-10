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
/* Compute frommsg from 32 bits input, output 32 int16_t coeffs */
.macro frommsg_32bits dst0, dst1, dst2, dst3, src, i0, i1, i2, i3
    dup     \dst0\().8h, \src\().h[\i0]
    dup     \dst1\().8h, \src\().h[\i1]
    dup     \dst2\().8h, \src\().h[\i2]
    dup     \dst3\().8h, \src\().h[\i3]

    and     \dst0\().16b, \dst0\().16b, bits\().16b
    and     \dst1\().16b, \dst1\().16b, bits\().16b
    and     \dst2\().16b, \dst2\().16b, bits\().16b
    and     \dst3\().16b, \dst3\().16b, bits\().16b

    cmeq    \dst0\().8h, \dst0\().8h, #0
    cmeq    \dst1\().8h, \dst1\().8h, #0
    cmeq    \dst2\().8h, \dst2\().8h, #0
    cmeq    \dst3\().8h, \dst3\().8h, #0

    bic     \dst0\().16b, const\().16b, \dst0\().16b
    bic     \dst1\().16b, const\().16b, \dst1\().16b
    bic     \dst2\().16b, const\().16b, \dst2\().16b
    bic     \dst3\().16b, const\().16b, \dst3\().16b

.endm

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

    m               .req v18
    mq              .req q18
    m1              .req v19
    m2              .req v20

    a0              .req v21
    a1              .req v22
    a2              .req v23
    a3              .req v24

    c0              .req v25
    c1              .req v26
    c2              .req v27
    c3              .req v28

    /* Vectorize code start */
    mov     tmp, #1665                // (KYBER_Q + 1) / 2
    dup     const.8h, tmp
    ldr     bitsq, [bit_table]
    mov     iter, xzr
    loop:
        // Load 16 bytes from m
        ldr     mq, [msg, iter]

        /* Extend from int8x16_t vector to 2 int16x8_t vectors */
        ushll   m1.8h, m.8b, #0
        ushll2  m2.8h, m.16b, #0

        frommsg_32bits a0, a1, a2, a3, m1, 0, 1, 2, 3
        frommsg_32bits c0, c1, c2, c3, m1, 4, 5, 6, 7

        st1     {a0.8h, a1.8h, a2.8h, a3.8h}, [coeffs]
        add     coeffs, coeffs, #64
        st1     {c0.8h, c1.8h, c2.8h, c3.8h}, [coeffs]
        add     coeffs, coeffs, #64

        frommsg_32bits a0, a1, a2, a3, m2, 0, 1, 2, 3
        frommsg_32bits c0, c1, c2, c3, m2, 4, 5, 6, 7

        st1     {a0.8h, a1.8h, a2.8h, a3.8h}, [coeffs]
        add     coeffs, coeffs, #64
        st1     {c0.8h, c1.8h, c2.8h, c3.8h}, [coeffs]
        add     coeffs, coeffs, #64

        add     iter, iter, #16
        cmp     iter, #32
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
    .unreq          m
    .unreq          mq
    .unreq          m1
    .unreq          m2
    .unreq          a0
    .unreq          a1
    .unreq          a2
    .unreq          a3
    .unreq          c0
    .unreq          c1
    .unreq          c2
    .unreq          c3
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

    t0s             .req s23
    t1s             .req s24
    t2s             .req s25
    t3s             .req s26

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

        fmov        r0, t0s
        fmov        r1, t1s
        fmov        r2, t2s
        fmov        r3, t3s

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

    .unreq t0s
    .unreq t1s
    .unreq t2s
    .unreq t3s
