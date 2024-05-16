// SPDX-License-Identifier: Apache-2.0
#include "params.h"

.text:

.macro div48    dst, src
    mov     w8, #43691
    movk    w8, #43690, lsl #16
    umull   x8, \src, w8
    lsr     x8, x8, #37
    add     w8, w8, w8, lsl #1
    lsl     \dst, w8, #4
.endm
/*************************************************
* Name:        rej_uniform_asm
*
* Description: Full SIMD lane, run rejection sampling on uniform random bytes to generate
*              uniform random integers mod q
*
* Arguments:   - int16_t *r:          pointer to output buffer
*              - unsigned int len:    requested number of 16-bit integers
*                                     (uniform mod q)
*              - const uint8_t *buf:  pointer to input buffer
*                                     (assumed to be uniform random bytes)
*              - unsigned int buflen: length of input buffer in bytes
*              - unsigned int *consumed: the length of consumed buffer
* Returns number of sampled 16-bit integers (at most len)
**************************************************/
.align 4
.global     rej_uniform_asm
.global     _rej_uniform_asm
rej_uniform_asm:
_rej_uniform_asm:

    /* Input registers */
    stack                       .req x0
    counter                     .req w0
    buf                         .req x1
    buf_consumed                .req x2
    buflen                      .req w3
    len                         .req x4
    lenw                        .req w4
    table_idx                   .req x5
    bit_table                   .req x6

    /* Output registers */
    output                      .req x11

    /* Temporary registers */
    tmp                         .req w8
    count                       .req w8
    bound                       .req w9
    iterw                       .req w10
    iter                        .req x10

    rec_idx_0                   .req w12
    rec_idx_1                   .req w13
    rec_idx_2                   .req w14
    rec_idx_3                   .req w15

    ctr0                        .req w12
    ctr1                        .req w13
    ctr2                        .req w14
    ctr3                        .req w15

    /* Vector registers */

    buf0                        .req v0
    buf1                        .req v1
    buf2                        .req v2

    tmp0                        .req v4
    tmp1                        .req v5
    tmp2                        .req v6
    tmp3                        .req v7

    sign0                       .req v4
    sign1                       .req v5
    sign2                       .req v6
    sign3                       .req v7

    val0                        .req v16
    val0q                       .req q16
    val1                        .req v17
    val1q                       .req q17
    val2                        .req v18
    val2q                       .req q18
    val3                        .req v19
    val3q                       .req q19

    t0                          .req s20
    t1                          .req s21
    t2                          .req s22
    t3                          .req s23

    table0                      .req v24
    table0q                     .req q24
    table1                      .req v25
    table1q                     .req q25
    table2                      .req v26
    table2q                     .req q26
    table3                      .req v27
    table3q                     .req q27

    kyber_q                     .req v30
    bits                        .req v31
    bits_q                      .req q31


    /* Vectorize code start */

    ldr bits_q, [bit_table]
    movz tmp, #KYBER_Q
    dup.8h kyber_q, tmp
    div48   bound, buflen

    mov     iterw, #0
    mov output, stack

    loop48:
        add     x8, buf, iter

        ld3.16b {buf0, buf1, buf2}, [x8]
        add iterw, iterw, #48

        zip1.16b tmp0, buf0, buf1
        zip2.16b tmp1, buf0, buf1
        zip1.16b tmp2, buf1, buf2
        zip2.16b tmp3, buf1, buf2

        bic.8h tmp0, #0xf0, lsl 8
        bic.8h tmp1, #0xf0, lsl 8
        ushr.8h tmp2, tmp2, #4
        ushr.8h tmp3, tmp3, #4

        zip1.8h val0, tmp0, tmp2
        zip2.8h val1, tmp0, tmp2
        zip1.8h val2, tmp1, tmp3
        zip2.8h val3, tmp1, tmp3

        cmhi.8h sign0, kyber_q, val0
        cmhi.8h sign1, kyber_q, val1
        cmhi.8h sign2, kyber_q, val2
        cmhi.8h sign3, kyber_q, val3

        and.16b sign0, sign0, bits
        and.16b sign1, sign1, bits
        and.16b sign2, sign2, bits
        and.16b sign3, sign3, bits

        uaddlv.8h t0, sign0
        uaddlv.8h t1, sign1
        uaddlv.8h t2, sign2
        uaddlv.8h t3, sign3

        fmov rec_idx_0, t0
        fmov rec_idx_1, t1
        fmov rec_idx_2, t2
        fmov rec_idx_3, t3

        ldr table0q, [table_idx, rec_idx_0, uxtw #4]
        ldr table1q, [table_idx, rec_idx_1, uxtw #4]
        ldr table2q, [table_idx, rec_idx_2, uxtw #4]
        ldr table3q, [table_idx, rec_idx_3, uxtw #4]

        cnt.16b sign0, sign0
        cnt.16b sign1, sign1
        cnt.16b sign2, sign2
        cnt.16b sign3, sign3

        uaddlv.8h t0, sign0
        uaddlv.8h t1, sign1
        uaddlv.8h t2, sign2
        uaddlv.8h t3, sign3

        fmov ctr0, t0
        fmov ctr1, t1
        fmov ctr2, t2
        fmov ctr3, t3

        tbl.16b val0, {val0}, table0
        tbl.16b val1, {val1}, table1
        tbl.16b val2, {val2}, table2
        tbl.16b val3, {val3}, table3

        str val0q, [output]
        add output, output, ctr0, uxtw #1

        str val1q, [output]
        add output, output, ctr1, uxtw #1

        str val2q, [output]
        add output, output, ctr2, uxtw #1

        str val3q, [output]
        add output, output, ctr3, uxtw #1

        sub     x8, output, stack
        lsr     x8, x8, #1

        cmp count, lenw
        b.hs    end

        cmp iterw, bound
        b.lo    loop48

    loop24:

        add x8, buf, iter

        ld3.8b {buf0, buf1, buf2}, [x8]
        add iterw, iterw, #24

        zip1.16b tmp0, buf0, buf1
        zip1.16b tmp1, buf1, buf2

        bic.8h tmp0, #0xf0, lsl 8
        ushr.8h tmp1, tmp1, #4

        zip1.8h val0, tmp0, tmp1
        zip2.8h val1, tmp0, tmp1

        cmhi.8h sign0, kyber_q, val0
        cmhi.8h sign1, kyber_q, val1

        and.16b sign0, sign0, bits
        and.16b sign1, sign1, bits

        uaddlv.8h t0, sign0
        uaddlv.8h t1, sign1

        fmov rec_idx_0, t0
        fmov rec_idx_1, t1

        ldr table0q, [table_idx, rec_idx_0, uxtw #4]
        ldr table1q, [table_idx, rec_idx_1, uxtw #4]

        cnt.16b sign0, sign0
        cnt.16b sign1, sign1

        uaddlv.8h t0, sign0
        uaddlv.8h t1, sign1

        fmov ctr0, t0
        fmov ctr1, t1

        tbl.16b val0, {val0}, table0
        tbl.16b val1, {val1}, table1

        str val0q, [output]
        add output, output, ctr0, uxtw #1

        str val1q, [output]
        add output, output, ctr1, uxtw #1

        sub x8, output, stack
        lsr x8, x8, #1

        cmp count, lenw
        b.hs    end

        cmp iterw, buflen
        b.lo    loop24

    end:
        mov counter, count
        str iterw, [buf_consumed]
        ret
