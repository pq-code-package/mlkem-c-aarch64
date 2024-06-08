// SPDX-License-Identifier: Apache-2.0

/*************************************************
* Name:        simd_memcpy
*
* Function: void simd_mempcy(void *dst, void *src, size_t length);
* Description: optimized memcpy with SIMD instructions for small data
*
* Arguments:   - void *dst:          pointer to destination buffer
*              - void *src:          pointer to source buffer
*              - size_t len:         length of src in bytes
**************************************************/
.align 4
.global simd_memcpy
.global _simd_memcpy
simd_memcpy:
_simd_memcpy:
    /* Input registers */
    dst                         .req x0
    src                         .req x1
    copylen                     .req x2

    /* Temporary registers, no need to preserve */
    data                        .req w12
    aligned_addr                .req x13
    aligned_len                 .req x14
    unaligned_len               .req x15

    cmp     copylen, #0                     // If copylen is less than or equal to 0
    b.le    end                             // then we exit the function
    cmp     copylen, #32                    // Check if size is less than 32 bytes
    b.lo    small_copy                      // Branch to small copy if size is less than 32

    // Align destination address
    mov     aligned_addr, dst
    and     aligned_addr, aligned_addr, #15
    cbz     aligned_addr, aligned_copy      // If already aligned, jump to aligned copy

    mov     unaligned_len, #16
    sub     unaligned_len, unaligned_len, aligned_addr
    cmp     copylen, unaligned_len
    b.lo    small_copy                      // If size is smaller than alignment padding, use small copy
    sub     copylen, copylen, unaligned_len

    small_align:
    ldrb    data, [src], #1
    strb    data, [dst], #1
    subs    unaligned_len, unaligned_len, #1
    b.ne    small_align

aligned_copy:
    // Main copy loop using 128-bit Neon registers
    lsr     aligned_len, copylen, #5        // Calculate the number of 32-byte chunks
    cbz     aligned_len, tail_copy          // If no chunks, jump to tail copy

    copy_loop:
    ldp     q0, q1, [src], #32
    stp     q0, q1, [dst], #32
    subs    aligned_len, aligned_len, #1
    b.ne    copy_loop

tail_copy:
    // Copy any remaining bytes less than 32 bytes
    and     copylen, copylen, #31
    cbz     copylen, end

small_copy:
    ldrb    data, [src], #1
    strb    data, [dst], #1
    subs    copylen, copylen, #1
    b.ne    small_copy

end:
    ret

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
.macro div48    dst, src
    mov     w8, #43691
    movk    w8, #43690, lsl #16
    umull   x8, \src, w8
    lsr     x8, x8, #37
    add     w8, w8, w8, lsl #1
    lsl     \dst, w8, #4
.endm

.align 4
.global     rej_uniform_asm
.global     _rej_uniform_asm
rej_uniform_asm:
_rej_uniform_asm:

    /* Input registers */
    stack                       .req x0
    buf                         .req x1
    buf_consumed                .req x2
    buflen                      .req w3
    len                         .req x4
    lenw                        .req w4
    table_idx                   .req x5
    bit_table                   .req x6

    /* Output registers */
    output                      .req x11
    sp_copy                     .req x16
    buf_consumed_cpy            .req x17

    /* Temporary registers */
    tmp                         .req w8
    count                       .req w8
    bound                       .req w9
    minw                        .req w8
    min                         .req x8
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


    /*
    * Preserve registers and restore them at the end of the function.
    * Stack alignment must be 16 bytes.
    * Stack size: 0x270 = 16 * 3 (preserve register) + sizeof(int16_t) * (KYBER_N + 32)
    * Memory layout from the bottom of the stack to the top:
    * 0x00:   x8   |  padding
    * 0x10:   x16  |  x17
    * 0x20:   x29  |  x30
    * Start at 0x030 to the end at 0x220:   KYBER_N * sizeof(int16_t)
    * 0x230 -> 0x270: 64 bytes padding to avoid overflow in the `str` sequence.
    * The 4 `str` sequences at the end of `loop48` can write from 0 bytes (4*0) to 64 bytes (4*16).
    * However, we only copy the maximum amount of `len` stored in x4 from stack to `x0`.
    */
    sub     sp, sp, #0x270
    str     x8, [sp]
    stp     x16, x17, [sp, #16]
    stp     x29, x30, [sp, #32]

    /* Vectorize code start */

    ldr     bits_q, [bit_table]
    movz    tmp, #3329
    dup     kyber_q.8h, tmp
    div48   bound, buflen

    mov     iterw, #0
    add     output, sp, #48
    mov     sp_copy, output
    mov     buf_consumed_cpy, buf_consumed

    loop48:
        add     x8, buf, iter

        ld3     {buf0.16b, buf1.16b, buf2.16b}, [x8]
        add     iterw, iterw, #48

        zip1    tmp0.16b, buf0.16b, buf1.16b
        zip2    tmp1.16b, buf0.16b, buf1.16b
        zip1    tmp2.16b, buf1.16b, buf2.16b
        zip2    tmp3.16b, buf1.16b, buf2.16b

        bic     tmp0.8h, #0xf0, lsl 8
        bic     tmp1.8h, #0xf0, lsl 8
        ushr    tmp2.8h, tmp2.8h, #4
        ushr    tmp3.8h, tmp3.8h, #4

        zip1    val0.8h, tmp0.8h, tmp2.8h
        zip2    val1.8h, tmp0.8h, tmp2.8h
        zip1    val2.8h, tmp1.8h, tmp3.8h
        zip2    val3.8h, tmp1.8h, tmp3.8h

        cmhi    sign0.8h, kyber_q.8h, val0.8h
        cmhi    sign1.8h, kyber_q.8h, val1.8h
        cmhi    sign2.8h, kyber_q.8h, val2.8h
        cmhi    sign3.8h, kyber_q.8h, val3.8h

        and     sign0.16b, sign0.16b, bits.16b
        and     sign1.16b, sign1.16b, bits.16b
        and     sign2.16b, sign2.16b, bits.16b
        and     sign3.16b, sign3.16b, bits.16b

        uaddlv  t0, sign0.8h
        uaddlv  t1, sign1.8h
        uaddlv  t2, sign2.8h
        uaddlv  t3, sign3.8h

        fmov    rec_idx_0, t0
        fmov    rec_idx_1, t1
        fmov    rec_idx_2, t2
        fmov    rec_idx_3, t3

        ldr     table0q, [table_idx, rec_idx_0, uxtw #4]
        ldr     table1q, [table_idx, rec_idx_1, uxtw #4]
        ldr     table2q, [table_idx, rec_idx_2, uxtw #4]
        ldr     table3q, [table_idx, rec_idx_3, uxtw #4]

        cnt     sign0.16b, sign0.16b
        cnt     sign1.16b, sign1.16b
        cnt     sign2.16b, sign2.16b
        cnt     sign3.16b, sign3.16b

        uaddlv  t0, sign0.8h
        uaddlv  t1, sign1.8h
        uaddlv  t2, sign2.8h
        uaddlv  t3, sign3.8h

        fmov    ctr0, t0
        fmov    ctr1, t1
        fmov    ctr2, t2
        fmov    ctr3, t3

        tbl     val0.16b, {val0.16b}, table0.16b
        tbl     val1.16b, {val1.16b}, table1.16b
        tbl     val2.16b, {val2.16b}, table2.16b
        tbl     val3.16b, {val3.16b}, table3.16b

        str     val0q, [output]
        add     output, output, ctr0, uxtw #1

        str     val1q, [output]
        add     output, output, ctr1, uxtw #1

        str     val2q, [output]
        add     output, output, ctr2, uxtw #1

        str     val3q, [output]
        add     output, output, ctr3, uxtw #1

        sub     x8, output, sp_copy
        lsr     x8, x8, #1

        cmp     count, lenw
        b.hs    memory_copy

        cmp     iterw, bound
        b.lo    loop48

    loop24:

        add     x8, buf, iter

        ld3     {buf0.8b, buf1.8b, buf2.8b}, [x8]
        add     iterw, iterw, #24

        zip1    tmp0.16b, buf0.16b, buf1.16b
        zip1    tmp1.16b, buf1.16b, buf2.16b

        bic     tmp0.8h, #0xf0, lsl 8
        ushr    tmp1.8h, tmp1.8h, #4

        zip1    val0.8h, tmp0.8h, tmp1.8h
        zip2    val1.8h, tmp0.8h, tmp1.8h

        cmhi    sign0.8h, kyber_q.8h, val0.8h
        cmhi    sign1.8h, kyber_q.8h, val1.8h

        and     sign0.16b, sign0.16b, bits.16b
        and     sign1.16b, sign1.16b, bits.16b

        uaddlv  t0, sign0.8h
        uaddlv  t1, sign1.8h

        fmov    rec_idx_0, t0
        fmov    rec_idx_1, t1

        ldr     table0q, [table_idx, rec_idx_0, uxtw #4]
        ldr     table1q, [table_idx, rec_idx_1, uxtw #4]

        cnt     sign0.16b, sign0.16b
        cnt     sign1.16b, sign1.16b

        uaddlv  t0, sign0.8h
        uaddlv  t1, sign1.8h

        fmov    ctr0, t0
        fmov    ctr1, t1

        tbl     val0.16b, {val0.16b}, table0.16b
        tbl     val1.16b, {val1.16b}, table1.16b

        str     val0q, [output]
        add     output, output, ctr0, uxtw #1

        str     val1q, [output]
        add     output, output, ctr1, uxtw #1

        sub     x8, output, sp_copy
        lsr     x8, x8, #1

        cmp     count, lenw
        b.hs    memory_copy

        cmp     iterw, buflen
        b.lo    loop24

    memory_copy:

        cmp     count, lenw
        csel    minw, count, lenw, lo
        cbz     minw, return

        ubfiz   x2, min, #1, #32
        mov     x1, sp_copy
        bl      simd_memcpy

    return:

        mov     w0, minw
        str     iterw, [buf_consumed_cpy]

        ldr     x8, [sp]
        ldp     x16, x17, [sp, #16]
        ldp     x29, x30, [sp, #32]
        add     sp, sp, #0x270
        ret
