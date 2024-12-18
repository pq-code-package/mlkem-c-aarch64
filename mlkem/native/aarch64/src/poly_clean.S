/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include "common.h"
#if defined(MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN)

// Needed to provide ASM_LOAD directive
#include "common.i"
#include "params.h"

.macro barrett_reduce a
        sqdmulh t0.8h, \a\().8h, consts.h[1]
        srshr   t0.8h, t0.8h, #11
        mls     \a\().8h, t0.8h, consts.h[0]
.endm

.macro scalar_signed_to_unsigned a
        sshr mask.8h, \a\().8h, #15
        and mask.16b, modulus.16b, mask.16b
        add \a\().8h, \a\().8h, mask.8h
.endm

.macro mulmod dst, src, const, const_twisted
        sqrdmulh tmp0.8h,    \src\().8h, \const_twisted\().8h
        mul      \dst\().8h, \src\().8h, \const\().8h
        mls      \dst\().8h, tmp0.8h,    consts.h[0]
.endm

/**********************************
 *          poly_reduce()         *
 **********************************/
.global MLKEM_NAMESPACE(poly_reduce_asm_clean)
.global _MLKEM_NAMESPACE(poly_reduce_asm_clean)

.p2align 4
const_addr:
        .short 3329   // ML-KEM modulus
        .short 20159  // Barrett twist of 1 wrt 2^27
        .short -1044  // 2^16 % 3329
        .short -10276 // Barrett twist of -1044 (wrt 2^16)
        .short 0
        .short 0
        .short 0
        .short 0

        ptr    .req x0
        count  .req x1
        xtmp   .req x2
        wmodulus .req w3

        q_data .req q0
        data   .req v0
        t0     .req v1
        consts .req v2
        mask    .req v3
        modulus .req v4

MLKEM_NAMESPACE(poly_reduce_asm_clean):
_MLKEM_NAMESPACE(poly_reduce_asm_clean):

        ASM_LOAD(xtmp, const_addr)
        ld1 {consts.8h}, [xtmp]

        mov wmodulus, #3329
        dup modulus.8h, wmodulus

        mov count, #8
loop_start:
        ldr q_data, [ptr], #64
        barrett_reduce data
        scalar_signed_to_unsigned data
        str q_data, [ptr, #-64]

        ldr q_data, [ptr, #-48]
        barrett_reduce data
        scalar_signed_to_unsigned data
        str q_data, [ptr, #-48]

        ldr q_data, [ptr, #-32]
        barrett_reduce data
        scalar_signed_to_unsigned data
        str q_data, [ptr, #-32]

        ldr q_data, [ptr, #-16]
        barrett_reduce data
        scalar_signed_to_unsigned data
        str q_data, [ptr, #-16]

        subs count, count, #1
        cbnz count, loop_start

        ret

        .unreq ptr
        .unreq count
        .unreq xtmp
        .unreq q_data
        .unreq data
        .unreq t0
        .unreq consts
        .unreq mask
        .unreq wmodulus
        .unreq modulus

/********************************************
 *          poly_mulcache_compute()         *
 ********************************************/
.global MLKEM_NAMESPACE(poly_mulcache_compute_asm_clean)
.global _MLKEM_NAMESPACE(poly_mulcache_compute_asm_clean)

        cache_ptr  .req x0
        data_ptr   .req x1
        zeta_ptr   .req x2
        zeta_twisted_ptr   .req x3
        xtmp       .req x4

        count      .req x5

        data_odd       .req v1

        zeta           .req v2
        zeta_twisted   .req v3
        q_zeta         .req q2
        q_zeta_twisted .req q3

        q_tmp0  .req q4
        q_tmp1  .req q5
        tmp0    .req v4
        tmp1    .req v5
        consts  .req v6
        dst     .req v7
        q_dst   .req q7

MLKEM_NAMESPACE(poly_mulcache_compute_asm_clean):
_MLKEM_NAMESPACE(poly_mulcache_compute_asm_clean):
        ASM_LOAD(xtmp, const_addr)
        ld1 {consts.8h}, [xtmp]

        mov count, #(16)
mulcache_compute_loop_start:
        ldr q_tmp0, [data_ptr], #32
        ldr q_tmp1, [data_ptr, #-16]
        ldr q_zeta, [zeta_ptr], #16
        ldr q_zeta_twisted, [zeta_twisted_ptr], #16
        uzp2 data_odd.8h, tmp0.8h, tmp1.8h
        mulmod dst, data_odd, zeta, zeta_twisted
        str q_dst, [cache_ptr], #16

        subs count, count, #1
        cbnz count, mulcache_compute_loop_start

        ret

        .unreq cache_ptr
        .unreq data_ptr
        .unreq zeta_ptr
        .unreq xtmp
        .unreq count

        .unreq data_odd
        .unreq zeta
        .unreq q_zeta
        .unreq zeta_twisted
        .unreq q_zeta_twisted

        .unreq q_tmp0
        .unreq q_tmp1
        .unreq tmp0
        .unreq tmp1
        .unreq consts
        .unreq dst

/********************************************
 *             poly_transpose()             *
 ********************************************/

.macro transpose4 data
        trn1 t0.4s, \data\()0.4s, \data\()1.4s
        trn2 t1.4s, \data\()0.4s, \data\()1.4s
        trn1 t2.4s, \data\()2.4s, \data\()3.4s
        trn2 t3.4s, \data\()2.4s, \data\()3.4s

        trn2 \data\()2.2d, t0.2d, t2.2d
        trn2 \data\()3.2d, t1.2d, t3.2d
        trn1 \data\()0.2d, t0.2d, t2.2d
        trn1 \data\()1.2d, t1.2d, t3.2d
.endm

.global MLKEM_NAMESPACE(poly_transpose_asm_clean)
.global _MLKEM_NAMESPACE(poly_transpose_asm_clean)

        data0  .req v0
        data1  .req v1
        data2  .req v2
        data3  .req v3

        q_data0  .req q0
        q_data1  .req q1
        q_data2  .req q2
        q_data3  .req q3

        t0  .req v4
        t1  .req v5
        t2  .req v6
        t3  .req v7

        ptr   .req x0
        count .req x1

MLKEM_NAMESPACE(poly_transpose_asm_clean):
_MLKEM_NAMESPACE(poly_transpose_asm_clean):

        mov count, #8
poly_transpose_asm_clean_asm_loop_start:
        ldr q_data0, [ptr]
        ldr q_data1, [ptr, #(1*16)]
        ldr q_data2, [ptr, #(2*16)]
        ldr q_data3, [ptr, #(3*16)]

        transpose4 data

        str q_data0, [ptr], #(4*16)
        str q_data1, [ptr, #(-3*16)]
        str q_data2, [ptr, #(-2*16)]
        str q_data3, [ptr, #(-1*16)]

        subs count, count, #1
        cbnz count, poly_transpose_asm_clean_asm_loop_start
        ret

        .unreq data0
        .unreq data1
        .unreq data2
        .unreq data3
        .unreq t0
        .unreq t1
        .unreq t2
        .unreq t3
        .unreq ptr
        .unreq count

/********************************************
 *             poly_tobytes()               *
 ********************************************/
.global MLKEM_NAMESPACE(poly_tobytes_asm_clean)
.global _MLKEM_NAMESPACE(poly_tobytes_asm_clean)

        data0 .req v0
        data1 .req v1

        out0  .req v2
        out1  .req v3
        out2  .req v4

        tmp     .req v5

        dst   .req x0
        src   .req x1
        count .req x2

MLKEM_NAMESPACE(poly_tobytes_asm_clean):
_MLKEM_NAMESPACE(poly_tobytes_asm_clean):

        mov count, #16
poly_tobytes_asm_clean_asm_loop_start:
        ld2 {data0.8h, data1.8h}, [src], #32

        // r[3 * i + 0] = (t0 >> 0);
        xtn out0.8b, data0.8h

        // r[3 * i + 1] = (t0 >> 8);
        shrn out1.8b, data0.8h, #8
        xtn tmp.8b, data1.8h
        // r[3 * i + 1] = (t0 >> 8) | (t1 << 4);
        sli out1.8b, tmp.8b, #4

        // r[3 * i + 2] = (t1 >> 4);
        shrn out2.8b, data1.8h, #4

        st3 {out0.8b, out1.8b, out2.8b}, [dst], #24

        subs count, count, #1
        cbnz count, poly_tobytes_asm_clean_asm_loop_start
        ret

        .unreq data0
        .unreq data1
        .unreq out0
        .unreq out1
        .unreq out2
        .unreq tmp
        .unreq dst
        .unreq src
        .unreq count

/********************************************
 *             poly_frombytes()             *
 ********************************************/
.global MLKEM_NAMESPACE(poly_frombytes_asm_clean)
.global _MLKEM_NAMESPACE(poly_frombytes_asm_clean)

        out0 .req v6
        out1 .req v7
        out2 .req v4
        out3 .req v5
        q_out0 .req q6
        q_out1 .req q7
        q_out2 .req q4
        q_out3 .req q5

        in0  .req v2
        in1  .req v3
        in2  .req v4

        t0 .req v0
        t1 .req v1
        t2 .req v2
        t3 .req v3

        dst   .req x0
        src   .req x1
        count .req x2

MLKEM_NAMESPACE(poly_frombytes_asm_clean):
_MLKEM_NAMESPACE(poly_frombytes_asm_clean):

        mov count, #8
poly_frombytes_asm_clean_asm_loop_start:
        ld3 {in0.8b, in1.8b, in2.8b}, [src], #24

        // This is little-endian specific
        // r[2 * i + 0] = t0 | (t1 << 8)
        zip1 t0.16b, in0.16b, in1.16b
        // r[2 * i + 0] = (t0 | (t1 << 8)) & 0xFFF
        bic t0.8h, #0xF0, lsl #8

        // r[2 * i + 1] = (t2 << 4), in 16-bit
        ushll t1.8h, in2.8b, #4
        // tmp = (t1 >> 4), in 8-bit
        ushr in1.8b, in1.8b, #4
        // tmp = (t1 >> 4), in 16-bit
        uxtl in1.8h, in1.8b
        // r[2 * i + 1] = (t1 >> 4) | (t2 << 4), in 16-bit
        eor t1.16b, t1.16b, in1.16b

        zip1 out0.8h, t0.8h, t1.8h
        zip2 out1.8h, t0.8h, t1.8h

        // Second half

        ld3 {in0.8b, in1.8b, in2.8b}, [src], #24

        // This is little-endian specific
        // r[2 * i + 0] = t0 | (t1 << 8)
        zip1 t0.16b, in0.16b, in1.16b
        // r[2 * i + 0] = (t0 | (t1 << 8)) & 0xFFF
        bic t0.8h, #0xF0, lsl #8

        // r[2 * i + 1] = (t2 << 4), in 16-bit
        ushll t1.8h, in2.8b, #4
        // tmp = (t1 >> 4), in 8-bit
        ushr in1.8b, in1.8b, #4
        // tmp = (t1 >> 4), in 16-bit
        uxtl in1.8h, in1.8b
        // r[2 * i + 1] = (t1 >> 4) | (t2 << 4), in 16-bit
        eor t1.16b, t1.16b, in1.16b

        zip1 out2.8h, t0.8h, t1.8h
        zip2 out3.8h, t0.8h, t1.8h

        transpose4 out
        str q_out0, [dst], #(4*16)
        str q_out1, [dst, #(-3*16)]
        str q_out2, [dst, #(-2*16)]
        str q_out3, [dst, #(-1*16)]

        subs count, count, #1
        cbnz count, poly_frombytes_asm_clean_asm_loop_start
        ret

        .unreq out0
        .unreq out1
        .unreq out2
        .unreq out3
        .unreq q_out0
        .unreq q_out1
        .unreq q_out2
        .unreq q_out3
        .unreq in0
        .unreq in1
        .unreq in2
        .unreq t0
        .unreq t1
        .unreq t2
        .unreq t3
        .unreq dst
        .unreq src
        .unreq count

/**********************************
 *          poly_tomont()         *
 **********************************/
.global MLKEM_NAMESPACE(poly_tomont_asm_clean)
.global _MLKEM_NAMESPACE(poly_tomont_asm_clean)

        src     .req x0
        count   .req x1
        xtmp    .req x2

        wtmp2   .req w3

        data    .req v0
        q_data  .req q0
        res     .req v1
        q_res   .req q1

        consts  .req v2

        factor   .req v3
        factor_t .req v4

        tmp0    .req v5

MLKEM_NAMESPACE(poly_tomont_asm_clean):
_MLKEM_NAMESPACE(poly_tomont_asm_clean):

        ASM_LOAD(xtmp, const_addr)
        ld1 {consts.8h}, [xtmp]

        ldrsh wtmp2, [xtmp, #(2*2)]
        dup factor.8h, wtmp2
        ldrh wtmp2, [xtmp, #(3*2)]
        dup factor_t.8h, wtmp2

        mov count, #8
poly_tomont_asm_loop:

        ldr q_data, [src], #64
        mulmod res, data, factor, factor_t
        str q_res, [src, #-64]

        ldr q_data, [src, #-48]
        mulmod res, data, factor, factor_t
        str q_res, [src, #-48]

        ldr q_data, [src, #-32]
        mulmod res, data, factor, factor_t
        str q_res, [src, #-32]

        ldr q_data, [src, #-16]
        mulmod res, data, factor, factor_t
        str q_res, [src, #-16]

        sub count, count, #1
        cbnz count, poly_tomont_asm_loop

        ret

#endif /* MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN */
