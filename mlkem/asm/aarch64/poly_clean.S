// SPDX-License-Identifier: Apache-2.0

#include "config.h"
#if defined(MLKEM_USE_AARCH64_ASM)

// Needed to provide ASM_LOAD directive
#include "common.i"

.macro barrett_reduce a
        sqdmulh t0.8h, \a\().8h, consts.h[1]
        srshr   t0.8h, t0.8h, #11
        mls     \a\().8h, t0.8h, consts.h[0]
.endm

.macro mulmod dst, src, const, const_twisted
        sqrdmulh tmp0.8h,    \src\().8h, \const_twisted\().8h
        mul      \dst\().8h, \src\().8h, \const\().8h
        mls      \dst\().8h, tmp0.8h,    consts.h[0]
.endm

.global poly_reduce_asm_clean
.global _poly_reduce_asm_clean

.p2align 4
const_addr:
        .short 3329
        .short 20159
        .short 0
        .short 0
        .short 0
        .short 0
        .short 0
        .short 0

        ptr    .req x0
        count  .req x1
        xtmp   .req x2

        q_data .req q0
        data   .req v0
        t0     .req v1
        consts .req v2

poly_reduce_asm_clean:
_poly_reduce_asm_clean:

        ASM_LOAD(xtmp, const_addr)
        ld1 {consts.8h}, [xtmp]

        mov count, #8
loop_start:
        ldr q_data, [ptr], #64
        barrett_reduce data
        str q_data, [ptr, #-64]

        ldr q_data, [ptr, #-48]
        barrett_reduce data
        str q_data, [ptr, #-48]

        ldr q_data, [ptr, #-32]
        barrett_reduce data
        str q_data, [ptr, #-32]

        ldr q_data, [ptr, #-16]
        barrett_reduce data
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

.global poly_mulcache_compute_asm_clean
.global _poly_mulcache_compute_asm_clean

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

poly_mulcache_compute_asm_clean:
_poly_mulcache_compute_asm_clean:
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


#endif /* MLKEM_USE_AARCH64_ASM */
