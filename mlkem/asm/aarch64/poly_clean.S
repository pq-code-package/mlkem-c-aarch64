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

#endif /* MLKEM_USE_AARCH64_ASM */
