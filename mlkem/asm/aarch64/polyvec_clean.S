// SPDX-License-Identifier: Apache-2.0
//
// AArch64 re-implementation of the asymmetric base multiplication from:
//
// Neon NTT: Faster Dilithium, Kyber, and Saber on Cortex-A72 and Apple M1
// https://eprint.iacr.org/2021/986
// https://github.com/neon-ntt/neon-ntt

#include "config.h"
#if defined(MLKEM_USE_AARCH64_ASM)

#include "params.h"

// Needed to provide ASM_LOAD directive
#include "common.i"

.macro barrett_reduce a
        sqdmulh t0.8h, \a\().8h, consts.h[1]
        srshr   t0.8h, t0.8h, #11
        mls     \a\().8h, t0.8h, consts.h[0]
.endm

// Input:
// - Vectors al, ah of 32-bit entries
// Output:
// - Montgomery reductions of al || ah, stored in al
.macro montgomery_reduce_long x, a
        uzp1   t0.8h, \a\()l.8h, \a\()h.8h
        mul    t0.8h, t0.8h, consts.h[2]
        smlal  \a\()l.4s, t0.4h, constN.4h
        smlal2 \a\()h.4s, t0.8h, constN.8h
        uzp2   \x\().8h, \a\()l.8h, \a\()h.8h
.endm

// Computes products (a0*b0 + a0*b0t, a0*b1 + a1*b0) in 32-bit.
.macro pmull d, a, b
        smull  \d\()0l.4s, \a\()0.4h, \b\()0.4h
        smull2 \d\()0h.4s, \a\()0.8h, \b\()0.8h
        smlal  \d\()0l.4s, \a\()1.4h, \b\()1t.4h
        smlal2 \d\()0h.4s, \a\()1.8h, \b\()1t.8h

        smull  \d\()1l.4s, \a\()0.4h, \b\()1.4h
        smull2 \d\()1h.4s, \a\()0.8h, \b\()1.8h
        smlal  \d\()1l.4s, \a\()1.4h, \b\()0.4h
        smlal2 \d\()1h.4s, \a\()1.8h, \b\()0.8h
.endm

.macro pmlal d, a, b
        smlal  \d\()0l.4s, \a\()0.4h, \b\()0.4h
        smlal2 \d\()0h.4s, \a\()0.8h, \b\()0.8h
        smlal  \d\()0l.4s, \a\()1.4h, \b\()1t.4h
        smlal2 \d\()0h.4s, \a\()1.8h, \b\()1t.8h

        smlal  \d\()1l.4s, \a\()0.4h, \b\()1.4h
        smlal2 \d\()1h.4s, \a\()0.8h, \b\()1.8h
        smlal  \d\()1l.4s, \a\()1.4h, \b\()0.4h
        smlal2 \d\()1h.4s, \a\()1.8h, \b\()0.8h
.endm

.macro load_polys a, b, a_ptr, b_ptr, b_cache_ptr
        ld2 {\a\()0.8h, \a\()1.8h}, [\a_ptr],       #32
        ld2 {\b\()0.8h, \b\()1.8h}, [\b_ptr],       #32
        ld1 {\b\()1t.8h},           [\b_cache_ptr], #16
.endm

.macro save_vregs
        sub sp, sp, #(16*4)
        stp  d8,  d9, [sp, #16*0]
        stp d10, d11, [sp, #16*1]
        stp d12, d13, [sp, #16*2]
        stp d14, d15, [sp, #16*3]
.endm

.macro restore_vregs
        ldp  d8,  d9, [sp, #16*0]
        ldp d10, d11, [sp, #16*1]
        ldp d12, d13, [sp, #16*2]
        ldp d14, d15, [sp, #16*3]
        add sp, sp, #(16*4)
.endm

.macro push_stack
        save_vregs
.endm

.macro pop_stack
        restore_vregs
.endm

.global polyvec_basemul_acc_montgomery_cached_asm_clean
.global _polyvec_basemul_acc_montgomery_cached_asm_clean

        out          .req x0
        a0_ptr       .req x1
        b0_ptr       .req x2
        b0_cache_ptr .req x3
        a1_ptr       .req x4
        b1_ptr       .req x5
        b1_cache_ptr .req x6
        a2_ptr       .req x7
        b2_ptr       .req x8
        b2_cache_ptr .req x9
        a3_ptr       .req x10
        b3_ptr       .req x11
        b3_cache_ptr .req x12

        count        .req x13
        xtmp         .req x14
        modulus      .req w15

        constN    .req v0
        constX    .req v1
        consts    .req v2

        aa0      .req v3
        aa1      .req v4
        bb0      .req v5
        bb1      .req v6
        bb1t     .req v7

        res0l   .req v8
        res1l   .req v9
        res0h   .req v10
        res1h   .req v11

        out0 .req v26
        out1 .req v27

        t0   .req v28

.p2align 4
const_addr:
        .short 3329
        .short 20159
        .short 3327
        .short 0
        .short 0
        .short 0
        .short 0
        .short 0

polyvec_basemul_acc_montgomery_cached_asm_clean:
_polyvec_basemul_acc_montgomery_cached_asm_clean:
        push_stack

        ASM_LOAD(xtmp, const_addr)
        ld1 {consts.8h}, [xtmp]

        ldrsh modulus, [xtmp]
        dup constN.8h, modulus

        // Computed bases of vector entries

        add a1_ptr, a0_ptr, #(1 * 512)
        add b1_ptr, b0_ptr, #(1 * 512)
        add b1_cache_ptr, b0_cache_ptr, #(1 * 512/2)

#if KYBER_K > 2
        add a2_ptr, a0_ptr, #(2 * 512)
        add b2_ptr, b0_ptr, #(2 * 512)
        add b2_cache_ptr, b0_cache_ptr, #(2 * 512/2)
#endif

#if KYBER_K > 3
        add a3_ptr, a0_ptr, #(3 * 512)
        add b3_ptr, b0_ptr, #(3 * 512)
        add b3_cache_ptr, b0_cache_ptr, #(3 * 512/2)
#endif

        mov count, #(KYBER_N / 16)
loop_start:

        load_polys aa, bb, a0_ptr, b0_ptr, b0_cache_ptr
        pmull res, aa, bb

        load_polys aa, bb, a1_ptr, b1_ptr, b1_cache_ptr
        pmlal res, aa, bb

#if KYBER_K > 2
        load_polys aa, bb, a2_ptr, b2_ptr, b2_cache_ptr
        pmlal res, aa, bb
#endif

#if KYBER_K > 3
        load_polys aa, bb, a3_ptr, b3_ptr, b3_cache_ptr
        pmlal res, aa, bb
#endif

        montgomery_reduce_long out0, res0
        montgomery_reduce_long out1, res1

        // CHECK: Is this really needed at this point?
        barrett_reduce out0
        barrett_reduce out1

        st2 {out0.8h, out1.8h}, [out], #32

        subs count, count, #1
        cbnz count, loop_start

        pop_stack
        ret

#endif /* MLKEM_USE_AARCH64_ASM */
