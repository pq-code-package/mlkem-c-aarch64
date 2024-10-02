// SPDX-License-Identifier: Apache-2.0
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include "kem.h"
#include "hal.h"
#include "randombytes.h"

#include "keccakf1600.h"
#include "../mlkem/asm/asm.h"

#define NWARMUP 50
#define NITERERATIONS 300
#define NTESTS 200

static int cmp_uint64_t(const void *a, const void *b)
{
    return (int)((*((const uint64_t *)a)) - (*((const uint64_t *)b)));
}

#define BENCH(txt,code)                                   \
    for (i = 0; i < NTESTS; i++)                          \
    {                                                     \
        randombytes((uint8_t*)data0, sizeof(data0));      \
        randombytes((uint8_t*)data1, sizeof(data1));      \
        randombytes((uint8_t*)data2, sizeof(data2));      \
        randombytes((uint8_t*)data3, sizeof(data3));      \
        for (j = 0; j < NWARMUP; j++)                     \
        {                                                 \
            code;                                         \
        }                                                 \
        \
        t0 = get_cyclecounter();                          \
        for (j = 0; j < NITERERATIONS; j++)               \
        {                                                 \
            code;                                         \
        }                                                 \
        t1 = get_cyclecounter();                          \
        (cyc)[i] = t1 - t0;                               \
    }                                                     \
    qsort((cyc), NTESTS, sizeof(uint64_t), cmp_uint64_t); \
    printf(txt " cycles=%"PRIu64"\n",                  \
           (cyc)[NTESTS >> 1]/NITERERATIONS);

static int bench(void)
{
    uint64_t data0[1024] ALIGN(16);
    uint64_t data1[1024] ALIGN(16);
    uint64_t data2[1024] ALIGN(16);
    uint64_t data3[1024] ALIGN(16);
    uint64_t cyc[NTESTS];

    unsigned int i, j;
    uint64_t t0, t1;

    BENCH("keccak-f1600-x1", KeccakF1600_StatePermute(data0));
    BENCH("keccak-f1600-x4", KeccakF1600x4_StatePermute(data0));

    #if defined(MLKEM_USE_AARCH64_ASM)
    BENCH("ntt-clean", ntt_asm_clean((int16_t *)data0));
    BENCH("intt-clean", intt_asm_clean((int16_t *)data0));
    BENCH("poly-reduce-clean", poly_reduce_asm_clean((int16_t *)data0));
    BENCH("poly-tomont-clean", poly_tomont_asm_clean((int16_t *)data0));
    BENCH("poly-tobytes-clean", poly_tobytes_asm_clean((uint8_t *) data0, (int16_t *)data1));
    BENCH("poly-mulcache-compute-clean",                                  \
          poly_mulcache_compute_asm_clean(                                \
                  (int16_t *) data0, (int16_t *) data1,                           \
                  (int16_t *) data2, (int16_t *) data3));
    BENCH("poly-basemul-acc-montgomery-clean",                            \
          polyvec_basemul_acc_montgomery_cached_asm_clean_name(KYBER_K) ( \
                  (int16_t *) data0, (int16_t *) data1,                           \
                  (int16_t *) data2, (int16_t *) data3));

    BENCH("ntt-opt", ntt_asm_opt((int16_t *)data0));
    BENCH("intt-opt", intt_asm_opt((int16_t *)data0));
    BENCH("poly-reduce-opt", poly_reduce_asm_opt((int16_t *)data0));
    BENCH("poly-tomont-opt", poly_tomont_asm_opt((int16_t *)data0));
    BENCH("poly-mulcache-compute-opt",                                    \
          poly_mulcache_compute_asm_opt(                                  \
                  (int16_t *) data0, (int16_t *) data1,                           \
                  (int16_t *) data2, (int16_t *) data3));
    BENCH("poly-basemul-acc-montgomery-opt",                              \
          polyvec_basemul_acc_montgomery_cached_asm_opt_name(KYBER_K) (   \
                  (int16_t *) data0, (int16_t *) data1,                           \
                  (int16_t *) data2, (int16_t *) data3));
    #endif

    return 0;
}

int main(void)
{
    enable_cyclecounter();
    bench();
    disable_cyclecounter();

    return 0;
}
