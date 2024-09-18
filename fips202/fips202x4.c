// SPDX-License-Identifier: Apache-2.0
#include <string.h>
#include "fips202x4.h"
#include "fips202.h"
#include "keccakf1600.h"

#define KECCAK_CTX 25

// Internal presentation of batched Keccak state.
//
// TODO: Lanes need to be interleaved for efficient use of SIMD instructions.
typedef struct
{
    uint64_t lanes[25 * KECCAK_WAY];
} keccakx4_state;


static inline keccakx4_state *shakex4_state_to_keccakx4(shakex4_state *raw)
{
    // TODO: Add static assert that this has the same size as shakex4_state.
    return (keccakx4_state *) raw;
}

static void keccak_absorb_x4(keccakx4_state *ctxt,
                             uint32_t r,
                             const uint8_t *in0,
                             const uint8_t *in1,
                             const uint8_t *in2,
                             const uint8_t *in3,
                             size_t inlen,
                             uint8_t p)
{
    uint64_t *s = ctxt->lanes;

    while (inlen >= r)
    {

        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 0, in0, 0, r);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 1, in1, 0, r);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 2, in2, 0, r);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 3, in3, 0, r);

        KeccakF1600_StatePermute(s + KECCAK_CTX * 0);
        KeccakF1600_StatePermute(s + KECCAK_CTX * 1);
        KeccakF1600_StatePermute(s + KECCAK_CTX * 2);
        KeccakF1600_StatePermute(s + KECCAK_CTX * 3);

        in0 += r;
        in1 += r;
        in2 += r;
        in3 += r;
        inlen -= r;
    }

    if (inlen > 0)
    {
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 0, in0, 0, inlen);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 1, in1, 0, inlen);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 2, in2, 0, inlen);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 3, in3, 0, inlen);
    }

    if (inlen == r - 1)
    {
        p |= 128;
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 0, &p, inlen, 1);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 1, &p, inlen, 1);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 2, &p, inlen, 1);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 3, &p, inlen, 1);
    }
    else
    {
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 0, &p, inlen, 1);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 1, &p, inlen, 1);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 2, &p, inlen, 1);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 3, &p, inlen, 1);
        p = 128;
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 0, &p, r - 1, 1);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 1, &p, r - 1, 1);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 2, &p, r - 1, 1);
        KeccakF1600_StateXORBytes(s + KECCAK_CTX * 3, &p, r - 1, 1);
    }
}

static void keccak_squeezeblocks_x4(uint8_t *out0,
                                    uint8_t *out1,
                                    uint8_t *out2,
                                    uint8_t *out3,
                                    size_t nblocks,
                                    keccakx4_state *ctxt,
                                    uint32_t r)
{
    uint64_t *s = ctxt->lanes;

    while (nblocks > 0)
    {
        KeccakF1600_StatePermute(s + KECCAK_CTX * 0);
        KeccakF1600_StatePermute(s + KECCAK_CTX * 1);
        KeccakF1600_StatePermute(s + KECCAK_CTX * 2);
        KeccakF1600_StatePermute(s + KECCAK_CTX * 3);

        KeccakF1600_StateExtractBytes(s + KECCAK_CTX * 0, out0, 0, r);
        KeccakF1600_StateExtractBytes(s + KECCAK_CTX * 1, out1, 0, r);
        KeccakF1600_StateExtractBytes(s + KECCAK_CTX * 2, out2, 0, r);
        KeccakF1600_StateExtractBytes(s + KECCAK_CTX * 3, out3, 0, r);

        out0 += r;
        out1 += r;
        out2 += r;
        out3 += r;
        nblocks--;
    }
}

void shake128x4_absorb(shakex4_state *state,
                       const uint8_t *in0,
                       const uint8_t *in1,
                       const uint8_t *in2,
                       const uint8_t *in3,
                       size_t inlen)
{
    keccakx4_state *ctxt = shakex4_state_to_keccakx4(state);
    memset(ctxt, 0, sizeof(keccakx4_state));
    keccak_absorb_x4(ctxt, SHAKE128_RATE, in0, in1, in2, in3, inlen, 0x1F);
}

void shake256x4_absorb(shakex4_state *state,
                       const uint8_t *in0,
                       const uint8_t *in1,
                       const uint8_t *in2,
                       const uint8_t *in3,
                       size_t inlen)
{
    keccakx4_state *ctxt = shakex4_state_to_keccakx4(state);
    memset(ctxt, 0, sizeof(keccakx4_state));
    keccak_absorb_x4(ctxt, SHAKE256_RATE, in0, in1, in2, in3, inlen, 0x1F);
}


void shake128x4_squeezeblocks(uint8_t *out0,
                              uint8_t *out1,
                              uint8_t *out2,
                              uint8_t *out3,
                              size_t nblocks,
                              shakex4_state *state)
{
    keccakx4_state *ctxt = shakex4_state_to_keccakx4(state);
    keccak_squeezeblocks_x4(out0, out1, out2, out3, nblocks, ctxt, SHAKE128_RATE);
}

void shake256x4_squeezeblocks(uint8_t *out0,
                              uint8_t *out1,
                              uint8_t *out2,
                              uint8_t *out3,
                              size_t nblocks,
                              shakex4_state *state)
{
    keccakx4_state *ctxt = shakex4_state_to_keccakx4(state);
    keccak_squeezeblocks_x4(out0, out1, out2, out3, nblocks, ctxt, SHAKE256_RATE);
}

void shake256x4(uint8_t *out0,
                uint8_t *out1,
                uint8_t *out2,
                uint8_t *out3,
                size_t outlen,
                uint8_t *in0,
                uint8_t *in1,
                uint8_t *in2,
                uint8_t *in3,
                size_t inlen)
{
    shakex4_state statex;
    size_t nblocks = outlen/SHAKE256_RATE;
    uint8_t tmp[KECCAK_WAY][SHAKE256_RATE];

    shake256x4_absorb(&statex, in0, in1, in2, in3, inlen);
    shake256x4_squeezeblocks(out0, out1, out2, out3, nblocks, &statex);

    out0 += nblocks * SHAKE256_RATE;
    out1 += nblocks * SHAKE256_RATE;
    out2 += nblocks * SHAKE256_RATE;
    out3 += nblocks * SHAKE256_RATE;

    outlen -= nblocks * SHAKE256_RATE;

    if (outlen)
    {
        shake256x4_squeezeblocks(tmp[0], tmp[1], tmp[2], tmp[3], 1, &statex);
        memcpy(out0, tmp[0], outlen);
        memcpy(out1, tmp[1], outlen);
        memcpy(out2, tmp[2], outlen);
        memcpy(out3, tmp[3], outlen);
    }
}
