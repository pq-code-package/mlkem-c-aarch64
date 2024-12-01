#!/usr/bin/env python3
# Copyright (c) 2024 The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0

import subprocess
import argparse
import math
import os

modulus = 3329
root_of_unity = 17
montgomery_factor = pow(2, 16, modulus)

# This file re-generated auto-generated source files in mlkem-native.
#
# It currently covers:
# - zeta values for the reference NTT and invNTT

def gen_header():
    yield "// Copyright (c) 2024 The mlkem-native project authors"
    yield "// SPDX-License-Identifier: Apache-2.0"
    yield ""
    yield "// WARNING: This file is auto-generated from scripts/autogenerate_files.py"
    yield "//          Do not modify it directly."
    yield ""

def update_file(filename, content, dry_run=False):

    # Format content
    p = subprocess.run(["clang-format"], capture_output=True, input=content, text=True)
    if p.returncode != 0:
        print(f"Failed to auto-format autogenerated code (clang-format return code {p.returncode}")
        exit(1)
    content = p.stdout

    if dry_run is False:
        with open(filename, "w+") as f:
            f.write(content)
    else:
        if os.path.exists(filename) is False:
            print(f"Autogenerated file {filename} does not exist")
            exit(1)
        with open(filename, "r") as f:
            current_content = f.read()
        if current_content != content:
            print(f"Autogenerated file {filename} needs updating. Have you called scripts/autogenerated.py?")
            exit(1)

def bitreverse(i,n):
    r = 0
    for _ in range(n):
        r = 2*r + (i & 1)
        i >>= 1
    return r

def signed_reduce(a):
    """Return signed canonical representative of a mod b"""
    c = a % modulus
    if c >= modulus / 2:
        c -= modulus
    return c

def prepare_root_for_montmul(root):
    """Takes a constant that the code needs to Montgomery-multiply with,
    and returns the pair of (a) the signed canonical representative of its
    Montgomery form, (b) the twisted constant used in the low-mul part of
    the Montgomery multiplication."""

    # Convert to Montgomery form and pick canonical signed representative
    root = signed_reduce(root * montgomery_factor)
    root_twisted = signed_reduce_u16(root * pow(modulus, -1, 2**16))
    return root, root_twisted

def prepare_root_for_barrett(root, even=True):
    """Takes a constant that the code needs to Barrett-multiply with,
    and returns the pair of (a) its signed canonical form, (b) the
    twisted constant used in the high-mul part of the Barrett multiplication."""

    # Signed canonical reduction
    root = signed_reduce(root)

    def round_to_suitable(t):
        if even is True:
            rt = round(t)
            if rt % 2 == 0:
                return rt
            # Make sure to pick a rounding target
            # that's <= 1 away from x in absolute value.
            if rt <= t:
                return rt + 1
            return rt - 1
        else:
            return math.floor(t)

    root_twisted = round_to_suitable((root * 2**16) / modulus)

    if even is True:
        root_twisted = root_twisted // 2

    return root, root_twisted

def gen_c_zetas(twisted=False):
    """Generate source and header file for zeta values used in
    the reference NTT and invNTT"""

    # The zeta values are the powers of the chosen root of unity (17),
    # converted to Montgomery form.

    zeta = []
    for i in range(128):
        root, root_twisted = prepare_root_for_barrett(pow(root_of_unity, i, modulus), even=False)
        if twisted is False:
            zeta.append(root)
        else:
            zeta.append(root_twisted)

    # The source code stores the zeta table in bit reversed form
    yield from (zeta[bitreverse(i,7)] for i in range(128))

def gen_c_zeta_file(dry_run=False):
    def gen():
        yield from gen_header()
        yield "#include \"ntt.h\""
        yield ""
        yield "// Table of zeta values used in the reference NTT and inverse NTT."
        yield "// See autogenerate_files.py for details."
        yield "const int16_t zetas[128] = {"
        yield from map(lambda t: str(t) + ",", gen_c_zetas())
        yield "};"
        yield ""
        yield "const int16_t zetas_twisted[128] = {"
        yield from map(lambda t: str(t) + ",", gen_c_zetas(twisted=True))
        yield "};"
        yield ""
    update_file("mlkem/zetas.c", '\n'.join(gen()), dry_run=dry_run)

def gen_aarch64_root_of_unity_for_block(layer, block, inv=False):
    # We are computing a negacyclic NTT; the twiddles needed here is
    # the second half of the twiddles for a cyclic NTT of twice the size.
    log = bitreverse(pow(2,layer) + block, 7)
    if inv is True:
        log = -log
    root, root_twisted = prepare_root_for_barrett(pow(root_of_unity, log, modulus))
    return root, root_twisted

def gen_aarch64_fwd_ntt_zetas_layer01234():
    # Layers 0,1,2 are merged
    yield from gen_aarch64_root_of_unity_for_block(0,0)
    yield from gen_aarch64_root_of_unity_for_block(1,0)
    yield from gen_aarch64_root_of_unity_for_block(1,1)
    yield from gen_aarch64_root_of_unity_for_block(2,0)
    yield from gen_aarch64_root_of_unity_for_block(2,1)
    yield from gen_aarch64_root_of_unity_for_block(2,2)
    yield from gen_aarch64_root_of_unity_for_block(2,3)
    yield from (0,0) # Padding

    # Layers 3,4,5,6 are merged, but we emit roots for 3,4
    # in separate arrays than those for 5,6
    for block in range(8): # There are 8 blocks in Layer 4
        yield from gen_aarch64_root_of_unity_for_block(3,block)
        yield from gen_aarch64_root_of_unity_for_block(4,2*block+0)
        yield from gen_aarch64_root_of_unity_for_block(4,2*block+1)
        yield from (0,0) # Padding

def gen_aarch64_fwd_ntt_zetas_layer56():
    # Layers 3,4,5,6 are merged, but we emit roots for 3,4
    # in separate arrays than those for 5,6
    for block in range(8):
        def double_ith(t, i):
            yield from (t[i], t[i])
        # Ordering of blocks is adjusted to suit the transposed internal
        # presentation of the data
        for i in range(2):
            yield from double_ith(gen_aarch64_root_of_unity_for_block(5,4*block+0), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(5,4*block+1), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(5,4*block+2), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(5,4*block+3), i)
        for i in range(2):
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+0), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+2), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+4), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+6), i)
        for i in range(2):
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+1), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+3), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+5), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+7), i)

def gen_aarch64_inv_ntt_zetas_layer01234():
    # Layers 3,4,5,6 are merged, but we emit roots for 3,4
    # in separate arrays than those for 5,6
    for block in range(8): # There are 8 blocks in Layer 4
        yield from gen_aarch64_root_of_unity_for_block(3,block,inv=True)
        yield from gen_aarch64_root_of_unity_for_block(4,2*block+0,inv=True)
        yield from gen_aarch64_root_of_unity_for_block(4,2*block+1,inv=True)
        yield from (0,0) # Padding

    # Layers 0,1,2 are merged
    yield from gen_aarch64_root_of_unity_for_block(0,0,inv=True)
    yield from gen_aarch64_root_of_unity_for_block(1,0,inv=True)
    yield from gen_aarch64_root_of_unity_for_block(1,1,inv=True)
    yield from gen_aarch64_root_of_unity_for_block(2,0,inv=True)
    yield from gen_aarch64_root_of_unity_for_block(2,1,inv=True)
    yield from gen_aarch64_root_of_unity_for_block(2,2,inv=True)
    yield from gen_aarch64_root_of_unity_for_block(2,3,inv=True)
    yield from (0,0) # Padding

def gen_aarch64_inv_ntt_zetas_layer56():
    # Layers 3,4,5,6 are merged, but we emit roots for 3,4
    # in separate arrays than those for 5,6
    for block in range(8):
        def double_ith(t, i):
            yield from (t[i], t[i])
        # Ordering of blocks is adjusted to suit the transposed internal
        # presentation of the data
        for i in range(2):
            yield from double_ith(gen_aarch64_root_of_unity_for_block(5,4*block+0, inv=True), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(5,4*block+1, inv=True), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(5,4*block+2, inv=True), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(5,4*block+3, inv=True), i)
        for i in range(2):
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+0, inv=True), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+2, inv=True), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+4, inv=True), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+6, inv=True), i)
        for i in range(2):
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+1, inv=True), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+3, inv=True), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+5, inv=True), i)
            yield from double_ith(gen_aarch64_root_of_unity_for_block(6,8*block+7, inv=True), i)

def gen_aarch64_mulcache_twiddles():
    for idx in range(64):
        root = pow(root_of_unity, bitreverse(64+idx,7), modulus)
        yield prepare_root_for_barrett(root)[0]
        yield prepare_root_for_barrett(-root)[0]

def gen_aarch64_mulcache_twiddles_twisted():
    for idx in range(64):
        root = pow(root_of_unity, bitreverse(64+idx,7), modulus)
        yield prepare_root_for_barrett(root)[1]
        yield prepare_root_for_barrett(-root)[1]

def gen_aarch64_fwd_ntt_zeta_file(dry_run=False):
    def gen():
        yield from gen_header()
        yield "#include \"arith_native_aarch64.h\""
        yield ""
        yield "#ifdef MLKEM_USE_NATIVE_AARCH64"
        yield ""
        yield "// Table of zeta values used in the AArch64 forward NTT"
        yield "// See autogenerate_files.py for details."
        yield "const int16_t aarch64_ntt_zetas_layer01234[] = {"
        yield from map(lambda t: str(t) + ",", gen_aarch64_fwd_ntt_zetas_layer01234())
        yield "};"
        yield ""
        yield "const int16_t aarch64_ntt_zetas_layer56[] = {"
        yield from map(lambda t: str(t) + ",", gen_aarch64_fwd_ntt_zetas_layer56())
        yield "};"
        yield ""
        yield "const int16_t aarch64_invntt_zetas_layer01234[] = {"
        yield from map(lambda t: str(t) + ",", gen_aarch64_inv_ntt_zetas_layer01234())
        yield "};"
        yield ""
        yield "const int16_t aarch64_invntt_zetas_layer56[] = {"
        yield from map(lambda t: str(t) + ",", gen_aarch64_inv_ntt_zetas_layer56())
        yield "};"
        yield ""
        yield "const int16_t aarch64_zetas_mulcache_native[] = {"
        yield from map(lambda t: str(t) + ",", gen_aarch64_mulcache_twiddles())
        yield "};"
        yield ""
        yield "const int16_t aarch64_zetas_mulcache_twisted_native[] = {"
        yield from map(lambda t: str(t) + ",", gen_aarch64_mulcache_twiddles_twisted())
        yield "};"
        yield ""
        yield "#else /* MLKEM_USE_NATIVE_AARCH64 */"
        yield "// Dummy declaration for compilers disliking empty compilation units"
        yield "int empty_cu_aarch64_zetas;"
        yield "#endif /* MLKEM_USE_NATIVE_AARCH64 */"
        yield ""
    update_file("mlkem/native/aarch64/aarch64_zetas.c", '\n'.join(gen()), dry_run=dry_run)

def signed_reduce_u16(x):
    x = x % 2**16
    if x >= 2**15:
        x -= 2**16
    return x

def gen_avx2_root_of_unity_for_block(layer, block, inv=False):
    # We are computing a negacyclic NTT; the twiddles needed here is
    # the second half of the twiddles for a cyclic NTT of twice the size.
    log = bitreverse(pow(2,layer) + block, 7)
    if inv is True:
        log = -log
    root, root_twisted = prepare_root_for_montmul(pow(root_of_unity, log, modulus))
    return root, root_twisted

def gen_avx2_fwd_ntt_zetas():

    def gen_twiddles(layer, block, repeat):
        """Generates twisted twiddle, then twiddle, for given layer and block.
        Repeat both the given number of times."""
        root, root_twisted = gen_avx2_root_of_unity_for_block(layer, block)
        return [root]*repeat, [root_twisted]*repeat

    def gen_twiddles_many(layer, block_base, block_offsets, repeat):
        """Generates twisted twiddles, then twiddles, of each (layer, block_base + i)
        pair for i in block_offsets. Each twiddle is repeated `repeat` times."""
        root_pairs = list(map(lambda x: gen_twiddles(layer, block_base + x, repeat), block_offsets))
        yield from (r for l in root_pairs for r in l[1])
        yield from (r for l in root_pairs for r in l[0])

    # Layers 0 twiddle
    yield from gen_twiddles_many(0, 0, range(1), 4)
    # Padding so that the subsequent twiddles are 16-byte aligned
    yield from [0]*8

    # Layer 1-6 twiddles, separated by whether they belong to the upper or lower half
    for i in range(2):
        yield from gen_twiddles_many(1, i*(2**0), range(1), 16)
        yield from gen_twiddles_many(2, i*(2**1), range(2), 8)
        yield from gen_twiddles_many(3, i*(2**2), range(4), 4)
        yield from gen_twiddles_many(4, i*(2**3), range(8), 2)
        yield from gen_twiddles_many(5, i*(2**4), range(16), 1)
        yield from gen_twiddles_many(6, i*(2**5), range(0,32,2), 1)
        yield from gen_twiddles_many(6, i*(2**5), range(1,32,2), 1)

def gen_avx2_fwd_ntt_zeta_file(dry_run=False):
    def gen():
        yield from gen_header()
        yield "// Table of zeta values used in the AVX2 NTTs"
        yield "// See autogenerate_files.py for details."
        yield ""
        yield from map(lambda t: str(t) + ",", gen_avx2_fwd_ntt_zetas())
        yield ""
    update_file("mlkem/native/x86_64/x86_64_zetas.i", '\n'.join(gen()), dry_run=dry_run)

def _main():
    parser = argparse.ArgumentParser(
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--dry-run", default=False, action='store_true')

    args = parser.parse_args()
    gen_c_zeta_file(args.dry_run)
    gen_aarch64_fwd_ntt_zeta_file(args.dry_run)
    gen_avx2_fwd_ntt_zeta_file(args.dry_run)

if __name__ == "__main__":
    _main()
