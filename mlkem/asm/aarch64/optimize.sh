#!/usr/bin/env sh
# SPDX-License-Identifier: Apache-2.0

set -e

TARGET_NAME="Cortex-A55"
TARGET=Arm_Cortex_A55

echo "* Base multiplication, ${TARGET_NAME}"

slothy-cli Arm_AArch64 $TARGET \
  poly_clean.S -o poly_opt.S \
  -r poly_reduce_asm_clean,poly_reduce_asm_opt \
  -l loop_start \
  -c sw_pipelining.enabled=true \
  -c inputs_are_outputs \
  -c reserved_regs="[x0--30,v10--v31,sp]" \
  -c sw_pipelining.minimize_overlapping=False \
  -c variable_size \
  -c constraints.stalls_first_attempt=64

echo " * Forward NTT, ${TARGET_NAME}"

slothy-cli Arm_AArch64 $TARGET \
  ntt_clean.S -o ntt_opt.S \
  -r ntt_asm_clean,ntt_asm_opt \
  -l layer123_start \
  -l layer4567_start \
  -c sw_pipelining.enabled=true \
  -c inputs_are_outputs \
  -c reserved_regs="[x18--30,sp]" \
  -c sw_pipelining.minimize_overlapping=False \
  -c variable_size \
  -c constraints.stalls_first_attempt=64

echo " * Inverse NTT, ${TARGET_NAME}"

slothy-cli Arm_AArch64 $TARGET \
  intt_clean.S -o intt_opt.S \
  -r intt_asm_clean,intt_asm_opt \
  -l layer123_start \
  -l layer4567_start \
  -c sw_pipelining.enabled=true \
  -c inputs_are_outputs \
  -c reserved_regs="[x18--30,sp]" \
  -c sw_pipelining.minimize_overlapping=False \
  -c variable_size \
  -c constraints.stalls_first_attempt=64
