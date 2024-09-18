// SPDX-License-Identifier: Apache-2.0
#ifndef ASM_H
#define ASM_H

#include <stdint.h>
#include "params.h"
#include "config.h"

#ifdef MLKEM_USE_AARCH64_ASM
void keccak_f1600_x1_scalar_slothy_opt_a55(uint64_t *state);
void keccak_f1600_x2_v84a_asm_clean(uint64_t *state);

#define keccak_f1600_x1_asm keccak_f1600_x1_scalar_slothy_opt_a55
#define keccak_f1600_x2_asm keccak_f1600_x2_v84a_asm_clean
#endif /* MLKEM_USE_AARCH64_ASM */


#endif
