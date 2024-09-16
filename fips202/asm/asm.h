// SPDX-License-Identifier: Apache-2.0
#ifndef ASM_H
#define ASM_H

#include <stdint.h>
#include "params.h"
#include "config.h"

#ifdef MLKEM_USE_AARCH64_ASM
void keccak_f1600_x1_scalar_pre_opt(uint64_t *state);
#endif /* MLKEM_USE_AARCH64_ASM */

#endif
