// SPDX-License-Identifier: Apache-2.0
#ifndef REJ_UNIFORM_ASM
#define REJ_UNIFORM_ASM

unsigned int rej_uniform_asm(int16_t *r,
                             const uint8_t *buf,
                             unsigned int *buf_consumed,
                             unsigned int buflen,
                             unsigned int len,
                             const uint8_t idx[256][16],
                             const uint16_t bits[8]);

#endif
