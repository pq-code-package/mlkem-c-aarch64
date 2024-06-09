// SPDX-License-Identifier: Apache-2.0
#ifndef POLY_ASM_H
#define POLY_ASM_H

#include "params.h"

void poly_frommsg_asm(int16_t coeffs[KYBER_N],
                      const uint8_t msg[KYBER_INDCPA_MSGBYTES],
                      const uint16_t bits[8]);

void poly_tomsg_asm(uint8_t msg[KYBER_INDCPA_MSGBYTES],
                    const int16_t coeffs[KYBER_N],
                    const uint16_t position[8]);

#endif
