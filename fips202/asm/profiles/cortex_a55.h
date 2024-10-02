// SPDX-License-Identifier: Apache-2.0

// FIPS202 assembly profile targeting Cortex-A55

#ifdef FIPS202_ASM_PROFILE_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define FIPS202_ASM_PROFILE_H

// On Cortex-A55, we use lazy rotation assembly for Keccak-x1,
// but no batched assembly implementation.
#define MLKEM_USE_FIPS202_X1_ASM
#define keccak_f1600_x1_asm keccak_f1600_x1_scalar_asm_opt

#endif /* FIPS202_ASM_PROFILE_H */
