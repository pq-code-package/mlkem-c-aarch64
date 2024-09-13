// SPDX-License-Identifier: Apache-2.0

#ifndef CONFIG_H
#define CONFIG_H

#include "cpucap.h"

#if defined(MLKEM_USE_ASM)

#if defined(SYS_AARCH64)
#define MLKEM_USE_AARCH64_ASM
#endif /* SYS_AARCH64 */

#endif /* MLKEM_USE_ASM */
#endif /* CONFIG_H */
