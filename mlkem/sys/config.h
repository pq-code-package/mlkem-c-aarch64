/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CONFIG_H
#define CONFIG_H

#include "cpucap.h"

#if defined(MLKEM_USE_NATIVE)

#if defined(SYS_AARCH64)
#define MLKEM_USE_NATIVE_AARCH64
#endif /* SYS_AARCH64 */

#if defined(SYS_X86_64)
#define MLKEM_USE_NATIVE_X86_64
#endif /* SYS_X86_64 */

#endif /* MLKEM_USE_NATIVE */
#endif /* CONFIG_H */
