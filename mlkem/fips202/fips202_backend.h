/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifdef MLKEM_NATIVE_FIPS202_IMPL_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define MLKEM_NATIVE_FIPS202_IMPL_H

/* Include to enforce consistency of API and implementation */
#include "native/api.h"

#if defined(MLKEM_NATIVE_FIPS202_BACKEND_IMPL)
#include MLKEM_NATIVE_FIPS202_BACKEND_IMPL
#endif

#endif /* MLKEM_NATIVE_FIPS202_IMPL_H */
