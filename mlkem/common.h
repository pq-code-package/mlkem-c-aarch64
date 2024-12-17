/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLKEM_NATIVE_COMMON_H
#define MLKEM_NATIVE_COMMON_H

#if defined(MLKEM_NATIVE_CONFIG_FILE)
#include MLKEM_NATIVE_CONFIG_FILE
#endif /* MLKEM_NATIVE_CONFIG_FILE */

#include "params.h"
#include "sys.h"

/* Include backend metadata */
#if defined(MLKEM_USE_NATIVE)
#if defined(MLKEM_NATIVE_ARITH_BACKEND)
#include MLKEM_NATIVE_ARITH_BACKEND
#endif
#if defined(MLKEM_NATIVE_FIPS202_BACKEND)
#include MLKEM_NATIVE_FIPS202_BACKEND
#endif
#endif

/* This must come after the inclusion of the backend metadata
 * since the backend choice may be part of the namespace. */
#include "namespace.h"

#endif /* MLKEM_NATIVE_COMMON_H */
