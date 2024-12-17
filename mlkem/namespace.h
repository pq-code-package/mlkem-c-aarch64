/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLKEM_NATIVE_NAMESPACE_H
#define MLKEM_NATIVE_NAMESPACE_H

#if !defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#define MLKEM_NATIVE_ARITH_BACKEND_NAME C
#endif

/* Don't change parameters below this line */
#if (MLKEM_K == 2)
#define MLKEM_PARAM_NAME MLKEM512
#elif (MLKEM_K == 3)
#define MLKEM_PARAM_NAME MLKEM768
#elif (MLKEM_K == 4)
#define MLKEM_PARAM_NAME MLKEM1024
#else
#error "MLKEM_K must be in {2,3,4}"
#endif

#define ___MLKEM_DEFAULT_NAMESPACE(x1, x2, x3, x4) x1##_##x2##_##x3##_##x4
#define __MLKEM_DEFAULT_NAMESPACE(x1, x2, x3, x4) \
  ___MLKEM_DEFAULT_NAMESPACE(x1, x2, x3, x4)

/*
 * NAMESPACE is PQCP_MLKEM_NATIVE_<PARAM_NAME>_<BACKEND>_
 * e.g., PQCP_MLKEM_NATIVE_MLKEM512_AARCH64_OPT_
 */
#define MLKEM_DEFAULT_NAMESPACE(s)                               \
  __MLKEM_DEFAULT_NAMESPACE(PQCP_MLKEM_NATIVE, MLKEM_PARAM_NAME, \
                            MLKEM_NATIVE_ARITH_BACKEND_NAME, s)
#define _MLKEM_DEFAULT_NAMESPACE(s)                               \
  __MLKEM_DEFAULT_NAMESPACE(_PQCP_MLKEM_NATIVE, MLKEM_PARAM_NAME, \
                            MLKEM_NATIVE_ARITH_BACKEND_NAME, s)

#if !defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#define MLKEM_NATIVE_FIPS202_BACKEND_NAME C
#endif

#define ___FIPS202_DEFAULT_NAMESPACE(x1, x2, x3) x1##_##x2##_##x3
#define __FIPS202_DEFAULT_NAMESPACE(x1, x2, x3) \
  ___FIPS202_DEFAULT_NAMESPACE(x1, x2, x3)

/*
 * NAMESPACE is PQCP_MLKEM_NATIVE_FIPS202_<BACKEND>_
 * e.g., PQCP_MLKEM_NATIVE_FIPS202_X86_64_XKCP_
 */
#define FIPS202_DEFAULT_NAMESPACE(s)                     \
  __FIPS202_DEFAULT_NAMESPACE(PQCP_MLKEM_NATIVE_FIPS202, \
                              MLKEM_NATIVE_FIPS202_BACKEND_NAME, s)
#define _FIPS202_DEFAULT_NAMESPACE(s)                     \
  __FIPS202_DEFAULT_NAMESPACE(_PQCP_MLKEM_NATIVE_FIPS202, \
                              MLKEM_NATIVE_FIPS202_BACKEND_NAME, s)

#endif /* MLKEM_NATIVE_NAMESPACE_H */
