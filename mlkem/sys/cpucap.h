// SPDX-License-Identifier: Apache-2.0

#ifndef CPUCAP_H
#define CPUCAP_H

/* Check if we're running on an AArch64 system. _M_ARM64 is set by MSVC. */
#if defined(__AARCH64EL__) || defined(_M_ARM64)
#define SYS_AARCH64
#endif

#if defined(__x86_64__)
#define SYS_X86_64
#if defined(__AVX2__)
#define SYS_X86_64_AVX2
#endif
#endif /* __x86_64__ */

/* Check endianness */
#if defined(__BYTE_ORDER__)

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define SYS_LITTLE_ENDIAN
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#define SYS_BIG_ENDIAN
#else /* __BYTE_ORER__ */
#error "__BYTE_ORDER__ defined, but don't recognize value."
#endif /* __BYTE_ORER__ */
#endif /* !defined(__BYTE_ORER__) */

/* If FORCE_AARCH64 is set, assert that we're indeed on an AArch64 system. */
#if defined(FORCE_AARCH64) && !defined(SYS_AARCH64)
#error "FORCE_AARCH64 is set, but we don't seem to be on an AArch64 system."
#endif

/* If FORCE_X86_64 is set, assert that we're indeed on an X86_64 system. */
#if defined(FORCE_X86_64) && !defined(SYS_X86_64)
#error "FORCE_X86_64 is set, but we don't seem to be on an X86_64 system."
#endif

#endif
