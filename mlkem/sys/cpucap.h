// SPDX-License-Identifier: Apache-2.0

#ifndef CPUCAP_H
#define CPUCAP_H

/* Check if we're running on an AArch64 system. _M_ARM64 is set by MSVC. */
#if defined(__AARCH64EL__) || defined(_M_ARM64)
#define SYS_AARCH64
#endif

/* If FORCE_AARCH64 is set, assert that we're indeed on an AArch64 system. */
#if defined(FORCE_AARCH64) && !defined(SYS_AARCH64)
#error "FORCE_AARCH64 is set, but we don't seem to be on an AArch64 system."
#endif

#endif
