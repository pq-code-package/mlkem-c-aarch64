// SPDX-License-Identifier: Apache-2.0
#ifndef COMMON_H
#define COMMON_H

#define DEFAULT_ALIGN 32
#define ALIGN __attribute__((aligned(DEFAULT_ALIGN)))
#define ALWAYS_INLINE __attribute__((always_inline))

#define MLKEM_CONCAT_(left, right) left##right
#define MLKEM_CONCAT(left, right) MLKEM_CONCAT_(left, right)

#endif
