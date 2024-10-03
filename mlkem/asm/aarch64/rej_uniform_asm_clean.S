// SPDX-License-Identifier: Apache-2.0

/*************************************************
* Name:        rej_uniform_asm
*
* Description: Full SIMD lane, run rejection sampling on uniform random bytes to generate
*              uniform random integers mod q
*
* Arguments:   - int16_t *r:          pointer to output buffer
*              - unsigned int len:    requested number of 16-bit integers
*                                     (uniform mod q)
*              - const uint8_t *buf:  pointer to input buffer
*                                     (assumed to be uniform random bytes)
*              - unsigned int buflen: length of input buffer in bytes
*              - unsigned int *consumed: the length of consumed buffer
* Returns number of sampled 16-bit integers (at most len)
***************************************************/

#include "config.h"
#include "params.h"
#if defined(MLKEM_USE_AARCH64_ASM)

// Needed to provide ASM_LOAD directive
#include "common.i"

.data
table_data:
    .byte -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1 // 0
    .byte 0, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 1
    .byte 2, 3, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 2
    .byte 0, 1, 2, 3, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 3
    .byte 4, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 4
    .byte 0, 1, 4, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 5
    .byte 2, 3, 4, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 6
    .byte 0, 1, 2, 3, 4, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1       // 7
    .byte 6, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 8
    .byte 0, 1, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 9
    .byte 2, 3, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 10
    .byte 0, 1, 2, 3, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1       // 11
    .byte 4, 5, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 12
    .byte 0, 1, 4, 5, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1       // 13
    .byte 2, 3, 4, 5, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1       // 14
    .byte 0, 1, 2, 3, 4, 5, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1         // 15
    .byte 8, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 16
    .byte 0, 1, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 17
    .byte 2, 3, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 18
    .byte 0, 1, 2, 3, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1       // 19
    .byte 4, 5, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 20
    .byte 0, 1, 4, 5, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1       // 21
    .byte 2, 3, 4, 5, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1       // 22
    .byte 0, 1, 2, 3, 4, 5, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1         // 23
    .byte 6, 7, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 24
    .byte 0, 1, 6, 7, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1       // 25
    .byte 2, 3, 6, 7, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1       // 26
    .byte 0, 1, 2, 3, 6, 7, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1         // 27
    .byte 4, 5, 6, 7, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1       // 28
    .byte 0, 1, 4, 5, 6, 7, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1         // 29
    .byte 2, 3, 4, 5, 6, 7, 8, 9, -1, -1, -1, -1, -1, -1, -1, -1         // 30
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, -1, -1, -1, -1, -1, -1           // 31
    .byte 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1 // 32
    .byte 0, 1, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 33
    .byte 2, 3, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 34
    .byte 0, 1, 2, 3, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 35
    .byte 4, 5, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 36
    .byte 0, 1, 4, 5, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 37
    .byte 2, 3, 4, 5, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 38
    .byte 0, 1, 2, 3, 4, 5, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1       // 39
    .byte 6, 7, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 40
    .byte 0, 1, 6, 7, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 41
    .byte 2, 3, 6, 7, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 42
    .byte 0, 1, 2, 3, 6, 7, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1       // 43
    .byte 4, 5, 6, 7, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 44
    .byte 0, 1, 4, 5, 6, 7, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1       // 45
    .byte 2, 3, 4, 5, 6, 7, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1       // 46
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 10, 11, -1, -1, -1, -1, -1, -1         // 47
    .byte 8, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 48
    .byte 0, 1, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 49
    .byte 2, 3, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 50
    .byte 0, 1, 2, 3, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1       // 51
    .byte 4, 5, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 52
    .byte 0, 1, 4, 5, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1       // 53
    .byte 2, 3, 4, 5, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1       // 54
    .byte 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1         // 55
    .byte 6, 7, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 56
    .byte 0, 1, 6, 7, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1       // 57
    .byte 2, 3, 6, 7, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1       // 58
    .byte 0, 1, 2, 3, 6, 7, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1         // 59
    .byte 4, 5, 6, 7, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1, -1       // 60
    .byte 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1         // 61
    .byte 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, -1, -1, -1, -1, -1, -1         // 62
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, -1, -1, -1, -1           // 63
    .byte 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1 // 64
    .byte 0, 1, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 65
    .byte 2, 3, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 66
    .byte 0, 1, 2, 3, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 67
    .byte 4, 5, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 68
    .byte 0, 1, 4, 5, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 69
    .byte 2, 3, 4, 5, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 70
    .byte 0, 1, 2, 3, 4, 5, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1       // 71
    .byte 6, 7, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 72
    .byte 0, 1, 6, 7, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 73
    .byte 2, 3, 6, 7, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 74
    .byte 0, 1, 2, 3, 6, 7, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1       // 75
    .byte 4, 5, 6, 7, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 76
    .byte 0, 1, 4, 5, 6, 7, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1       // 77
    .byte 2, 3, 4, 5, 6, 7, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1       // 78
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 12, 13, -1, -1, -1, -1, -1, -1         // 79
    .byte 8, 9, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 80
    .byte 0, 1, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 81
    .byte 2, 3, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 82
    .byte 0, 1, 2, 3, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1       // 83
    .byte 4, 5, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 84
    .byte 0, 1, 4, 5, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1       // 85
    .byte 2, 3, 4, 5, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1       // 86
    .byte 0, 1, 2, 3, 4, 5, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1         // 87
    .byte 6, 7, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 88
    .byte 0, 1, 6, 7, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1       // 89
    .byte 2, 3, 6, 7, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1       // 90
    .byte 0, 1, 2, 3, 6, 7, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1         // 91
    .byte 4, 5, 6, 7, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1       // 92
    .byte 0, 1, 4, 5, 6, 7, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1         // 93
    .byte 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, -1, -1, -1, -1, -1, -1         // 94
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, -1, -1, -1, -1           // 95
    .byte 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1 // 96
    .byte 0, 1, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 97
    .byte 2, 3, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 98
    .byte 0, 1, 2, 3, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1     // 99
    .byte 4, 5, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 100
    .byte 0, 1, 4, 5, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1     // 101
    .byte 2, 3, 4, 5, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1     // 102
    .byte 0, 1, 2, 3, 4, 5, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1       // 103
    .byte 6, 7, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 104
    .byte 0, 1, 6, 7, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1     // 105
    .byte 2, 3, 6, 7, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1     // 106
    .byte 0, 1, 2, 3, 6, 7, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1       // 107
    .byte 4, 5, 6, 7, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1     // 108
    .byte 0, 1, 4, 5, 6, 7, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1       // 109
    .byte 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1       // 110
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, -1, -1, -1, -1         // 111
    .byte 8, 9, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 112
    .byte 0, 1, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1     // 113
    .byte 2, 3, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1     // 114
    .byte 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1       // 115
    .byte 4, 5, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1     // 116
    .byte 0, 1, 4, 5, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1       // 117
    .byte 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1       // 118
    .byte 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1         // 119
    .byte 6, 7, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1, -1, -1     // 120
    .byte 0, 1, 6, 7, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1       // 121
    .byte 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1       // 122
    .byte 0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1         // 123
    .byte 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1, -1, -1       // 124
    .byte 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1         // 125
    .byte 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, -1, -1, -1, -1         // 126
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, -1, -1           // 127
    .byte 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1 // 128
    .byte 0, 1, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 129
    .byte 2, 3, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 130
    .byte 0, 1, 2, 3, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 131
    .byte 4, 5, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 132
    .byte 0, 1, 4, 5, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 133
    .byte 2, 3, 4, 5, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 134
    .byte 0, 1, 2, 3, 4, 5, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1       // 135
    .byte 6, 7, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 136
    .byte 0, 1, 6, 7, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 137
    .byte 2, 3, 6, 7, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 138
    .byte 0, 1, 2, 3, 6, 7, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1       // 139
    .byte 4, 5, 6, 7, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 140
    .byte 0, 1, 4, 5, 6, 7, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1       // 141
    .byte 2, 3, 4, 5, 6, 7, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1       // 142
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 14, 15, -1, -1, -1, -1, -1, -1         // 143
    .byte 8, 9, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 144
    .byte 0, 1, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 145
    .byte 2, 3, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 146
    .byte 0, 1, 2, 3, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1       // 147
    .byte 4, 5, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 148
    .byte 0, 1, 4, 5, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1       // 149
    .byte 2, 3, 4, 5, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1       // 150
    .byte 0, 1, 2, 3, 4, 5, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1         // 151
    .byte 6, 7, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1     // 152
    .byte 0, 1, 6, 7, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1       // 153
    .byte 2, 3, 6, 7, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1       // 154
    .byte 0, 1, 2, 3, 6, 7, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1         // 155
    .byte 4, 5, 6, 7, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1       // 156
    .byte 0, 1, 4, 5, 6, 7, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1         // 157
    .byte 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, -1, -1, -1, -1, -1, -1         // 158
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, -1, -1, -1, -1           // 159
    .byte 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1 // 160
    .byte 0, 1, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 161
    .byte 2, 3, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 162
    .byte 0, 1, 2, 3, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 163
    .byte 4, 5, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 164
    .byte 0, 1, 4, 5, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 165
    .byte 2, 3, 4, 5, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 166
    .byte 0, 1, 2, 3, 4, 5, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1       // 167
    .byte 6, 7, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 168
    .byte 0, 1, 6, 7, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 169
    .byte 2, 3, 6, 7, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 170
    .byte 0, 1, 2, 3, 6, 7, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1       // 171
    .byte 4, 5, 6, 7, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 172
    .byte 0, 1, 4, 5, 6, 7, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1       // 173
    .byte 2, 3, 4, 5, 6, 7, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1       // 174
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 14, 15, -1, -1, -1, -1         // 175
    .byte 8, 9, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 176
    .byte 0, 1, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 177
    .byte 2, 3, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 178
    .byte 0, 1, 2, 3, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1       // 179
    .byte 4, 5, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 180
    .byte 0, 1, 4, 5, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1       // 181
    .byte 2, 3, 4, 5, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1       // 182
    .byte 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1         // 183
    .byte 6, 7, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 184
    .byte 0, 1, 6, 7, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1       // 185
    .byte 2, 3, 6, 7, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1       // 186
    .byte 0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1         // 187
    .byte 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1, -1, -1       // 188
    .byte 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1         // 189
    .byte 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, -1, -1, -1, -1         // 190
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, -1, -1           // 191
    .byte 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1 // 192
    .byte 0, 1, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 193
    .byte 2, 3, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 194
    .byte 0, 1, 2, 3, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 195
    .byte 4, 5, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 196
    .byte 0, 1, 4, 5, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 197
    .byte 2, 3, 4, 5, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 198
    .byte 0, 1, 2, 3, 4, 5, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1       // 199
    .byte 6, 7, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 200
    .byte 0, 1, 6, 7, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 201
    .byte 2, 3, 6, 7, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 202
    .byte 0, 1, 2, 3, 6, 7, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1       // 203
    .byte 4, 5, 6, 7, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 204
    .byte 0, 1, 4, 5, 6, 7, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1       // 205
    .byte 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1       // 206
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, -1, -1, -1, -1         // 207
    .byte 8, 9, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1   // 208
    .byte 0, 1, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 209
    .byte 2, 3, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 210
    .byte 0, 1, 2, 3, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1       // 211
    .byte 4, 5, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 212
    .byte 0, 1, 4, 5, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1       // 213
    .byte 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1       // 214
    .byte 0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1         // 215
    .byte 6, 7, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1     // 216
    .byte 0, 1, 6, 7, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1       // 217
    .byte 2, 3, 6, 7, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1       // 218
    .byte 0, 1, 2, 3, 6, 7, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1         // 219
    .byte 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1       // 220
    .byte 0, 1, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1         // 221
    .byte 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, -1, -1, -1, -1         // 222
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, -1, -1           // 223
    .byte 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1 // 224
    .byte 0, 1, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1   // 225
    .byte 2, 3, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1   // 226
    .byte 0, 1, 2, 3, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1     // 227
    .byte 4, 5, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1   // 228
    .byte 0, 1, 4, 5, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1     // 229
    .byte 2, 3, 4, 5, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1     // 230
    .byte 0, 1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1       // 231
    .byte 6, 7, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1   // 232
    .byte 0, 1, 6, 7, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1     // 233
    .byte 2, 3, 6, 7, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1     // 234
    .byte 0, 1, 2, 3, 6, 7, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1       // 235
    .byte 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1     // 236
    .byte 0, 1, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1       // 237
    .byte 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1       // 238
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, -1, -1         // 239
    .byte 8, 9, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1   // 240
    .byte 0, 1, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1     // 241
    .byte 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1     // 242
    .byte 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1       // 243
    .byte 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1     // 244
    .byte 0, 1, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1       // 245
    .byte 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1       // 246
    .byte 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1         // 247
    .byte 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1     // 248
    .byte 0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1       // 249
    .byte 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1       // 250
    .byte 0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1         // 251
    .byte 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1       // 252
    .byte 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1         // 253
    .byte 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, -1, -1         // 254
    .byte 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15           // 255

bit_table_data:
    .short 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80

/* Return multiple of 48: (n/48) * 48 */
.macro round_48x    dst, src
    mov     w8, #48
    udiv    \dst, \src, w8
    mul     \dst, \dst, w8
.endm

// Maximum size of int16 output array
#define REJ_UNIFORM_ASM_MAX_OUTPUT KYBER_N

#define STACK_LOCS 2
#define STACK_SIZE_TMP_OUTPUT (2*REJ_UNIFORM_ASM_MAX_OUTPUT + 64) // We overwrite by max. 64 bytes in loop48
#define STACK_SIZE_LOCS (8*STACK_LOCS)
#define STACK_SIZE_GPRS (6 * 8)
#define STACK_OFFSET_GPRS 0
#define STACK_OFFSET_LOCS STACK_SIZE_GPRS
#define STACK_OFFSET_TMP_OUTPUT (STACK_SIZE_LOCS + STACK_SIZE_GPRS)
#define STACK_SIZE (STACK_SIZE_TMP_OUTPUT + STACK_SIZE_LOCS + STACK_SIZE_GPRS)

#define STACK_OFFSET_RESULT (STACK_OFFSET_LOCS)

.macro push_stack
        sub sp, sp, #STACK_SIZE
.endm

.macro pop_stack
        add sp, sp, #STACK_SIZE
.endm

.macro save_gprs
    str     x8,       [sp, #(STACK_OFFSET_GPRS + 0)]
    stp     x16, x17, [sp, #(STACK_OFFSET_GPRS + 16)]
    stp     x29, x30, [sp, #(STACK_OFFSET_GPRS + 32)]
.endm

.macro restore_gprs
    ldr     x8,       [sp, #(STACK_OFFSET_GPRS + 0)]
    ldp     x16, x17, [sp, #(STACK_OFFSET_GPRS + 16)]
    ldp     x29, x30, [sp, #(STACK_OFFSET_GPRS + 32)]
.endm

    /* Input registers */
    output                      .req x0
    buf                         .req x2
    buf_consumed                .req x3
    buflen                      .req w4
    len                         .req x1
    lenw                        .req w1
    table_idx                   .req x5
    bit_table                   .req x6

    /* Output registers */
    output_tmp                  .req x11
    output_tmp_base             .req x16

    /* Temporary registers */
    tmp                         .req w8
    count                       .req w8
    bound                       .req w9
    minw                        .req w8
    min                         .req x8
    iterw                       .req w10
    iter                        .req x10

    rec_idx_0                   .req w12
    rec_idx_1                   .req w13
    rec_idx_2                   .req w14
    rec_idx_3                   .req w15

    ctr0                        .req w12
    ctr1                        .req w13
    ctr2                        .req w14
    ctr3                        .req w15

    /* Vector registers */

    buf0                        .req v0
    buf1                        .req v1
    buf2                        .req v2

    tmp0                        .req v4
    tmp1                        .req v5
    tmp2                        .req v6
    tmp3                        .req v7

    sign0                       .req v4
    sign1                       .req v5
    sign2                       .req v6
    sign3                       .req v7

    val0                        .req v16
    val0q                       .req q16
    val1                        .req v17
    val1q                       .req q17
    val2                        .req v18
    val2q                       .req q18
    val3                        .req v19
    val3q                       .req q19

    t0                          .req s20
    t1                          .req s21
    t2                          .req s22
    t3                          .req s23

    table0                      .req v24
    table0q                     .req q24
    table1                      .req v25
    table1q                     .req q25
    table2                      .req v26
    table2q                     .req q26
    table3                      .req v27
    table3q                     .req q27

    kyber_q                     .req v30
    bits                        .req v31
    bits_q                      .req q31

.text
.align 4
.global     rej_uniform_asm_clean
.global     _rej_uniform_asm_clean
rej_uniform_asm_clean:
_rej_uniform_asm_clean:
    push_stack
    save_gprs

    // TODO: This routine seems to write the results on the stack first, which is statically sized.
    //       It therefore only works for input buffers of bounded size, which needs to be documented.

    ASM_LOAD(bit_table, bit_table_data)
    ASM_LOAD(table_idx, table_data)

    /* Vectorize code start */

    ldr         bits_q, [bit_table]
    movz        tmp, #3329
    dup         kyber_q.8h, tmp

    // We cannot handle buffer lengths larger than REJ_UNIFORM_ASM_MAX_OUTPUT
    // In this case, we just return immediately, indicating that 0 bytes have
    // been processed.
    mov tmp, #REJ_UNIFORM_ASM_MAX_OUTPUT
    cmp lenw, tmp
    b.hi reject

    round_48x   bound, buflen
    mov     iterw, #0
    add     output_tmp_base, sp, #STACK_OFFSET_TMP_OUTPUT
    mov     output_tmp, output_tmp_base

    // TODO: This must be skipped if the remaining length is < 48
    loop48:
        add     x8, buf, iter

        // First, we unpack the byte stream into a stream of signed
        // coefficients, interpreting each consecutive 3 bytes as two
        // signed 12-bit coefficients, presented as 16-bit integers.
        //
        // We handle 16 such triples a time, and use ld3 for the required
        // de-interleaving of the byte stream.
        ld3     {buf0.16b, buf1.16b, buf2.16b}, [x8]
        add     iterw, iterw, #48

        // Unpack 16 triples of bytes into 16 pairs of 16-bit integers,
        // represented as 4 vectors val0-val3.
        zip1    tmp0.16b, buf0.16b, buf1.16b
        zip2    tmp1.16b, buf0.16b, buf1.16b
        zip1    tmp2.16b, buf1.16b, buf2.16b
        zip2    tmp3.16b, buf1.16b, buf2.16b

        bic     tmp0.8h, #0xf0, lsl 8
        bic     tmp1.8h, #0xf0, lsl 8
        ushr    tmp2.8h, tmp2.8h, #4
        ushr    tmp3.8h, tmp3.8h, #4

        zip1    val0.8h, tmp0.8h, tmp2.8h
        zip2    val1.8h, tmp0.8h, tmp2.8h
        zip1    val2.8h, tmp1.8h, tmp3.8h
        zip2    val3.8h, tmp1.8h, tmp3.8h

        // At this point, val0-val3 are the signed integers to do rejection
        // sampling on. For each of them, do the following:
        // - Check which coefficients are within range, and represent the set
        //   of lane-indices of those coefficients as an 8-bit bitmap.
        // - Move the respective lanes to the front of the vector. This is the
        //   most complex part, and is done by interpreting the 8-bit bitmap as
        //   an index into a lookup table giving the lane-table to be use for
        //   the `tbl` instruction.
        // - Write the vector to the output buffer, but merely increase the output
        //   buffer pointer by the number of valid coefficients.

        // Set valid lanes to -1 (0b1...1)
        cmhi    sign0.8h, kyber_q.8h, val0.8h
        cmhi    sign1.8h, kyber_q.8h, val1.8h
        cmhi    sign2.8h, kyber_q.8h, val2.8h
        cmhi    sign3.8h, kyber_q.8h, val3.8h

        // If lane i is valid and has value -1, retain only i-th bit
        and     sign0.16b, sign0.16b, bits.16b
        and     sign1.16b, sign1.16b, bits.16b
        and     sign2.16b, sign2.16b, bits.16b
        and     sign3.16b, sign3.16b, bits.16b

        // Get 8-bit bitmap of valid lane indices by adding lanes
        uaddlv  t0, sign0.8h
        uaddlv  t1, sign1.8h
        uaddlv  t2, sign2.8h
        uaddlv  t3, sign3.8h

        fmov    rec_idx_0, t0
        fmov    rec_idx_1, t1
        fmov    rec_idx_2, t2
        fmov    rec_idx_3, t3

        ldr     table0q, [table_idx, rec_idx_0, uxtw #4]
        ldr     table1q, [table_idx, rec_idx_1, uxtw #4]
        ldr     table2q, [table_idx, rec_idx_2, uxtw #4]
        ldr     table3q, [table_idx, rec_idx_3, uxtw #4]

        // Compute number of valid coefficients. Recall that at this
        // point, lane i has value 2^i (hence popcount 1) if its coefficient
        // is valid, and 0 otherwise.
        //
        // TODO: We could do this popcount directly on the result of cmhi,
        // thereby reducing the computation depth.
        cnt     sign0.16b, sign0.16b
        cnt     sign1.16b, sign1.16b
        cnt     sign2.16b, sign2.16b
        cnt     sign3.16b, sign3.16b

        // Extract number of valid coefficients
        uaddlv  t0, sign0.8h
        uaddlv  t1, sign1.8h
        uaddlv  t2, sign2.8h
        uaddlv  t3, sign3.8h

        fmov    ctr0, t0
        fmov    ctr1, t1
        fmov    ctr2, t2
        fmov    ctr3, t3

        // Move valid coefficients to the front
        tbl     val0.16b, {val0.16b}, table0.16b
        tbl     val1.16b, {val1.16b}, table1.16b
        tbl     val2.16b, {val2.16b}, table2.16b
        tbl     val3.16b, {val3.16b}, table3.16b

        str     val0q, [output_tmp]
        add     output_tmp, output_tmp, ctr0, uxtw #1

        str     val1q, [output_tmp]
        add     output_tmp, output_tmp, ctr1, uxtw #1

        str     val2q, [output_tmp]
        add     output_tmp, output_tmp, ctr2, uxtw #1

        str     val3q, [output_tmp]
        add     output_tmp, output_tmp, ctr3, uxtw #1

        sub     x8, output_tmp, output_tmp_base
        lsr     x8, x8, #1

        // Finish once we've generated sufficiently many coefficients
        cmp     count, lenw
        b.hs    memory_copy

        cmp     iterw, bound
        b.lo    loop48

        // TODO: This must be skipped if the remaining length is < 24
        // it is by luck only that this doesn't happen...
    loop24:

        add     x8, buf, iter

        ld3     {buf0.8b, buf1.8b, buf2.8b}, [x8]
        add     iterw, iterw, #24

        zip1    tmp0.16b, buf0.16b, buf1.16b
        zip1    tmp1.16b, buf1.16b, buf2.16b

        bic     tmp0.8h, #0xf0, lsl 8
        ushr    tmp1.8h, tmp1.8h, #4

        zip1    val0.8h, tmp0.8h, tmp1.8h
        zip2    val1.8h, tmp0.8h, tmp1.8h

        cmhi    sign0.8h, kyber_q.8h, val0.8h
        cmhi    sign1.8h, kyber_q.8h, val1.8h

        and     sign0.16b, sign0.16b, bits.16b
        and     sign1.16b, sign1.16b, bits.16b

        uaddlv  t0, sign0.8h
        uaddlv  t1, sign1.8h

        fmov    rec_idx_0, t0
        fmov    rec_idx_1, t1

        ldr     table0q, [table_idx, rec_idx_0, uxtw #4]
        ldr     table1q, [table_idx, rec_idx_1, uxtw #4]

        cnt     sign0.16b, sign0.16b
        cnt     sign1.16b, sign1.16b

        uaddlv  t0, sign0.8h
        uaddlv  t1, sign1.8h

        fmov    ctr0, t0
        fmov    ctr1, t1

        tbl     val0.16b, {val0.16b}, table0.16b
        tbl     val1.16b, {val1.16b}, table1.16b

        str     val0q, [output_tmp]
        add     output_tmp, output_tmp, ctr0, uxtw #1

        str     val1q, [output_tmp]
        add     output_tmp, output_tmp, ctr1, uxtw #1

        sub     x8, output_tmp, output_tmp_base
        lsr     x8, x8, #1

        // Finish once we've generated sufficiently many coefficients
        cmp     count, lenw
        b.hs    memory_copy

        cmp     iterw, buflen
        b.lo    loop24

memory_copy:
        str     iterw, [buf_consumed]

        // min = min(count,len)
        cmp     count, lenw
        csel    minw, count, lenw, lo
        str     min, [sp, #STACK_OFFSET_RESULT]

        // Skip memcpy if length is 0
        // TODO: Remove this?
        cbz     minw, end

        ubfiz   x2, min, #1, #32
        mov     x1, output_tmp_base
        // x0 is still the output buffer pointer

        // TODO: Hoist this out or write it manually
        // Also, once that's done, x30 is no longer clobbered
    #ifdef __APPLE__
        bl _memcpy
    #else
        bl memcpy
    #endif

    end:
        ldr     min, [sp, #STACK_OFFSET_RESULT]
        mov     w0, minw
        b return

reject:
        mov x0, #0
        str w0, [buf_consumed]
return:
        restore_gprs
        pop_stack
        ret

#endif /* MLKEM_USE_AARCH64_ASM */
