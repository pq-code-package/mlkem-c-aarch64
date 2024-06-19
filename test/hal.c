/*
 * Copyright (c) 2022 Arm Limited
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */
#include "hal.h"

void enable_cyclecounter()
{
    uint64_t tmp;
    __asm __volatile (
        "mrs    %[tmp], pmcr_el0\n"
        "orr    %[tmp], %[tmp], #1\n"
        "msr    pmcr_el0, %[tmp]\n"
        "mrs    %[tmp], pmcntenset_el0\n"
        "orr    %[tmp], %[tmp], #1<<31\n"
        "msr    pmcntenset_el0, %[tmp]\n"
        : [tmp] "=r" (tmp)
    );
}

void disable_cyclecounter()
{
    uint64_t tmp;
    __asm __volatile (
        "mov   %[tmp], #0x3f\n"
        "orr   %[tmp], %[tmp], #1<<31\n"
        "msr    pmcntenclr_el0, %[tmp]\n"
        : [tmp] "=r" (tmp)
    );
}

uint64_t get_cyclecounter()
{
    uint64_t retval;
    __asm __volatile (
        "mrs    %[retval], pmccntr_el0\n"
        : [retval] "=r" (retval));
    return retval;
}
