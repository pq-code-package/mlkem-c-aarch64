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

#if defined(PMU_CYCLES)
void enable_cyclecounter(void)
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

void disable_cyclecounter(void)
{
    uint64_t tmp;
    __asm __volatile (
        "mov   %[tmp], #0x3f\n"
        "orr   %[tmp], %[tmp], #1<<31\n"
        "msr    pmcntenclr_el0, %[tmp]\n"
        : [tmp] "=r" (tmp)
    );
}

uint64_t get_cyclecounter(void)
{
    uint64_t retval;
    __asm __volatile (
        "mrs    %[retval], pmccntr_el0\n"
        : [retval] "=r" (retval));
    return retval;
}

#elif defined(PERF_CYCLES)

#include <asm/unistd.h>
#include <linux/perf_event.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <sys/ioctl.h>
#include <unistd.h>

static int perf_fd = 0;
void enable_cyclecounter(void) {
    struct perf_event_attr pe;
    memset(&pe, 0, sizeof(struct perf_event_attr));
    pe.type = PERF_TYPE_HARDWARE;
    pe.size = sizeof(struct perf_event_attr);
    pe.config = PERF_COUNT_HW_CPU_CYCLES;
    pe.disabled = 1;
    pe.exclude_kernel = 1;
    pe.exclude_hv = 1;

    perf_fd = syscall(__NR_perf_event_open, &pe, 0, -1, -1, 0);

    ioctl(perf_fd, PERF_EVENT_IOC_RESET, 0);
    ioctl(perf_fd, PERF_EVENT_IOC_ENABLE, 0);
}

void disable_cyclecounter(void) {
    ioctl(perf_fd, PERF_EVENT_IOC_DISABLE, 0);
    close(perf_fd);
}

uint64_t get_cyclecounter(void) {
    long long cpu_cycles;
    ioctl(perf_fd, PERF_EVENT_IOC_DISABLE, 0);
    ssize_t read_count = read(perf_fd, &cpu_cycles, sizeof(cpu_cycles));
    if (read_count < 0) {
        perror("read");
        exit(EXIT_FAILURE);
    } else if (read_count == 0) {
        /* Should not happen */
        printf("perf counter empty\n");
        exit(EXIT_FAILURE);
    }
    ioctl(perf_fd, PERF_EVENT_IOC_ENABLE, 0);
    return cpu_cycles;
}

#else

void enable_cyclecounter(void) {
    return;
}
void disable_cyclecounter(void) {
    return;
}
uint64_t get_cyclecounter(void) {
    return(0);
}

#endif