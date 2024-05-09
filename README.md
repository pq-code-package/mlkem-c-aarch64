[//]: # (SPDX-License-Identifier: CC-BY-4.0)

**MLKEM-C-AArch64** is a collection of [MLKEM](https://doi.org/10.6028/NIST.FIPS.203.ipd) implementations for CPUs based on the Armv8-A and Armv9-A architectures.

There is a wide spectrum of implementations of the Armv8-A and Armv9-A architectures, ranging from efficiency-focused in-order cores to performance-centric highly out-of-order cores. Depending on a CPU's placement on this spectrum, its optimal MLKEM implementation will vary: Code that performs well on Apple M1 may not perform well on Cortex-A55, or vice versa.

MLKEM-C-AArch64 aims to provide a portfolio of implementations covering most Armv8-A/Armv9-A microarchitectures, plus code optimized for specific microarchitectures.

Initially, our benchmarking platforms are:
- Arm Cortex-A53 (as used in the Raspberry Pi3)
- Arm Cortex-A55
- Arm Cortex-A72 (as used in the Raspberry Pi4)
- Arm Cortex-A76 (as used in the Raspberry Pi5) / Neoverse N1 (as used in AWS Graviton2/c6g instances)
- Arm Neoverse-V1 (as used in the AWS Graviton3/c7g instances)
- Apple M1

Please reach out to the MLKEM-C-AArch64 maintainers or open an issue if you would like to see benchmarking on other microarchitectures.

Initially the primary target platforms are:
 - Arm Cortex-A72 (as used in the Raspberry Pi4)
 - Apple M1
 - AWS [Graviton 4](https://press.aboutamazon.com/2023/11/aws-unveils-next-generation-aws-designed-chips) instances based on [Arm Neoverse V2](https://developer.arm.com/Processors/Neoverse%20V2)


## Goals of MLKEM-C-AArch64

The goals of this project are as follows:

- Provide production-grade code that can be dropped into other projects.
- Being permissibly licensed with all code coming with an Apache-2.0 license.
- Tested against the official reference known-answer tests (KATs) and extended KATs (taken from another [PQCP](https://github.com/pq-code-package) project).
- Include Neon assembly implementations of the core building blocks of MLKEM performing well on a wide range of Armv8-A and Armv9-A platforms.
- Achieve performance matching the state-of-the-art on the target platforms.
- Maintainability should not be sacrificed and assembly should be as readable as possible. We make use of automated tooling for microarchitecture-specific optimization (e.g., by using [SLOTHY](https://slothy-optimizer.github.io/slothy/)).
- Provide a unified interface for Keccak implementations allowing 2-way, 4-way, and 8-way parallel implementations depending on the target microarchitecture.
- Eventually, we aim to unify the implementations with the implementations in [mlkem-c-generic](https://github.com/pq-code-package/mlkem-c-generic). However, we believe that for AArch64, there are too many relevant microarchitectures to come up with a single implementation that performs well on all. 


## Current state

**MLKEM-C-AArch64** is currently a work in progress and we do not recommend relying on it at this point.
**WE DO NOT CURRENTLY RECOMMEND RELYING ON THIS LIBRARY IN A PRODUCTION ENVIRONMENT OR TO PROTECT ANY SENSITIVE DATA.**
Once we have the first stable version, this notice will be removed.

The current code is compatible with the [`standard` branch of the official MLKEM repository](https://github.com/pq-crystals/kyber/tree/standard).

## Call for contributors

We are actively seeking contributors who can help us build **MLKEM-C-AArch64**.
If you are interested, please contact us, or volunteer for any of the open issues.

## Call for potential consumers

If you are a potential consumer of **MLKEM-C-AArch64**, please reach out to us.
We're interested in hearing the way you are considering using **MLKEM-C-AArch64** and could benefit from additional features.
If you have specific feature requests, please open an issue.
