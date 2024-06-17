[//]: # (SPDX-License-Identifier: CC-BY-4.0)

**mlkem-c-aarch64** is a collection of [MLKEM](https://doi.org/10.6028/NIST.FIPS.203.ipd) implementations for CPUs based on the Armv8-A and Armv9-A architectures.

## Goals of mlkem-c-aarch64

The primary goals of this project are as follows:
- _Assurance:_ Clean code that's extensively tested and amenable for audit and verification
- _Ease of use:_ Permissive licensing, modularity, few dependencies
- _Performance:_ Competitive performance for most Armv8-A/Armv9-A platforms

There are tensions between these goals:
- Optimal code is target-specific, but a large variety of CPU-specific implementations makes a library harder to both use and maintain.
- Optimal code is complex (e.g. relying on handwritten assembly), impeding maintainenance and amenability for audit or verification.

In doubt, **mlkem-c-aarch64** chooses assurance and ease of use over performance: We only include implementations into **mlkem-c-aarch64** which are manually auditable or (ideally _and_) for which we see a path towards formal verification. All assembly should be as readable as possible and micro-optimization ideally deferred to automated tooling such as [SLOTHY](https://slothy-optimizer.github.io/slothy/). Ultimately, **mlkem-c-aarch64** strives for constant-time implementations for which the C-code is, at minimum, verified to be free of undefined behaviour, and where all assembly is functionally verified.

**mlkem-c-aarch64** aims to provide a portfolio of implementations jointly providing competitive performance for most Armv8-A/Armv9-A microarchitectures. For some specific microarchitectures of particular interest, **mlkem-c-aarch64** may also provide CPU-specific implementations. Initially, our benchmarking platforms are:
- Arm Cortex-A55
- Arm Cortex-A72 (as used in the Raspberry Pi4)
- Arm Cortex-A76 (as used in the Raspberry Pi5) / Neoverse N1 (as used in AWS Graviton2/c6g instances)
- Arm Neoverse V1 (as used in the AWS Graviton3/c7g instances)
- Apple M1

Please reach out to the **mlkem-c-aarch64** maintainers or open an issue if you would like to see benchmarking on other microarchitectures.

## Non-goals

At this point, we do not provide implementations optimized for memory usage (code / RAM). If you need a memory-optimized implementation and the implementation provided by MLKEM-C-Generic is not of sufficient performance to your application, please contact us.

## Relation to MLKEM-C-Generic

Eventually, we aim to unify the (shared) C-part of the implementations provided by **mlkem-c-aarch64** with the implementations in [mlkem-c-generic](https://github.com/pq-code-package/mlkem-c-generic). Initially, however, we will allow some divergence, e.g. to explore interfaces to 2-/4-/8-way parallel Keccak implementations which are essential for high-performance implementations of MLKEM.


## Current state

**mlkem-c-aarch64** is currently a work in progress and we do not recommend relying on it at this point.
**WE DO NOT CURRENTLY RECOMMEND RELYING ON THIS LIBRARY IN A PRODUCTION ENVIRONMENT OR TO PROTECT ANY SENSITIVE DATA.**
Once we have the first stable version, this notice will be removed.

The current code is compatible with the [`standard` branch of the official MLKEM repository](https://github.com/pq-crystals/kyber/tree/standard).


## Development

### Environment Setup

All the development and build dependencies are specified in [flake.nix](flake.nix). We recommend installing them using [nix](https://nixos.org/download/).

- **Setup with nix**
    - Running `nix develop` will execute a bash shell with the development environment specified in [flake.nix](flake.nix).
    - Alternatively, you can enable `direnv` by using `direnv allow`, allowing it to handle the environment setup for you.

    - As flake is still an experimental feature of nix, `--experimental-features 'nix-command flakes'` is needed when running the nix command. Alternatively, add the following to your `~/.config/nix/nix.conf` or `/etc/nix/nix.conf`:
```
experimental-features = nix-command flakes
```

- If you are not using nix, please ensure you have installed the same versions as specified in [flake.nix](flake.nix).

### Development scripts
After running `nix develop` you should automatically have a number of support scripts in your PATH:

- [`format`](scripts/format) formats all files. The format is enforced by our CI, so you should run this script prior to committing.
- [`tests`](scripts/tests) run functional, kat tests natively or emulate them using `QEMU`. For information on how to use the script, please refer to the `--help` option.

## Call for contributors

We are actively seeking contributors who can help us build **mlkem-c-aarch64**.
If you are interested, please contact us, or volunteer for any of the open issues.

## Call for potential consumers

If you are a potential consumer of **mlkem-c-aarch64**, please reach out to us.
We're interested in hearing the way you are considering using **mlkem-c-aarch64** and could benefit from additional features.
If you have specific feature requests, please open an issue.
