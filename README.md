[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# mlkem-native

**mlkem-native** is a C99 implementation of [ML-KEM](https://doi.org/10.6028/NIST.FIPS.203.ipd) targeting
PC, mobile and server platforms. It is a fork of the ML-KEM [reference
implementation](https://github.com/pq-crystals/kyber/tree/main/ref) and remains very close to it, adding a simple
interface for native code (e.g. assembler) as well as implementations of that interface for Arm (AArch64) and
Intel/AMD (x86_64) platforms.

If you need an ML-KEM implementation suitable for embedded systems, see
[**mlkem-c-embedded**](https://github.com/pq-code-package/mlkem-c-embedded/).

### Goals

**mlkem-native** aims for _assurance_, _ease of use_, and _performance_. In doubt, assurance and ease of
use take precedence over performance: We only include implementations into **mlkem-c-aarch64** which are manually
auditable or for which we see a path towards formal verification. All assembly aims to be readable and
micro-optimization deferred to automated tooling such as
[SLOTHY](https://slothy-optimizer.github.io/slothy/). Ultimately, **mlkem-native** strives for constant-time
implementations for which the C-code is verified to be free of undefined behaviour, and where all assembly is
functionally verified.

### Current state

**mlkem-native** is work in progress. **WE DO NOT CURRENTLY RECOMMEND RELYING ON THIS LIBRARY IN A PRODUCTION
ENVIRONMENT OR TO PROTECT ANY SENSITIVE DATA.** Once we have the first stable version, this notice will be removed.

#### Performance

**mlkem-native** has a complete AArch64 backend and offers highly competitive performance on AArch64 (see
[benchmarks](https://pq-code-package.github.io/mlkem-c-aarch64/dev/bench/)). An AVX2 backend is in development.

#### Verification

Mostly TODO. We apply CBMC to verify the absence of UB in a few basic C routines, but the bulk of the C verification
is outstanding. No formal verification has yet been applied to the backends.

### Call for contributors

We are actively seeking contributors who can help us build **mlkem-native**. If you are interested, please contact us,
or volunteer for any of the open issues.

### Call for potential consumers

If you are a potential consumer of **mlkem-native**, please reach out: We're interested in hearing the way you want to
use **mlkem-native**. If you have specific feature requests, please open an issue.

### Development

#### Environment Setup

All the development and build dependencies are specified in [flake.nix](flake.nix). We recommend installing them using
[nix](https://nixos.org/download/).

- **Setup with nix**
    - Running `nix develop` will execute a bash shell with the development environment specified in [flake.nix](flake.nix).
    - Alternatively, you can enable `direnv` by using `direnv allow`, allowing it to handle the environment setup for you.

    - As flake is still an experimental feature of nix, `--experimental-features 'nix-command flakes'` is needed when running the nix command. Alternatively, add the following to your `~/.config/nix/nix.conf` or `/etc/nix/nix.conf`:
```
experimental-features = nix-command flakes
```

- If you are not using nix, please ensure you have installed the same versions as specified in [flake.nix](flake.nix).

#### Development scripts
After running `nix develop` you should automatically have a number of support scripts in your PATH:

- [`format`](scripts/format) formats all files. The format is enforced by our CI, so you should run this script prior to committing.
- [`tests`](scripts/tests) run functional, kat tests natively or emulate them using `QEMU`. For information on how to use the script, please refer to the `--help` option.
