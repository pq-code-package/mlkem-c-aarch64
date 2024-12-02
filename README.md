[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# mlkem-native

**mlkem-native** is a C90 implementation of [ML-KEM](https://doi.org/10.6028/NIST.FIPS.203.ipd) targeting
PC, mobile and server platforms. It is a fork of the ML-KEM [reference
implementation](https://github.com/pq-crystals/kyber/tree/main/ref), deviating primarily to (a) accommodate an
interface for native code (e.g. assembler), and (b) facilitate formal verification. **mlkem-native** provides
native code backends in C, AArch64 and x86_64, offering state of the art performance on most Arm, Intel and AMD
platforms.

If you need an ML-KEM implementation suitable for embedded systems, see
[**mlkem-c-embedded**](https://github.com/pq-code-package/mlkem-c-embedded/).

### Goals

**mlkem-native** aims for _assurance_, _ease of use_, and _performance_. We seek implementations
which are manually auditable or for which we see a path towards formal verification. All assembly aims
to be readable and micro-optimization deferred to automated tooling such as
[SLOTHY](https://slothy-optimizer.github.io/slothy/). Ultimately, **mlkem-native** strives for constant-time
implementations for which the C-code is verified to be free of undefined behaviour, and where all assembly is
functionally verified.

### Intended use

**mlkem-native** is currently intended to be used as a code package, where source files of **mlkem-native**
are imported into a consuming project's source tree and built using that project's build system. The build system
provided in this repository is for experimental and development purposes only.

### Current state

**mlkem-native** is work in progress. **WE DO NOT CURRENTLY RECOMMEND RELYING ON THIS LIBRARY IN A PRODUCTION
ENVIRONMENT OR TO PROTECT ANY SENSITIVE DATA.** Once we have the first stable version, this notice will be removed.

#### Performance

**mlkem-native** has complete AArch64 and AVX2 backends of competitive performance (see
[benchmarks](https://pq-code-package.github.io/mlkem-native/dev/bench/)).

#### Verification

All C code in [mlkem/*](mlkem) is verified to be memory and type safe using CBMC. This excludes, for example, out of
bounds accesses, as well as integer overflows during optimized modular arithmetic. See the [CBMC
Readme](cbmc/proofs/README.md) and the [CBMC Proof Guide](cbmc/proofs/proof_guide.md) for more information and how to
reproduce the proofs. The code in [fips202/*](fips202) has not yet been verified using CBMC.

Initial experiments are underway to verify AArch64 using [HOL-Light](https://hol-light.github.io/).

### Getting started

### Nix setup

All the development and build dependencies are specified in [flake.nix](flake.nix). We recommend installing them using
[nix](https://nixos.org/download/).

To execute a bash shell with the development environment specified in [flake.nix](flake.nix), run
```bash
nix develop --experimental-features 'nix-command flakes'
```

### Native setup

To build **mlkem-native**, you need `make` and a C99 compiler. To use the test scripts, you need Python3 with
dependencies as specified in [requirements.txt](requirements.txt). We recommend using a virtual environment, e.g.:

```bash
python3 -m venv venv
./venv/bin/python3 -m pip install -r requirements.txt
source venv/bin/activate
```

### Using `make`

You can build tests and benchmarks using the following `make` targets:

```bash
make mlkem
make bench
make bench_components
make nistkat
make kat
```

The resulting binaries can be found in [test/build](test/build).

### Windows

You can also build **mlkem-native** on Windows using `nmake` and an MSVC compiler.

To build and run the tests (only support functional testing for non-opt implementation for now), use the following `nmake` targets:
```powershell
nmke /f .\Makefile.Microsoft_nmake quickcheck
```

### Using `tests` script

We recommend compiling and running tests and benchmarks using the [`./scripts/tests`](scripts/tests) script. For
example,

```bash
./scripts/tests func
```

will compile and run functionality tests. For detailed information on how to use the script, please refer to the
`--help` option.

### Call for contributors

We are actively seeking contributors who can help us build **mlkem-native**. If you are interested, please contact us,
or volunteer for any of the open issues.

### Call for potential consumers

If you are a potential consumer of **mlkem-native**, please reach out: We're interested in hearing the way you want to
use **mlkem-native**. If you have specific feature requests, please open an issue.
