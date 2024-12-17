[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Building mlkem-native

### Prerequisites

To build **mlkem-native**, you need `make` and a C90 compiler. To use the test scripts, you need Python3 with
dependencies as specified in [requirements.txt](requirements.txt). We recommend using a virtual environment, e.g.:

```bash
python3 -m venv venv
./venv/bin/python3 -m pip install -r requirements.txt
source venv/bin/activate
```

### Using `make`

You can build and test **mlkem-native** as follows:

```bash
make quickcheck       # With native code backend (if available)
make OPT=0 quickcheck # With C backend
```

To merely build test and benchmarking components, use the following `make` targets:

```bash
make mlkem
make bench
make bench_components
make nistkat
make kat
```

The resulting binaries can then be found in `test/build`.

### Using `tests` script

We recommend compiling and running tests and benchmarks using the [`./scripts/tests`](scripts/tests) script. For
example,

```bash
./scripts/tests func
```

will compile and run functionality tests. For detailed information on how to use the script, please refer to the
`--help` option.

### Nix setup

All the development and build dependencies are also specified in [flake.nix](flake.nix). We recommend installing them
using
[nix](https://nixos.org/download/). To execute a bash shell with the development environment specified in
[flake.nix](flake.nix), run
```bash
nix develop --experimental-features 'nix-command flakes'
```

### Windows

You can also build **mlkem-native** on Windows using `nmake` and an MSVC compiler.

To build and run the tests (only support functional testing for non-opt implementation for now), use the following `nmake` targets:
```powershell
nmke /f .\Makefile.Microsoft_nmake quickcheck
```
