[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Replacing FIPS-202

If your library has a FIPS-202 implementation, you can use it instead of the one shipped with mlkem-native.

1. Replace `mlkem/fips202/*` by your own FIPS-202 implementation.
2. Provide replacements for the headers [`mlkem/fips202/fips202.h`](mlkem/fips202/fips202.h) and [`mlkem/fips202/fips202x4.h`](mlkem/fips202/fips202x4.h) and the
functionalities specified therein:
  * Structure definitions for `shake128ctx` and `shake128x4ctx`
  * `shake128_absorb_once()`: Initialize a SHAKE-128 context and perform a single absorb step.
  * `shake128_squeezeblocks()`: Squeeze SHAKE-128 context
  * `shake128_release()`: Release a SHAKE-128 context after use
  * `shake256()`, `sha3_256()`, `sha3_512()`: One-shot SHAKE-256 / SHA3-256 / SHA3-512 operations
  * `shake256x4()`: One-shot 4x-batched SHAKE-256 operation
  * `shake128x4_absorb_once()`: Initialize a 4x-batched SHAKE-128 context and perform a single absorb step.
  * `shake128x4_squeezeblocks()`: Squeeze 4x-batched SHAKE-128 context
  * `shake128x4_release()`: Release a 4x-batched SHAKE-128 context after use

See [`mlkem/fips202/fips202.h`](mlkem/fips202/fips202.h) and [`mlkem/fips202/fips202x4.h`](mlkem/fips202/fips202x4.h) for more details. Note that the structure
definitions may differ from those shipped with mlkem-native: In particular, you may fall back to an incremental hashing
implementation which tracks the current offset in its state.
