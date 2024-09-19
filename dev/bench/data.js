window.BENCHMARK_DATA = {
  "lastUpdate": 1726721732369,
  "repoUrl": "https://github.com/pq-code-package/mlkem-c-aarch64",
  "entries": {
    "Arm Cortex-A76 (Raspberry Pi 5) benchmarks": [
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "efadcf93448a4b28425e38aaf8f1dfac2eb623f8",
          "message": "Add batched Keccak ASM (#137)\n\n* Keccak: Remove need for shake256x4_squeezeblocks_single\r\n\r\nWhen we move towards an interleaved representation of the batched\r\nKeccak state, squeezing a single block becomes awkward.\r\n\r\nInstead, follow the approach of the AVX2 implementation from\r\nthe Kyber repository, and always squeeze all blocks during gen_matrix,\r\neven if some lanes have already been completed.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Keccak: Remove mix of XOF vs. SHAKE128\r\n\r\nThe reference implementation hides the specific choice of XOF\r\nbehind a shallow internal interface resolving to shake128.\r\n\r\nThe batched implementation of gen_matrix bypasses this interface\r\nby directly calling into shake128x4, while still using the shim\r\nxof-api for non-batched invocations.\r\n\r\nThis distinction is confusing: We should either use a XOF wrapper\r\nthroughout -- both for batched and non-batched calls -- or not use\r\nit at all.\r\n\r\nThis commit removes the XOF wrapper for now.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Remove no longer needed keccakx_get_lane_state\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hide implementation details of batched SHAKE state\r\n\r\nThe internal structure of the batched SHAKE state is irrelevant\r\nto the caller; it only needs to know its size in order to be able\r\nto allocate it on the stack.\r\n\r\nThis commit makes keccakx4_state an implementation detail of\r\nfips202x4.c, and instead exposes shakex4_state as a raw byte\r\narray.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Rename KECCAK_CTX -> KECCAK_LANES in fips202x4.c\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Introduce wrappers for x4-batched Keccak\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add clean Armv8.4-A assembly for 2-fold batched Keccak-f1600\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add logic choosing Keccak-f1600 assembly\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* FIPS202: Remove spurious `.endm` from common.i\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* FIPS202: Minor optimization for little endian systems\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-19T12:51:46+08:00",
          "tree_id": "b60137af050067455922370eda66165aa24d4bd2",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/efadcf93448a4b28425e38aaf8f1dfac2eb623f8"
        },
        "date": 1726721589483,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 70576,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 73813,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 91033,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 124763,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 125981,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 149549,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 195491,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 194809,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 224579,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton3": [
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "efadcf93448a4b28425e38aaf8f1dfac2eb623f8",
          "message": "Add batched Keccak ASM (#137)\n\n* Keccak: Remove need for shake256x4_squeezeblocks_single\r\n\r\nWhen we move towards an interleaved representation of the batched\r\nKeccak state, squeezing a single block becomes awkward.\r\n\r\nInstead, follow the approach of the AVX2 implementation from\r\nthe Kyber repository, and always squeeze all blocks during gen_matrix,\r\neven if some lanes have already been completed.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Keccak: Remove mix of XOF vs. SHAKE128\r\n\r\nThe reference implementation hides the specific choice of XOF\r\nbehind a shallow internal interface resolving to shake128.\r\n\r\nThe batched implementation of gen_matrix bypasses this interface\r\nby directly calling into shake128x4, while still using the shim\r\nxof-api for non-batched invocations.\r\n\r\nThis distinction is confusing: We should either use a XOF wrapper\r\nthroughout -- both for batched and non-batched calls -- or not use\r\nit at all.\r\n\r\nThis commit removes the XOF wrapper for now.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Remove no longer needed keccakx_get_lane_state\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hide implementation details of batched SHAKE state\r\n\r\nThe internal structure of the batched SHAKE state is irrelevant\r\nto the caller; it only needs to know its size in order to be able\r\nto allocate it on the stack.\r\n\r\nThis commit makes keccakx4_state an implementation detail of\r\nfips202x4.c, and instead exposes shakex4_state as a raw byte\r\narray.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Rename KECCAK_CTX -> KECCAK_LANES in fips202x4.c\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Introduce wrappers for x4-batched Keccak\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add clean Armv8.4-A assembly for 2-fold batched Keccak-f1600\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add logic choosing Keccak-f1600 assembly\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* FIPS202: Remove spurious `.endm` from common.i\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* FIPS202: Minor optimization for little endian systems\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-19T12:51:46+08:00",
          "tree_id": "b60137af050067455922370eda66165aa24d4bd2",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/efadcf93448a4b28425e38aaf8f1dfac2eb623f8"
        },
        "date": 1726721711925,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 47632,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49241,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 59583,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 83524,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 84252,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 98343,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 128544,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 129839,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 148062,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton2": [
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "efadcf93448a4b28425e38aaf8f1dfac2eb623f8",
          "message": "Add batched Keccak ASM (#137)\n\n* Keccak: Remove need for shake256x4_squeezeblocks_single\r\n\r\nWhen we move towards an interleaved representation of the batched\r\nKeccak state, squeezing a single block becomes awkward.\r\n\r\nInstead, follow the approach of the AVX2 implementation from\r\nthe Kyber repository, and always squeeze all blocks during gen_matrix,\r\neven if some lanes have already been completed.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Keccak: Remove mix of XOF vs. SHAKE128\r\n\r\nThe reference implementation hides the specific choice of XOF\r\nbehind a shallow internal interface resolving to shake128.\r\n\r\nThe batched implementation of gen_matrix bypasses this interface\r\nby directly calling into shake128x4, while still using the shim\r\nxof-api for non-batched invocations.\r\n\r\nThis distinction is confusing: We should either use a XOF wrapper\r\nthroughout -- both for batched and non-batched calls -- or not use\r\nit at all.\r\n\r\nThis commit removes the XOF wrapper for now.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Remove no longer needed keccakx_get_lane_state\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hide implementation details of batched SHAKE state\r\n\r\nThe internal structure of the batched SHAKE state is irrelevant\r\nto the caller; it only needs to know its size in order to be able\r\nto allocate it on the stack.\r\n\r\nThis commit makes keccakx4_state an implementation detail of\r\nfips202x4.c, and instead exposes shakex4_state as a raw byte\r\narray.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Rename KECCAK_CTX -> KECCAK_LANES in fips202x4.c\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Introduce wrappers for x4-batched Keccak\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add clean Armv8.4-A assembly for 2-fold batched Keccak-f1600\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add logic choosing Keccak-f1600 assembly\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* FIPS202: Remove spurious `.endm` from common.i\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* FIPS202: Minor optimization for little endian systems\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-19T12:51:46+08:00",
          "tree_id": "b60137af050067455922370eda66165aa24d4bd2",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/efadcf93448a4b28425e38aaf8f1dfac2eb623f8"
        },
        "date": 1726721721686,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 70581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 74405,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 91704,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 124881,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 125953,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 149533,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 194394,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 193505,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 223190,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Arm Cortex-A55 (Snapdragon 888) benchmarks": [
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "efadcf93448a4b28425e38aaf8f1dfac2eb623f8",
          "message": "Add batched Keccak ASM (#137)\n\n* Keccak: Remove need for shake256x4_squeezeblocks_single\r\n\r\nWhen we move towards an interleaved representation of the batched\r\nKeccak state, squeezing a single block becomes awkward.\r\n\r\nInstead, follow the approach of the AVX2 implementation from\r\nthe Kyber repository, and always squeeze all blocks during gen_matrix,\r\neven if some lanes have already been completed.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Keccak: Remove mix of XOF vs. SHAKE128\r\n\r\nThe reference implementation hides the specific choice of XOF\r\nbehind a shallow internal interface resolving to shake128.\r\n\r\nThe batched implementation of gen_matrix bypasses this interface\r\nby directly calling into shake128x4, while still using the shim\r\nxof-api for non-batched invocations.\r\n\r\nThis distinction is confusing: We should either use a XOF wrapper\r\nthroughout -- both for batched and non-batched calls -- or not use\r\nit at all.\r\n\r\nThis commit removes the XOF wrapper for now.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Remove no longer needed keccakx_get_lane_state\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hide implementation details of batched SHAKE state\r\n\r\nThe internal structure of the batched SHAKE state is irrelevant\r\nto the caller; it only needs to know its size in order to be able\r\nto allocate it on the stack.\r\n\r\nThis commit makes keccakx4_state an implementation detail of\r\nfips202x4.c, and instead exposes shakex4_state as a raw byte\r\narray.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Rename KECCAK_CTX -> KECCAK_LANES in fips202x4.c\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Introduce wrappers for x4-batched Keccak\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add clean Armv8.4-A assembly for 2-fold batched Keccak-f1600\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add logic choosing Keccak-f1600 assembly\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* FIPS202: Remove spurious `.endm` from common.i\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* FIPS202: Minor optimization for little endian systems\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-19T12:51:46+08:00",
          "tree_id": "b60137af050067455922370eda66165aa24d4bd2",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/efadcf93448a4b28425e38aaf8f1dfac2eb623f8"
        },
        "date": 1726721728305,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 170804,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 184543,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 236629,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 311265,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 323546,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 395680,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 487518,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 499369,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 591032,
            "unit": "cycles"
          }
        ]
      }
    ]
  }
}