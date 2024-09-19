window.BENCHMARK_DATA = {
  "lastUpdate": 1726725134871,
  "repoUrl": "https://github.com/pq-code-package/mlkem-c-aarch64",
  "entries": {
    "Arm Cortex-A72 (Raspberry Pi 4) benchmarks": [
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "de9203e2161ca48bc4daf7c30ea8e80ae77557d7",
          "message": "Add github benchmark action (#78)\n\n* add github benchmark action\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* -output should be -o\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* add comment on output format\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* format\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>",
          "timestamp": "2024-06-26T13:46:54+01:00",
          "tree_id": "a0be78ac5569604219677d305ab65d0daa0b8192",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/de9203e2161ca48bc4daf7c30ea8e80ae77557d7"
        },
        "date": 1719406252982,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 139737,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 173440,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 223995,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 240688,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 284687,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 351714,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 378520,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 430122,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 513480,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "99893ebf2436c1ab8d9122c963931cf999153f88",
          "message": "Add M1 benchmarking code (#81)\n\n* add M1 benchmarking code\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* Update scripts/tests\r\n\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* improve bench script\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* add taskpolicy\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* typo\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-06-28T13:40:04+08:00",
          "tree_id": "dcc9da99b0216e78be2ea2cfa84fe85b0dc6adda",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/99893ebf2436c1ab8d9122c963931cf999153f88"
        },
        "date": 1719553429162,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 139839,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 173467,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 224224,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 240948,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 285582,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 352382,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 378944,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 429900,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 513382,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a3d00c7b6721f55ac1fff34bfa085c0e585a5e9e",
          "message": "Add support for static linking of glibc on aarch64 and x86_64 linux  (#82)\n\n* use cross compiled nix gcc for x86_64 instead\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* cleanup and refactor nix\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix dynamic linking glibc\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* remove redundant empty lines\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* use specific gcc for the shell\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-06-28T16:10:43+08:00",
          "tree_id": "9b320ca3da71582bb6dab308c25232aab06fcd98",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/a3d00c7b6721f55ac1fff34bfa085c0e585a5e9e"
        },
        "date": 1719562467346,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 139915,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 173680,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 224975,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 240880,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 285430,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 351945,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 377966,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 429291,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 512818,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "124e51051c8420ea0ecd1cd41f5bd96869ecf20f",
          "message": "Add z3_4_12 to standard NIX config for all platforms. (#85)\n\n* Add z3_4_12 to standard NIX config for all platforms.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* move z3_4_12 to cbmcpkg\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nCo-authored-by: Matthias J. Kannwischer <matthias@kannwischer.eu>",
          "timestamp": "2024-06-28T22:48:49+08:00",
          "tree_id": "4446d18679d2abd2f0af17c94d46aa780dc5ede6",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/124e51051c8420ea0ecd1cd41f5bd96869ecf20f"
        },
        "date": 1719586354099,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 139886,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 173481,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 224078,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 240657,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 284898,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 351440,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 378984,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 429791,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 513141,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "41237b36f7615fd6d17030962582268902af3156",
          "message": "Benchmarking on A55 (#84)\n\n* add exec_wrapper for tests script\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* add ci benchmark on a55 runner\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix if condition for the benchmark workflow\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make parsing of results more robust\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* log cmd on failure\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* remove taskpolicy and replace by exec_wrapper\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* refactor benchmarking yml\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* fix exec wrapper\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* add name of job\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* always turn exec wrapper into a list\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* remove duplicate test script\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* move splitting of exec wrapper\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nCo-authored-by: Matthias J. Kannwischer <matthias@kannwischer.eu>",
          "timestamp": "2024-07-02T09:50:39+01:00",
          "tree_id": "2958eba8994fdec161ca0bc185904cc972a20649",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/41237b36f7615fd6d17030962582268902af3156"
        },
        "date": 1719910771192,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 139832,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 173610,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 224400,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 240903,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 285424,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 351957,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 378461,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 429532,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 514008,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c37532bef14837c88cfa797794cce5bfe1358973",
          "message": "Add coeff_signed_to_unsigned() functions and its proof (#67)\n\n* Add coeff_signed_to_unsigned() functions and its proof\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Rename coeff_signed_to_unsigned -> scalar_signed_to_unsigned_q_16\r\n\r\nAlso, uniformize file structure of proof subdirctory for\r\nscalar_signed_to_unsigned_q_16 with those of other functions.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add warning & TODO regarding potential introduction of branch\r\n\r\nscalar_signed_to_unsigned_q_16() uses the expression `(r < 0)`\r\nfor the extraction of the sign-bit, which is prone to compilers\r\nturning them into a branch.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Re-write and prove scalar_signed_to_unsigned_q_16() using cmov_int16()\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Add verify.c to proof dependencies for this function.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Increase CBMC_OBJECT_BITS for this function.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-07-02T11:27:13+01:00",
          "tree_id": "4067a9e22d19e020bba9a65eb00ac3366b500a85",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/c37532bef14837c88cfa797794cce5bfe1358973"
        },
        "date": 1719916572653,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 149852,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176107,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 226776,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 255603,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 287623,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 354589,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 398973,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 433080,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 516800,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "dde6611ae205ba649b2e4224da2dbba3425d676f",
          "message": "Add RPi5 benchmarks (#86)\n\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>",
          "timestamp": "2024-07-02T19:34:47+01:00",
          "tree_id": "28a200c5504f1a22ed03b16b21a4e6afc4ddbedb",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/dde6611ae205ba649b2e4224da2dbba3425d676f"
        },
        "date": 1719945824738,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 149776,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176138,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 226913,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 255578,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 288305,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 355219,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 398096,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 431517,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 515279,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "dnguye69@gmu.edu",
            "name": "Duc Tri Nguyen",
            "username": "cothan"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "88fcf89619af84a941f403cfbb02780f2c6f3b02",
          "message": "add keccakx interface (#62)\n\nSigned-off-by: Duc Tri Nguyen <dnguye69@gmu.edu>\r\n\r\nrename to x4\r\n\r\nadd shake256x4 interface\r\n\r\nadd shake256x4\r\n\r\nadd batch getnoise sampling\r\n\r\nSigned-off-by: Duc Tri Nguyen <9219016+cothan@users.noreply.github.com>\r\n\r\nunroll prf to shake256x4\r\n\r\nSigned-off-by: Duc Tri Nguyen <dnguye69@gmu.edu>\r\nSigned-off-by: Duc Tri Nguyen <9219016+cothan@users.noreply.github.com>\r\n\r\nfix space\r\n\r\nSigned-off-by: Duc Tri Nguyen <9219016+cothan@users.noreply.github.com>\r\n\r\nassume input pointers are valid, thus, remove conditions.\r\n\r\nmove memcpy outside of the loop",
          "timestamp": "2024-07-19T04:06:40+01:00",
          "tree_id": "875dd304a7e951f97e792cab580ba9f2196bf863",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/88fcf89619af84a941f403cfbb02780f2c6f3b02"
        },
        "date": 1721358957664,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150101,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 175718,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 226211,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 258716,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 288241,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 354840,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 396398,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 429277,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 513338,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bad1095a2223a6cea6cf47b9c4966fc983ce3de8",
          "message": "Refactor nix configuration on ci and the aarch64 gcc dependency on x86_64 machines  (#89)\n\n* use nix aarch64-multiplatform gcc instead\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* cleanup arm-gnu-gcc.nix\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* expose cross_prefix for the tests script\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor with github action defaults shell feature\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make the nix config more readable\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* hide cross prefix for x86_64 machines\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* set default of cross prefix for different machines to make it clearer\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix the case if cross prefix is empty string in ci\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-07-29T18:33:53+08:00",
          "tree_id": "d427096ed306aabd1e59110ad7a85923f0f1abd0",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/bad1095a2223a6cea6cf47b9c4966fc983ce3de8"
        },
        "date": 1722249792197,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150230,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 175756,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 226412,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 259071,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 288597,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 356202,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 397000,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 432161,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 515891,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "20c1bcacba92c7889674626f1ba0e0cf99500ee7",
          "message": "Update CBMC to v6.1.1 (#90)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-07-30T13:06:07+08:00",
          "tree_id": "e928b3a128c4713afb3c883d00638eb4fd655865",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/20c1bcacba92c7889674626f1ba0e0cf99500ee7"
        },
        "date": 1722316495552,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150407,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 175918,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 226465,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 259388,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 289112,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 355689,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 0,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 0,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 0,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "de2c8425e0e478c6643b064c037776ae0a717d31",
          "message": "Fix CBMC build on Linux and run CBMC in CI (#93)\n\n* CI: Enable CBMC on Linux\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* fix cbmc patch and refactor cbmc pkgs into cbmc folder\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* add license\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* Add cbmc version to flake.nix\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* reuse the version in cbmc/default.nix\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\nCo-authored-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-08-09T13:02:25+01:00",
          "tree_id": "58230eb2971153cd8f26344311bb0359ae081c0f",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/de2c8425e0e478c6643b064c037776ae0a717d31"
        },
        "date": 1723281272499,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150228,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 175632,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 226255,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 258722,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 288887,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 355243,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 395725,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 429493,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 513230,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "ad56b2a1098d26c71bab6c6158a01a1c1c093aba",
          "message": "Update version and hash to specify cbmc-viewer version 3.9 (#92)\n\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>",
          "timestamp": "2024-08-11T11:58:29+08:00",
          "tree_id": "23c8d6801c91a3c906ad95434cae6f93424ee634",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ad56b2a1098d26c71bab6c6158a01a1c1c093aba"
        },
        "date": 1723349294703,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150522,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176088,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 226842,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 258759,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 288144,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 355911,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 397968,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 433383,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 516849,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "bd2edd6cfb22435130cd584cdfc1221466376377",
          "message": "Add workflows for benchmarking on EC2 (#99)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\nUpdate setup-nix github action",
          "timestamp": "2024-09-05T04:59:55+01:00",
          "tree_id": "dfc7dc995548de931085a140a57a48f5069424fb",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/bd2edd6cfb22435130cd584cdfc1221466376377"
        },
        "date": 1725509344204,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150840,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176811,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227668,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 260115,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 290365,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 357533,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 398566,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 432980,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 517332,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "16a4c696ba752cb7e669158785b61755d91a862c",
          "message": "Push EC2 benchmark results to GH pages (#101)\n\n* Push EC2 benchmark results to GH pages\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Switch Gv2 benchmark to t4g.small\r\n\r\nAlso, use archflags instead of cflags for -mcpu setting\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-05T10:53:09+01:00",
          "tree_id": "e7a0471c2b7da5d78d8a3f110473d1b34d2cf890",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/16a4c696ba752cb7e669158785b61755d91a862c"
        },
        "date": 1725530548320,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 151081,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176875,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227702,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 260160,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 289728,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 357066,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 399334,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 433846,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 518672,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9a44cdc93770b6afeb161be193c9d6e0bd8c30b8",
          "message": "update aws credential to v4 (#105)\n\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-05T11:21:30+01:00",
          "tree_id": "807d87749a67ce70769d0f1ac0b43b0d6f4b858b",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/9a44cdc93770b6afeb161be193c9d6e0bd8c30b8"
        },
        "date": 1725533847482,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150893,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176973,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227730,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 260992,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 290944,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 358150,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 399436,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 433645,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 520312,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d72aa188854a724853a6808bfa19ef743cafcca8",
          "message": "Add proof of poly_compress() (#91)\n\n* Add contract-based proofs for compression functions\r\n\r\n- scalar_compress_q_16\r\n- scalar_compress_q_32\r\n- poly_compress\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Correct loop invariants and assigns clauses in poly_compress()\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Update poly_compress() to avoid pointer arithmetic and mutation of formal parameter r. Uses array indexing instead.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Use Bitwuzla for proof of poly_compress()\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* 1. Correct pre-condition on poly_compress()\r\n\r\n2. Remove commented-out line in body of poly_compress()\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Explicitly disable EXTERNAL_SAT_SOLVER, and use SMT2 back-end instead\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Finalize proof of poly_compress()\r\n\r\n1. Introduce common num_blocks constant to avoid repetition of \"KYBER_N / 8\"\r\n2. Add explanatory comment on switch from pointer arithmetic to array indexing\r\n   in assignment to r[]\r\n3. Introduce loop invariants for the KYBER_K=4 branch of the code.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Remove CBMC contracts on poly_decompress(). These will be re-introduced in a later PR\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Remove INDENT-ON and INDENT-OFF tags for now to keep astyle happy.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-05T20:08:22+01:00",
          "tree_id": "36933cf1671eef6052c9c107f420e7e92ee6f277",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/d72aa188854a724853a6808bfa19ef743cafcca8"
        },
        "date": 1725563853525,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150815,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176282,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227272,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 260188,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 289840,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 356795,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 399279,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 432938,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 519154,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "ry@linux.com",
            "name": "Ry Jones",
            "username": "ryjones"
          },
          "committer": {
            "email": "ry@linux.com",
            "name": "Ry Jones",
            "username": "ryjones"
          },
          "distinct": true,
          "id": "3138820190d7af42f69d148ae7b865f717f5ae6e",
          "message": "Update configure-aws-credentials to latest\n\nSigned-off-by: Ry Jones <ry@linux.com>",
          "timestamp": "2024-09-06T09:41:29-07:00",
          "tree_id": "742924c90f34428a237dd9d7ee0d5a2d5af089bd",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/3138820190d7af42f69d148ae7b865f717f5ae6e"
        },
        "date": 1725641438012,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 151103,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176557,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227203,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 259800,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 289597,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 356890,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 399613,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 432509,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 517759,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b9e7133a164c7f4a266009c8b1271ab2124cc4c3",
          "message": "Refactor Build System for Easier Extensibility and Future Optimizations (#100)\n\n* place all artifacts under test/build dir\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor the build system\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor build system objs macro\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make don't print directory\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* integrate the new build system to python script\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* format nix file\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix arch flags not correctly set\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* ci fix -static to be cflags\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix static compilation for benchmarking on a55\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-08T05:58:33+01:00",
          "tree_id": "5d8a46f9da0e558e3ff1f02c93884de9cc2258af",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/b9e7133a164c7f4a266009c8b1271ab2124cc4c3"
        },
        "date": 1725772060698,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150883,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176290,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227130,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 261718,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 291721,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 358658,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 398859,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 432881,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 517487,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "f4ba147375abd145b9447a8ddfbf698252c7c46d",
          "message": "Clear nix-installer cache prior to EC2 benchmarks (#108)\n\n* Allow keeping EC2 instances after workflow failures\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Clear nix-installer cache before running EC2 bench workflow\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hoist GH cache clearing into reusable action\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-09T05:29:40+01:00",
          "tree_id": "773365ad06f4cd23f411c72c5f661774ad4da6c8",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/f4ba147375abd145b9447a8ddfbf698252c7c46d"
        },
        "date": 1725856728755,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 151170,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176804,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227770,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 261260,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 290632,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 357753,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 399219,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 433029,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 517773,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "a5b57128fcf5079c21af3c52595fe96f1b41876e",
          "message": "Hoist benchmarking steps into reusable GH action (#110)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nSigned-off-by: Ry Jones <ry@linux.com>",
          "timestamp": "2024-09-09T08:01:11+01:00",
          "tree_id": "3444a5bd5ad8e18c4139cff55a32144195dfe712",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/a5b57128fcf5079c21af3c52595fe96f1b41876e"
        },
        "date": 1725865827682,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150881,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176309,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227372,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 261465,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 291111,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 359483,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 398737,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 434869,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 520997,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "580c136b692ff8f4b68b823e1a90c89db17448a1",
          "message": "Update CBMC to version 6.2.0 (#112)\n\n* Update CBMC to version 6.2.0\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Update version number of CBMC to 6.2.0 in flake.nix and add reminder in cbmc/default.nix to do this in future.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>",
          "timestamp": "2024-09-09T11:39:30+01:00",
          "tree_id": "8bc367c010be48281edf81e455a1241762b38b87",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/580c136b692ff8f4b68b823e1a90c89db17448a1"
        },
        "date": 1725878950391,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150854,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176400,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227506,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 260861,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 290563,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 357854,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 398834,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 432551,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 519197,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9df492987200d8f8de7796fdab71a39866e778ea",
          "message": "Fix variable detection of recursive make (#115)\n\n* fix variable detection of recursive make\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* remove the need of recursive make\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-10T09:16:17+01:00",
          "tree_id": "0353d30fc8dd14e5da0923ac038eea0c4aebd8c4",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/9df492987200d8f8de7796fdab71a39866e778ea"
        },
        "date": 1725956414251,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150850,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176208,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227090,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 261176,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 290657,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 357951,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 400455,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 435436,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 519678,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "1912ae84ba269f7886c767c19efd8e708ccecc0e",
          "message": "Fix comments on poly_tobytes() and poly_frombytes() (#116)\n\n* Fix comments on poly_tobytes() and poly_frombytes()\r\n\r\nComments now specify exact ranges of input and outputs.\r\n\r\nTo be promoted to being proper contracts in a future PR.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Update mlkem/poly.c\r\n\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>\r\nSigned-off-by: Roderick Chapman <rodchap@amazon.com>\r\n\r\n* Correct typo in comment only. Fixes #52\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Roderick Chapman <rodchap@amazon.com>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-10T09:58:31+01:00",
          "tree_id": "dc03fd0170a49ceef7abb0406c0cb453cc5f6954",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/1912ae84ba269f7886c767c19efd8e708ccecc0e"
        },
        "date": 1725959257069,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150919,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 176343,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227190,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 261627,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 291458,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 358475,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 399673,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 433818,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 519111,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "bc53aafed8422548860cad92c6f0c778f40a7292",
          "message": "Add cpucap.h header and detect AArch64 systems (#113)\n\n* Add cpucap.h header and detect AArch64 systems\r\n\r\nAlso, allow `FORCE_AARCH64` to double-check that a system is recognized\r\nas AArch64. Use this in all AArch64-based CI builds.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Don't run CBMC on free ubuntu-latest runner\r\n\r\nWe seem to be hitting resource limitations and need to consider\r\nre-enabling it on a self-hosted runner (likely EC2).\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-11T04:48:12+01:00",
          "tree_id": "b5b5c6ba6d6ad24a7b56be7d3f8bd152b4e956c0",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/bc53aafed8422548860cad92c6f0c778f40a7292"
        },
        "date": 1726027045803,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 151282,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 177590,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 228811,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 261664,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 292020,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 359589,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 398588,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 432243,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 518314,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "e3d21eb770ecc527b7b18d4e78f2806ec4e5f63d",
          "message": "Hoist CI components into reusable actions and workflows (#122)\n\n* Hoist functional tests into composite action\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hoist benchmarking into reusable job\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hoist CI components into reusable workflows\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add triggerable workflow for CI on EC2\r\n\r\nFixes #118\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Move reusable workflows into actions\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Reduce nix output\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Address review feedback\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-11T11:14:08+01:00",
          "tree_id": "8cf293d0f60c389cfe3c8b4a07bbc733a9b331e1",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/e3d21eb770ecc527b7b18d4e78f2806ec4e5f63d"
        },
        "date": 1726050195548,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 150948,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 177388,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 227747,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 260923,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 290482,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 357379,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 398740,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 432389,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 518623,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "489959ced9ed2997e41293509114589a219a2900",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/489959ced9ed2997e41293509114589a219a2900"
        },
        "date": 1726153741385,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120729,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 125762,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 149760,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 215908,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 221021,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253744,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 338960,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 344218,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 390596,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b50083388b43c0562fd336dcd065a4ec7b036ab0",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/b50083388b43c0562fd336dcd065a4ec7b036ab0"
        },
        "date": 1726156919684,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120718,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 125794,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 149784,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 215773,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 220647,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253152,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 338750,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 343363,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 385907,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "ad617bf86b504169a96dcec72219a93149bcecf2",
          "message": "Run opt/non-opt in CI (#125)\n\n* run opt/non-opt bench in ci\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* run opt/non-opt in ci\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make ci_ec2_any always lint\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix ci reusable ami id\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* wip fix store_results\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* remove inputs boolean check\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix if argument is empty string\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* update bench matrix jobs name\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* update ci opt/non-opt functest names\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-12T18:12:43+01:00",
          "tree_id": "ecbb51bba55c773f44b0aeb502aa0163efa56210",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ad617bf86b504169a96dcec72219a93149bcecf2"
        },
        "date": 1726161629147,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120679,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 127013,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 149939,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 215922,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 221259,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253072,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 338598,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 344012,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 386075,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "740bbe29f53f53b24baaa3d1a66eedfdc9bac65a",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/740bbe29f53f53b24baaa3d1a66eedfdc9bac65a"
        },
        "date": 1726163888529,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 121086,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 126536,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 150808,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 215684,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 220899,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 254341,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 338411,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 343428,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 385346,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "36c8f10a51eb420162f8ea938708c193987bb53b",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/36c8f10a51eb420162f8ea938708c193987bb53b"
        },
        "date": 1726164616241,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120615,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 125853,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 149891,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 215903,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 221207,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253825,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 338596,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 343203,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 385378,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b811694874d1dcf60be121841a37b49c681d9fac",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/b811694874d1dcf60be121841a37b49c681d9fac"
        },
        "date": 1726164875920,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120832,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 126500,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 150958,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 216334,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 221356,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253761,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 340321,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 344344,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 387119,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "5543151c04108d76829e496c994749b6583a5aeb",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/5543151c04108d76829e496c994749b6583a5aeb"
        },
        "date": 1726165389002,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120775,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 126176,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 150136,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 216342,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 221285,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253314,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 338672,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 342885,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 385389,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "f272655395f09f3811f184dbbc054d3a8930bec2",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/f272655395f09f3811f184dbbc054d3a8930bec2"
        },
        "date": 1726166094502,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120707,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 125797,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 149817,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 216529,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 221498,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 254061,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 338761,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 343456,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 387213,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "ec360c30d92c817070b79d7d453dfb4c60125a53",
          "message": "Disambiguate opt vs non-opt in benchmarking stats (#126)\n\n* Disambiguate opt vs non-opt in benchmarking stats\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Compactify bench_ec2_all.yml\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Only store optimized benchmark results\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-13T04:03:20+01:00",
          "tree_id": "e91a6ff6a461ac385aebd9bd24d8c910d760b105",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ec360c30d92c817070b79d7d453dfb4c60125a53"
        },
        "date": 1726197046969,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120798,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 126800,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 150319,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 215685,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 220575,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253001,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 338588,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 342850,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 385555,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-13T03:03:24Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9"
        },
        "date": 1726198533484,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 123162,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 128458,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 153360,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 220034,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 227797,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 259596,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 344929,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 350940,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395808,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "71b83a80d2e4e2e1ca08c2fc457a0bedfe8f51e3",
          "message": "Add native x86_64 test to CI (#127)\n\n* Add native x86_64 test to CI\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Make cross prefix configurable in benchmark action and workflow\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Don't provide default archflags in dispatchable EC2 bench flow\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-13T07:26:29+01:00",
          "tree_id": "4c694faa42f2b77fe8552cf048c82acb34d27369",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/71b83a80d2e4e2e1ca08c2fc457a0bedfe8f51e3"
        },
        "date": 1726209242689,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120792,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 127114,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 150064,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 215772,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 221188,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253938,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 339148,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 343339,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 385607,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "e4b002498cab20c6675a268320af5a7cf5f86c23",
          "message": "update DeterminateSystems to latest version",
          "timestamp": "2024-09-13T06:26:32Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/129/commits/e4b002498cab20c6675a268320af5a7cf5f86c23"
        },
        "date": 1726210945408,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120742,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 125766,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 149686,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 215672,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 220493,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 252895,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 338176,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 344165,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 385897,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "7f39c0ab7b962022f18ec2c9e614fe3081b1c56e",
          "message": "update DeterminateSystems to latest version (#129)\n\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-13T08:26:12+01:00",
          "tree_id": "92bc3a39254c2cabeaebab612a4d90c07d9c3c71",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/7f39c0ab7b962022f18ec2c9e614fe3081b1c56e"
        },
        "date": 1726212820473,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120745,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 126877,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 150416,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 215743,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 221420,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253582,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 337881,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 342914,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 384840,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "bc8569771e87ef66641996af0d400ca61d143c5f",
          "message": "X86 64 gcc",
          "timestamp": "2024-09-13T07:26:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/130/commits/bc8569771e87ef66641996af0d400ca61d143c5f"
        },
        "date": 1726461704669,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120735,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 125809,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 149749,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 215617,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 220371,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253188,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 339287,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 343210,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 385767,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "3ed1b94f4be8f53b39a6620735a96c738c2975c0",
          "message": "Fix name propagation in manually triggered CI workflow (#131)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-16T05:50:28+01:00",
          "tree_id": "8b2900c86be870cfc6bc054d7fd6d0c3c3096f39",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/3ed1b94f4be8f53b39a6620735a96c738c2975c0"
        },
        "date": 1726462688132,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120674,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 126717,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 150221,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 215680,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 221105,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253924,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 339798,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 343801,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 385871,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "640005de83fa2b47ca23d7bf76193efd1d7ba6d7",
          "message": "X86 64 gcc (#130)\n\n* add native x86_64 gcc\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* remove warning for missing GNU-stack for x86_64\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* split nix shell for native and cross gcc on x86_64 linux\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor use-nix -> nix-shell\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* update ci to use x86_64-linux-cross shell\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix nix flake\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* try fix string interpolation\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-16T06:50:11+01:00",
          "tree_id": "f6ec9096203030a564e6e165f1437623296a5677",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/640005de83fa2b47ca23d7bf76193efd1d7ba6d7"
        },
        "date": 1726466258108,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 120708,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 125909,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 149938,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 216507,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 221602,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 253842,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 338618,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 342677,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 385099,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "523d66140fd328a3eaf8272e164bfe9c9906e57b",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/523d66140fd328a3eaf8272e164bfe9c9906e57b"
        },
        "date": 1726544729181,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 144308,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 149408,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 172471,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 255215,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 261005,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 293801,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 401779,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 407993,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 451838,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "991ff695449eb2cb0c275ff8437e86bb1916571f",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/991ff695449eb2cb0c275ff8437e86bb1916571f"
        },
        "date": 1726558582229,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 143557,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 148671,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 172132,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 253780,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 258563,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 291025,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 396806,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 402289,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 444602,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "861095be62d1b8db932f1c4c83bffdb28aebffd6",
          "message": "Add scalar AArch64 Keccak-f1600 ASM (#133)\n\n* Add first AArch64 Keccak-f1600 ASM\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Update scalar Keccak ASM with A55-optimized version\r\n\r\nThis should perform decent on most microarchitectures.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Minor cleanup of auto-generated scalar Keccak-f1600 assembly\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-17T16:20:25+01:00",
          "tree_id": "664de110674e734f8b0a1c4efcdb11acd0b89d80",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/861095be62d1b8db932f1c4c83bffdb28aebffd6"
        },
        "date": 1726586917464,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 143890,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 148194,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 172270,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 254243,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 259355,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 291589,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 397986,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 404112,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 446927,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b699376c9a053b57207ec72fc29c77c549ba2e43",
          "message": "Update to FIPS203 (#96)\n\n* Update to FIPS203\r\n\r\nFollowing https://github.com/pq-crystals/kyber/commit/3c874cddd5fdaf4a7bd13f7e2e4d98a2a1eb8dc4\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* Update mlkem/indcpa.c\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:06+01:00",
          "tree_id": "850ec0275d88520f560cd46106d97d880cabeeb2",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/b699376c9a053b57207ec72fc29c77c549ba2e43"
        },
        "date": 1726628502909,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 143772,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 149305,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 172757,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 254357,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 259516,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 292204,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 398371,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 404927,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 446956,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "caa9a053645e8b02d24a9137d9b24c4809bdd8d7",
          "message": "Fix string vs. boolean in store_results argument to bench action\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:59+01:00",
          "tree_id": "d3adfb465eac34bd521db4004ca2a6a81667c774",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/caa9a053645e8b02d24a9137d9b24c4809bdd8d7"
        },
        "date": 1726628982111,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 143679,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 148876,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 171935,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 254001,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 259373,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 292417,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 397353,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 403399,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 446683,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Arm Cortex-A55 (Snapdragon 888) benchmarks": [
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "41237b36f7615fd6d17030962582268902af3156",
          "message": "Benchmarking on A55 (#84)\n\n* add exec_wrapper for tests script\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* add ci benchmark on a55 runner\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix if condition for the benchmark workflow\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make parsing of results more robust\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* log cmd on failure\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* remove taskpolicy and replace by exec_wrapper\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* refactor benchmarking yml\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* fix exec wrapper\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* add name of job\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* always turn exec wrapper into a list\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* remove duplicate test script\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* move splitting of exec wrapper\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nCo-authored-by: Matthias J. Kannwischer <matthias@kannwischer.eu>",
          "timestamp": "2024-07-02T09:50:39+01:00",
          "tree_id": "2958eba8994fdec161ca0bc185904cc972a20649",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/41237b36f7615fd6d17030962582268902af3156"
        },
        "date": 1719910559295,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 277828,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 366730,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 493524,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 475274,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 588825,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 755774,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 737681,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870690,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1077827,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c37532bef14837c88cfa797794cce5bfe1358973",
          "message": "Add coeff_signed_to_unsigned() functions and its proof (#67)\n\n* Add coeff_signed_to_unsigned() functions and its proof\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Rename coeff_signed_to_unsigned -> scalar_signed_to_unsigned_q_16\r\n\r\nAlso, uniformize file structure of proof subdirctory for\r\nscalar_signed_to_unsigned_q_16 with those of other functions.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add warning & TODO regarding potential introduction of branch\r\n\r\nscalar_signed_to_unsigned_q_16() uses the expression `(r < 0)`\r\nfor the extraction of the sign-bit, which is prone to compilers\r\nturning them into a branch.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Re-write and prove scalar_signed_to_unsigned_q_16() using cmov_int16()\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Add verify.c to proof dependencies for this function.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Increase CBMC_OBJECT_BITS for this function.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-07-02T11:27:13+01:00",
          "tree_id": "4067a9e22d19e020bba9a65eb00ac3366b500a85",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/c37532bef14837c88cfa797794cce5bfe1358973"
        },
        "date": 1719916355734,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 296007,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 369669,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 496425,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 502643,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 591725,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 758702,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 773765,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 873690,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1080893,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "dde6611ae205ba649b2e4224da2dbba3425d676f",
          "message": "Add RPi5 benchmarks (#86)\n\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>",
          "timestamp": "2024-07-02T19:34:47+01:00",
          "tree_id": "28a200c5504f1a22ed03b16b21a4e6afc4ddbedb",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/dde6611ae205ba649b2e4224da2dbba3425d676f"
        },
        "date": 1719945612181,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 295941,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 369599,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 496383,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 502648,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 591741,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 758637,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 773910,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 873782,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1081002,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "dnguye69@gmu.edu",
            "name": "Duc Tri Nguyen",
            "username": "cothan"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "88fcf89619af84a941f403cfbb02780f2c6f3b02",
          "message": "add keccakx interface (#62)\n\nSigned-off-by: Duc Tri Nguyen <dnguye69@gmu.edu>\r\n\r\nrename to x4\r\n\r\nadd shake256x4 interface\r\n\r\nadd shake256x4\r\n\r\nadd batch getnoise sampling\r\n\r\nSigned-off-by: Duc Tri Nguyen <9219016+cothan@users.noreply.github.com>\r\n\r\nunroll prf to shake256x4\r\n\r\nSigned-off-by: Duc Tri Nguyen <dnguye69@gmu.edu>\r\nSigned-off-by: Duc Tri Nguyen <9219016+cothan@users.noreply.github.com>\r\n\r\nfix space\r\n\r\nSigned-off-by: Duc Tri Nguyen <9219016+cothan@users.noreply.github.com>\r\n\r\nassume input pointers are valid, thus, remove conditions.\r\n\r\nmove memcpy outside of the loop",
          "timestamp": "2024-07-19T04:06:40+01:00",
          "tree_id": "875dd304a7e951f97e792cab580ba9f2196bf863",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/88fcf89619af84a941f403cfbb02780f2c6f3b02"
        },
        "date": 1721358744957,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297654,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368849,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495721,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510738,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596249,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763549,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771226,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 871364,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078978,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bad1095a2223a6cea6cf47b9c4966fc983ce3de8",
          "message": "Refactor nix configuration on ci and the aarch64 gcc dependency on x86_64 machines  (#89)\n\n* use nix aarch64-multiplatform gcc instead\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* cleanup arm-gnu-gcc.nix\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* expose cross_prefix for the tests script\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor with github action defaults shell feature\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make the nix config more readable\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* hide cross prefix for x86_64 machines\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* set default of cross prefix for different machines to make it clearer\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix the case if cross prefix is empty string in ci\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-07-29T18:33:53+08:00",
          "tree_id": "d427096ed306aabd1e59110ad7a85923f0f1abd0",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/bad1095a2223a6cea6cf47b9c4966fc983ce3de8"
        },
        "date": 1722249574549,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297689,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368839,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495698,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510702,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596238,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763525,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771276,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 871212,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078390,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "20c1bcacba92c7889674626f1ba0e0cf99500ee7",
          "message": "Update CBMC to v6.1.1 (#90)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-07-30T13:06:07+08:00",
          "tree_id": "e928b3a128c4713afb3c883d00638eb4fd655865",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/20c1bcacba92c7889674626f1ba0e0cf99500ee7"
        },
        "date": 1722316291253,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297671,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368799,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495633,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510681,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596082,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763122,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771353,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 871145,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078347,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "de2c8425e0e478c6643b064c037776ae0a717d31",
          "message": "Fix CBMC build on Linux and run CBMC in CI (#93)\n\n* CI: Enable CBMC on Linux\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* fix cbmc patch and refactor cbmc pkgs into cbmc folder\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* add license\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* Add cbmc version to flake.nix\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* reuse the version in cbmc/default.nix\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\nCo-authored-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-08-09T13:02:25+01:00",
          "tree_id": "58230eb2971153cd8f26344311bb0359ae081c0f",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/de2c8425e0e478c6643b064c037776ae0a717d31"
        },
        "date": 1723205282124,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297667,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368846,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495724,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510714,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596150,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763296,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771263,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 871029,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078363,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "ad56b2a1098d26c71bab6c6158a01a1c1c093aba",
          "message": "Update version and hash to specify cbmc-viewer version 3.9 (#92)\n\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>",
          "timestamp": "2024-08-11T11:58:29+08:00",
          "tree_id": "23c8d6801c91a3c906ad95434cae6f93424ee634",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ad56b2a1098d26c71bab6c6158a01a1c1c093aba"
        },
        "date": 1723349049013,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297629,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368825,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495646,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510649,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596072,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763235,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771184,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 871126,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078478,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "bd2edd6cfb22435130cd584cdfc1221466376377",
          "message": "Add workflows for benchmarking on EC2 (#99)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\nUpdate setup-nix github action",
          "timestamp": "2024-09-05T04:59:55+01:00",
          "tree_id": "dfc7dc995548de931085a140a57a48f5069424fb",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/bd2edd6cfb22435130cd584cdfc1221466376377"
        },
        "date": 1725509126849,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297682,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368827,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495748,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510680,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596102,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763225,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771118,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 871075,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078423,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "16a4c696ba752cb7e669158785b61755d91a862c",
          "message": "Push EC2 benchmark results to GH pages (#101)\n\n* Push EC2 benchmark results to GH pages\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Switch Gv2 benchmark to t4g.small\r\n\r\nAlso, use archflags instead of cflags for -mcpu setting\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-05T10:53:09+01:00",
          "tree_id": "e7a0471c2b7da5d78d8a3f110473d1b34d2cf890",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/16a4c696ba752cb7e669158785b61755d91a862c"
        },
        "date": 1725530328753,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297672,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368820,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495708,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510691,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596116,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763366,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771158,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 871081,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078453,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9a44cdc93770b6afeb161be193c9d6e0bd8c30b8",
          "message": "update aws credential to v4 (#105)\n\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-05T11:21:30+01:00",
          "tree_id": "807d87749a67ce70769d0f1ac0b43b0d6f4b858b",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/9a44cdc93770b6afeb161be193c9d6e0bd8c30b8"
        },
        "date": 1725533628900,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297656,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368814,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495660,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510623,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596033,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763162,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771113,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870908,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078462,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d72aa188854a724853a6808bfa19ef743cafcca8",
          "message": "Add proof of poly_compress() (#91)\n\n* Add contract-based proofs for compression functions\r\n\r\n- scalar_compress_q_16\r\n- scalar_compress_q_32\r\n- poly_compress\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Correct loop invariants and assigns clauses in poly_compress()\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Update poly_compress() to avoid pointer arithmetic and mutation of formal parameter r. Uses array indexing instead.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Use Bitwuzla for proof of poly_compress()\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* 1. Correct pre-condition on poly_compress()\r\n\r\n2. Remove commented-out line in body of poly_compress()\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Explicitly disable EXTERNAL_SAT_SOLVER, and use SMT2 back-end instead\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Finalize proof of poly_compress()\r\n\r\n1. Introduce common num_blocks constant to avoid repetition of \"KYBER_N / 8\"\r\n2. Add explanatory comment on switch from pointer arithmetic to array indexing\r\n   in assignment to r[]\r\n3. Introduce loop invariants for the KYBER_K=4 branch of the code.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Remove CBMC contracts on poly_decompress(). These will be re-introduced in a later PR\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Remove INDENT-ON and INDENT-OFF tags for now to keep astyle happy.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-05T20:08:22+01:00",
          "tree_id": "36933cf1671eef6052c9c107f420e7e92ee6f277",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/d72aa188854a724853a6808bfa19ef743cafcca8"
        },
        "date": 1725563636393,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297640,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368562,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495391,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510698,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 595805,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 762904,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771222,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870837,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078272,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "ry@linux.com",
            "name": "Ry Jones",
            "username": "ryjones"
          },
          "committer": {
            "email": "ry@linux.com",
            "name": "Ry Jones",
            "username": "ryjones"
          },
          "distinct": true,
          "id": "3138820190d7af42f69d148ae7b865f717f5ae6e",
          "message": "Update configure-aws-credentials to latest\n\nSigned-off-by: Ry Jones <ry@linux.com>",
          "timestamp": "2024-09-06T09:41:29-07:00",
          "tree_id": "742924c90f34428a237dd9d7ee0d5a2d5af089bd",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/3138820190d7af42f69d148ae7b865f717f5ae6e"
        },
        "date": 1725641219848,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297707,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368579,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495457,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510734,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 595970,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763078,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771161,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870865,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078146,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b9e7133a164c7f4a266009c8b1271ab2124cc4c3",
          "message": "Refactor Build System for Easier Extensibility and Future Optimizations (#100)\n\n* place all artifacts under test/build dir\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor the build system\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor build system objs macro\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make don't print directory\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* integrate the new build system to python script\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* format nix file\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix arch flags not correctly set\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* ci fix -static to be cflags\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix static compilation for benchmarking on a55\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-08T05:58:33+01:00",
          "tree_id": "5d8a46f9da0e558e3ff1f02c93884de9cc2258af",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/b9e7133a164c7f4a266009c8b1271ab2124cc4c3"
        },
        "date": 1725771842350,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297817,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495486,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510707,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 595892,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 762966,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771377,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870845,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078418,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "f4ba147375abd145b9447a8ddfbf698252c7c46d",
          "message": "Clear nix-installer cache prior to EC2 benchmarks (#108)\n\n* Allow keeping EC2 instances after workflow failures\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Clear nix-installer cache before running EC2 bench workflow\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hoist GH cache clearing into reusable action\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-09T05:29:40+01:00",
          "tree_id": "773365ad06f4cd23f411c72c5f661774ad4da6c8",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/f4ba147375abd145b9447a8ddfbf698252c7c46d"
        },
        "date": 1725856511132,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297741,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368541,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495412,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510819,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 595928,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 762984,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771295,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870773,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078141,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "a5b57128fcf5079c21af3c52595fe96f1b41876e",
          "message": "Hoist benchmarking steps into reusable GH action (#110)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nSigned-off-by: Ry Jones <ry@linux.com>",
          "timestamp": "2024-09-09T08:01:11+01:00",
          "tree_id": "3444a5bd5ad8e18c4139cff55a32144195dfe712",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/a5b57128fcf5079c21af3c52595fe96f1b41876e"
        },
        "date": 1725865609420,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297760,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368498,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495404,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510680,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 595798,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763008,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771412,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870958,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078363,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "580c136b692ff8f4b68b823e1a90c89db17448a1",
          "message": "Update CBMC to version 6.2.0 (#112)\n\n* Update CBMC to version 6.2.0\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Update version number of CBMC to 6.2.0 in flake.nix and add reminder in cbmc/default.nix to do this in future.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>",
          "timestamp": "2024-09-09T11:39:30+01:00",
          "tree_id": "8bc367c010be48281edf81e455a1241762b38b87",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/580c136b692ff8f4b68b823e1a90c89db17448a1"
        },
        "date": 1725878716515,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297775,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368626,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495465,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510738,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 595953,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 762989,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771320,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870783,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078223,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9df492987200d8f8de7796fdab71a39866e778ea",
          "message": "Fix variable detection of recursive make (#115)\n\n* fix variable detection of recursive make\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* remove the need of recursive make\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-10T09:16:17+01:00",
          "tree_id": "0353d30fc8dd14e5da0923ac038eea0c4aebd8c4",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/9df492987200d8f8de7796fdab71a39866e778ea"
        },
        "date": 1725956728163,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297705,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368597,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495444,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510970,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596088,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763249,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771451,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870992,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078360,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "1912ae84ba269f7886c767c19efd8e708ccecc0e",
          "message": "Fix comments on poly_tobytes() and poly_frombytes() (#116)\n\n* Fix comments on poly_tobytes() and poly_frombytes()\r\n\r\nComments now specify exact ranges of input and outputs.\r\n\r\nTo be promoted to being proper contracts in a future PR.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Update mlkem/poly.c\r\n\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>\r\nSigned-off-by: Roderick Chapman <rodchap@amazon.com>\r\n\r\n* Correct typo in comment only. Fixes #52\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Roderick Chapman <rodchap@amazon.com>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-10T09:58:31+01:00",
          "tree_id": "dc03fd0170a49ceef7abb0406c0cb453cc5f6954",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/1912ae84ba269f7886c767c19efd8e708ccecc0e"
        },
        "date": 1725959040076,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297698,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368587,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495482,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510923,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596060,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763272,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771337,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870907,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078542,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "bc53aafed8422548860cad92c6f0c778f40a7292",
          "message": "Add cpucap.h header and detect AArch64 systems (#113)\n\n* Add cpucap.h header and detect AArch64 systems\r\n\r\nAlso, allow `FORCE_AARCH64` to double-check that a system is recognized\r\nas AArch64. Use this in all AArch64-based CI builds.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Don't run CBMC on free ubuntu-latest runner\r\n\r\nWe seem to be hitting resource limitations and need to consider\r\nre-enabling it on a self-hosted runner (likely EC2).\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-11T04:48:12+01:00",
          "tree_id": "b5b5c6ba6d6ad24a7b56be7d3f8bd152b4e956c0",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/bc53aafed8422548860cad92c6f0c778f40a7292"
        },
        "date": 1726026823232,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297707,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368546,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495376,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 510956,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596050,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763284,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771252,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870982,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078477,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "e3d21eb770ecc527b7b18d4e78f2806ec4e5f63d",
          "message": "Hoist CI components into reusable actions and workflows (#122)\n\n* Hoist functional tests into composite action\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hoist benchmarking into reusable job\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hoist CI components into reusable workflows\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add triggerable workflow for CI on EC2\r\n\r\nFixes #118\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Move reusable workflows into actions\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Reduce nix output\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Address review feedback\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-11T11:14:08+01:00",
          "tree_id": "8cf293d0f60c389cfe3c8b4a07bbc733a9b331e1",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/e3d21eb770ecc527b7b18d4e78f2806ec4e5f63d"
        },
        "date": 1726049979813,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 297682,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 368531,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 495333,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 511019,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 596057,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 763175,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 771280,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 870944,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1078489,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "489959ced9ed2997e41293509114589a219a2900",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/489959ced9ed2997e41293509114589a219a2900"
        },
        "date": 1726153994996,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215449,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226484,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278623,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387281,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399669,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471562,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606723,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620480,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712114,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b50083388b43c0562fd336dcd065a4ec7b036ab0",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/b50083388b43c0562fd336dcd065a4ec7b036ab0"
        },
        "date": 1726156727090,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215381,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226475,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278598,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387248,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399700,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471501,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606699,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620430,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712106,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "ad617bf86b504169a96dcec72219a93149bcecf2",
          "message": "Run opt/non-opt in CI (#125)\n\n* run opt/non-opt bench in ci\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* run opt/non-opt in ci\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make ci_ec2_any always lint\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix ci reusable ami id\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* wip fix store_results\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* remove inputs boolean check\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix if argument is empty string\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* update bench matrix jobs name\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* update ci opt/non-opt functest names\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-12T18:12:43+01:00",
          "tree_id": "ecbb51bba55c773f44b0aeb502aa0163efa56210",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ad617bf86b504169a96dcec72219a93149bcecf2"
        },
        "date": 1726161437215,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215353,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226488,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278590,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387200,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399618,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471371,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606897,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620937,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712483,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "740bbe29f53f53b24baaa3d1a66eedfdc9bac65a",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/740bbe29f53f53b24baaa3d1a66eedfdc9bac65a"
        },
        "date": 1726164142512,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215456,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226523,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278647,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387251,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399611,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471451,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606754,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620886,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712148,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "36c8f10a51eb420162f8ea938708c193987bb53b",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/36c8f10a51eb420162f8ea938708c193987bb53b"
        },
        "date": 1726164420352,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215405,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226530,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278591,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387173,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399665,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471566,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606779,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620652,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712355,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b811694874d1dcf60be121841a37b49c681d9fac",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/b811694874d1dcf60be121841a37b49c681d9fac"
        },
        "date": 1726165129033,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215388,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226490,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278550,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387131,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399546,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471368,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606855,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620670,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712414,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "5543151c04108d76829e496c994749b6583a5aeb",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/5543151c04108d76829e496c994749b6583a5aeb"
        },
        "date": 1726165643480,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215371,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226509,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278549,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387307,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399706,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471517,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606900,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620789,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712417,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "f272655395f09f3811f184dbbc054d3a8930bec2",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/f272655395f09f3811f184dbbc054d3a8930bec2"
        },
        "date": 1726166358369,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215418,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226538,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278625,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387196,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399611,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471383,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606718,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620594,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712286,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "ec360c30d92c817070b79d7d453dfb4c60125a53",
          "message": "Disambiguate opt vs non-opt in benchmarking stats (#126)\n\n* Disambiguate opt vs non-opt in benchmarking stats\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Compactify bench_ec2_all.yml\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Only store optimized benchmark results\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-13T04:03:20+01:00",
          "tree_id": "e91a6ff6a461ac385aebd9bd24d8c910d760b105",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ec360c30d92c817070b79d7d453dfb4c60125a53"
        },
        "date": 1726196858821,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215388,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226487,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278531,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387109,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399544,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471432,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606860,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620917,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712182,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-13T03:03:24Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9"
        },
        "date": 1726198798004,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215385,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226438,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278601,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387145,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399544,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471306,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606833,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620916,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712107,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "71b83a80d2e4e2e1ca08c2fc457a0bedfe8f51e3",
          "message": "Add native x86_64 test to CI (#127)\n\n* Add native x86_64 test to CI\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Make cross prefix configurable in benchmark action and workflow\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Don't provide default archflags in dispatchable EC2 bench flow\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-13T07:26:29+01:00",
          "tree_id": "4c694faa42f2b77fe8552cf048c82acb34d27369",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/71b83a80d2e4e2e1ca08c2fc457a0bedfe8f51e3"
        },
        "date": 1726209048287,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215378,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226525,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278654,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387201,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399558,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471375,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606800,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620683,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712260,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "e4b002498cab20c6675a268320af5a7cf5f86c23",
          "message": "update DeterminateSystems to latest version",
          "timestamp": "2024-09-13T06:26:32Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/129/commits/e4b002498cab20c6675a268320af5a7cf5f86c23"
        },
        "date": 1726210757437,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215396,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226524,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278701,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387229,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399635,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471463,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606824,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620688,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712459,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "7f39c0ab7b962022f18ec2c9e614fe3081b1c56e",
          "message": "update DeterminateSystems to latest version (#129)\n\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-13T08:26:12+01:00",
          "tree_id": "92bc3a39254c2cabeaebab612a4d90c07d9c3c71",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/7f39c0ab7b962022f18ec2c9e614fe3081b1c56e"
        },
        "date": 1726212633895,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215381,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226543,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278605,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387135,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399527,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471348,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606798,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620956,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712250,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "bc8569771e87ef66641996af0d400ca61d143c5f",
          "message": "X86 64 gcc",
          "timestamp": "2024-09-13T07:26:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/130/commits/bc8569771e87ef66641996af0d400ca61d143c5f"
        },
        "date": 1726461511906,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215472,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226650,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278786,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387224,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399586,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471498,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606888,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620828,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712126,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "3ed1b94f4be8f53b39a6620735a96c738c2975c0",
          "message": "Fix name propagation in manually triggered CI workflow (#131)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-16T05:50:28+01:00",
          "tree_id": "8b2900c86be870cfc6bc054d7fd6d0c3c3096f39",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/3ed1b94f4be8f53b39a6620735a96c738c2975c0"
        },
        "date": 1726462498914,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215374,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226579,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278708,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387197,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399651,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471454,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606840,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620811,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712463,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "640005de83fa2b47ca23d7bf76193efd1d7ba6d7",
          "message": "X86 64 gcc (#130)\n\n* add native x86_64 gcc\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* remove warning for missing GNU-stack for x86_64\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* split nix shell for native and cross gcc on x86_64 linux\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor use-nix -> nix-shell\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* update ci to use x86_64-linux-cross shell\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix nix flake\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* try fix string interpolation\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-16T06:50:11+01:00",
          "tree_id": "f6ec9096203030a564e6e165f1437623296a5677",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/640005de83fa2b47ca23d7bf76193efd1d7ba6d7"
        },
        "date": 1726466071273,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 215432,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 226589,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 278752,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 387167,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 399648,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 471485,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 606778,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 620885,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 712189,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "523d66140fd328a3eaf8272e164bfe9c9906e57b",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/523d66140fd328a3eaf8272e164bfe9c9906e57b"
        },
        "date": 1726544970196,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 205209,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 216759,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 268957,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 370111,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 382581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 454323,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 580609,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 594318,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 685601,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "991ff695449eb2cb0c275ff8437e86bb1916571f",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/991ff695449eb2cb0c275ff8437e86bb1916571f"
        },
        "date": 1726558365064,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 201972,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 213687,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 265864,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 364610,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 377050,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 449036,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 572372,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 585661,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 677467,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "861095be62d1b8db932f1c4c83bffdb28aebffd6",
          "message": "Add scalar AArch64 Keccak-f1600 ASM (#133)\n\n* Add first AArch64 Keccak-f1600 ASM\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Update scalar Keccak ASM with A55-optimized version\r\n\r\nThis should perform decent on most microarchitectures.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Minor cleanup of auto-generated scalar Keccak-f1600 assembly\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-17T16:20:25+01:00",
          "tree_id": "664de110674e734f8b0a1c4efcdb11acd0b89d80",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/861095be62d1b8db932f1c4c83bffdb28aebffd6"
        },
        "date": 1726586680435,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 202005,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 213717,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 265829,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 364708,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 377105,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 448859,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 572354,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 585935,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 677255,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b699376c9a053b57207ec72fc29c77c549ba2e43",
          "message": "Update to FIPS203 (#96)\n\n* Update to FIPS203\r\n\r\nFollowing https://github.com/pq-crystals/kyber/commit/3c874cddd5fdaf4a7bd13f7e2e4d98a2a1eb8dc4\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* Update mlkem/indcpa.c\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:06+01:00",
          "tree_id": "850ec0275d88520f560cd46106d97d880cabeeb2",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/b699376c9a053b57207ec72fc29c77c549ba2e43"
        },
        "date": 1726628295407,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 202034,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 213731,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 265902,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 364684,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 377156,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 448886,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 572344,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 585891,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 677447,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "caa9a053645e8b02d24a9137d9b24c4809bdd8d7",
          "message": "Fix string vs. boolean in store_results argument to bench action\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:59+01:00",
          "tree_id": "d3adfb465eac34bd521db4004ca2a6a81667c774",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/caa9a053645e8b02d24a9137d9b24c4809bdd8d7"
        },
        "date": 1726628778670,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 201987,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 213662,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 265789,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 364815,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 377183,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 448998,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 572261,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 585687,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 677493,
            "unit": "cycles"
          }
        ]
      },
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
        "date": 1726725028080,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 170737,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 184510,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 236673,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 311244,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 323529,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 395773,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 487616,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 499500,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 591060,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Arm Cortex-A76 (Raspberry Pi 5) benchmarks": [
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "dde6611ae205ba649b2e4224da2dbba3425d676f",
          "message": "Add RPi5 benchmarks (#86)\n\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>",
          "timestamp": "2024-07-02T19:34:47+01:00",
          "tree_id": "28a200c5504f1a22ed03b16b21a4e6afc4ddbedb",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/dde6611ae205ba649b2e4224da2dbba3425d676f"
        },
        "date": 1719945394253,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 117802,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138685,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178585,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 197305,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 222097,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 274374,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305313,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330894,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396033,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "dnguye69@gmu.edu",
            "name": "Duc Tri Nguyen",
            "username": "cothan"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "88fcf89619af84a941f403cfbb02780f2c6f3b02",
          "message": "add keccakx interface (#62)\n\nSigned-off-by: Duc Tri Nguyen <dnguye69@gmu.edu>\r\n\r\nrename to x4\r\n\r\nadd shake256x4 interface\r\n\r\nadd shake256x4\r\n\r\nadd batch getnoise sampling\r\n\r\nSigned-off-by: Duc Tri Nguyen <9219016+cothan@users.noreply.github.com>\r\n\r\nunroll prf to shake256x4\r\n\r\nSigned-off-by: Duc Tri Nguyen <dnguye69@gmu.edu>\r\nSigned-off-by: Duc Tri Nguyen <9219016+cothan@users.noreply.github.com>\r\n\r\nfix space\r\n\r\nSigned-off-by: Duc Tri Nguyen <9219016+cothan@users.noreply.github.com>\r\n\r\nassume input pointers are valid, thus, remove conditions.\r\n\r\nmove memcpy outside of the loop",
          "timestamp": "2024-07-19T04:06:40+01:00",
          "tree_id": "875dd304a7e951f97e792cab580ba9f2196bf863",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/88fcf89619af84a941f403cfbb02780f2c6f3b02"
        },
        "date": 1721358510973,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 123401,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 140697,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 183055,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200762,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 224161,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276268,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306095,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 331024,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396199,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bad1095a2223a6cea6cf47b9c4966fc983ce3de8",
          "message": "Refactor nix configuration on ci and the aarch64 gcc dependency on x86_64 machines  (#89)\n\n* use nix aarch64-multiplatform gcc instead\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* cleanup arm-gnu-gcc.nix\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* expose cross_prefix for the tests script\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor with github action defaults shell feature\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make the nix config more readable\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* hide cross prefix for x86_64 machines\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* set default of cross prefix for different machines to make it clearer\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix the case if cross prefix is empty string in ci\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-07-29T18:33:53+08:00",
          "tree_id": "d427096ed306aabd1e59110ad7a85923f0f1abd0",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/bad1095a2223a6cea6cf47b9c4966fc983ce3de8"
        },
        "date": 1722249346977,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 123429,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 140757,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 183174,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200806,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 224259,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276362,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306033,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 331041,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396201,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "20c1bcacba92c7889674626f1ba0e0cf99500ee7",
          "message": "Update CBMC to v6.1.1 (#90)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-07-30T13:06:07+08:00",
          "tree_id": "e928b3a128c4713afb3c883d00638eb4fd655865",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/20c1bcacba92c7889674626f1ba0e0cf99500ee7"
        },
        "date": 1722316078070,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 123420,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 140747,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 183113,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200744,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 224285,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276376,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306209,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 331135,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396271,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "de2c8425e0e478c6643b064c037776ae0a717d31",
          "message": "Fix CBMC build on Linux and run CBMC in CI (#93)\n\n* CI: Enable CBMC on Linux\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* fix cbmc patch and refactor cbmc pkgs into cbmc folder\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* add license\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* Add cbmc version to flake.nix\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* reuse the version in cbmc/default.nix\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\nCo-authored-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-08-09T13:02:25+01:00",
          "tree_id": "58230eb2971153cd8f26344311bb0359ae081c0f",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/de2c8425e0e478c6643b064c037776ae0a717d31"
        },
        "date": 1723205062306,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 123412,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 140721,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 183097,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200750,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 224173,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276299,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305952,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330958,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396168,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "ad56b2a1098d26c71bab6c6158a01a1c1c093aba",
          "message": "Update version and hash to specify cbmc-viewer version 3.9 (#92)\n\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>",
          "timestamp": "2024-08-11T11:58:29+08:00",
          "tree_id": "23c8d6801c91a3c906ad95434cae6f93424ee634",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ad56b2a1098d26c71bab6c6158a01a1c1c093aba"
        },
        "date": 1723348830753,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 123418,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 140718,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 183099,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200724,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 224130,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276202,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305842,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330897,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396045,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "bd2edd6cfb22435130cd584cdfc1221466376377",
          "message": "Add workflows for benchmarking on EC2 (#99)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\nUpdate setup-nix github action",
          "timestamp": "2024-09-05T04:59:55+01:00",
          "tree_id": "dfc7dc995548de931085a140a57a48f5069424fb",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/bd2edd6cfb22435130cd584cdfc1221466376377"
        },
        "date": 1725508911406,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 123442,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 140757,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 183131,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200759,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 224225,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276334,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306057,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330954,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396162,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "16a4c696ba752cb7e669158785b61755d91a862c",
          "message": "Push EC2 benchmark results to GH pages (#101)\n\n* Push EC2 benchmark results to GH pages\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Switch Gv2 benchmark to t4g.small\r\n\r\nAlso, use archflags instead of cflags for -mcpu setting\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-05T10:53:09+01:00",
          "tree_id": "e7a0471c2b7da5d78d8a3f110473d1b34d2cf890",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/16a4c696ba752cb7e669158785b61755d91a862c"
        },
        "date": 1725530157292,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 123423,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 140798,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 183180,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200799,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 224205,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276322,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305949,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330943,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396113,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9a44cdc93770b6afeb161be193c9d6e0bd8c30b8",
          "message": "update aws credential to v4 (#105)\n\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-05T11:21:30+01:00",
          "tree_id": "807d87749a67ce70769d0f1ac0b43b0d6f4b858b",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/9a44cdc93770b6afeb161be193c9d6e0bd8c30b8"
        },
        "date": 1725531804034,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 123427,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 140740,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 183120,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200754,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 224174,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276250,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306039,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330959,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396092,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d72aa188854a724853a6808bfa19ef743cafcca8",
          "message": "Add proof of poly_compress() (#91)\n\n* Add contract-based proofs for compression functions\r\n\r\n- scalar_compress_q_16\r\n- scalar_compress_q_32\r\n- poly_compress\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Correct loop invariants and assigns clauses in poly_compress()\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Update poly_compress() to avoid pointer arithmetic and mutation of formal parameter r. Uses array indexing instead.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Use Bitwuzla for proof of poly_compress()\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* 1. Correct pre-condition on poly_compress()\r\n\r\n2. Remove commented-out line in body of poly_compress()\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Explicitly disable EXTERNAL_SAT_SOLVER, and use SMT2 back-end instead\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Finalize proof of poly_compress()\r\n\r\n1. Introduce common num_blocks constant to avoid repetition of \"KYBER_N / 8\"\r\n2. Add explanatory comment on switch from pointer arithmetic to array indexing\r\n   in assignment to r[]\r\n3. Introduce loop invariants for the KYBER_K=4 branch of the code.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Remove CBMC contracts on poly_decompress(). These will be re-introduced in a later PR\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Remove INDENT-ON and INDENT-OFF tags for now to keep astyle happy.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-05T20:08:22+01:00",
          "tree_id": "36933cf1671eef6052c9c107f420e7e92ee6f277",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/d72aa188854a724853a6808bfa19ef743cafcca8"
        },
        "date": 1725563414752,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 123391,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 140620,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 183015,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200716,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223948,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276074,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306038,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 331366,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396739,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "ry@linux.com",
            "name": "Ry Jones",
            "username": "ryjones"
          },
          "committer": {
            "email": "ry@linux.com",
            "name": "Ry Jones",
            "username": "ryjones"
          },
          "distinct": true,
          "id": "3138820190d7af42f69d148ae7b865f717f5ae6e",
          "message": "Update configure-aws-credentials to latest\n\nSigned-off-by: Ry Jones <ry@linux.com>",
          "timestamp": "2024-09-06T09:41:29-07:00",
          "tree_id": "742924c90f34428a237dd9d7ee0d5a2d5af089bd",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/3138820190d7af42f69d148ae7b865f717f5ae6e"
        },
        "date": 1725640999679,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 123377,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 140683,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 182880,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200966,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223857,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276229,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306177,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 331524,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396762,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b9e7133a164c7f4a266009c8b1271ab2124cc4c3",
          "message": "Refactor Build System for Easier Extensibility and Future Optimizations (#100)\n\n* place all artifacts under test/build dir\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor the build system\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor build system objs macro\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make don't print directory\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* integrate the new build system to python script\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* format nix file\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix arch flags not correctly set\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* ci fix -static to be cflags\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix static compilation for benchmarking on a55\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-08T05:58:33+01:00",
          "tree_id": "5d8a46f9da0e558e3ff1f02c93884de9cc2258af",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/b9e7133a164c7f4a266009c8b1271ab2124cc4c3"
        },
        "date": 1725771629604,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118629,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138360,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178228,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200511,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223382,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275998,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306054,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330715,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396234,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "f4ba147375abd145b9447a8ddfbf698252c7c46d",
          "message": "Clear nix-installer cache prior to EC2 benchmarks (#108)\n\n* Allow keeping EC2 instances after workflow failures\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Clear nix-installer cache before running EC2 bench workflow\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hoist GH cache clearing into reusable action\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-09T05:29:40+01:00",
          "tree_id": "773365ad06f4cd23f411c72c5f661774ad4da6c8",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/f4ba147375abd145b9447a8ddfbf698252c7c46d"
        },
        "date": 1725856289845,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118644,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138473,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178331,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200592,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223410,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276003,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305935,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330745,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396207,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "a5b57128fcf5079c21af3c52595fe96f1b41876e",
          "message": "Hoist benchmarking steps into reusable GH action (#110)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nSigned-off-by: Ry Jones <ry@linux.com>",
          "timestamp": "2024-09-09T08:01:11+01:00",
          "tree_id": "3444a5bd5ad8e18c4139cff55a32144195dfe712",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/a5b57128fcf5079c21af3c52595fe96f1b41876e"
        },
        "date": 1725865412620,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118660,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138447,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178313,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200635,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223484,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276128,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306012,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330711,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396155,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "580c136b692ff8f4b68b823e1a90c89db17448a1",
          "message": "Update CBMC to version 6.2.0 (#112)\n\n* Update CBMC to version 6.2.0\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Update version number of CBMC to 6.2.0 in flake.nix and add reminder in cbmc/default.nix to do this in future.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>",
          "timestamp": "2024-09-09T11:39:30+01:00",
          "tree_id": "8bc367c010be48281edf81e455a1241762b38b87",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/580c136b692ff8f4b68b823e1a90c89db17448a1"
        },
        "date": 1725878499164,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118640,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138307,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178144,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200692,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223503,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276152,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306052,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330880,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396434,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9df492987200d8f8de7796fdab71a39866e778ea",
          "message": "Fix variable detection of recursive make (#115)\n\n* fix variable detection of recursive make\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* remove the need of recursive make\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-10T09:16:17+01:00",
          "tree_id": "0353d30fc8dd14e5da0923ac038eea0c4aebd8c4",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/9df492987200d8f8de7796fdab71a39866e778ea"
        },
        "date": 1725956289400,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118600,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138388,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178231,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200550,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223323,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275969,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306107,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330919,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396511,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "1912ae84ba269f7886c767c19efd8e708ccecc0e",
          "message": "Fix comments on poly_tobytes() and poly_frombytes() (#116)\n\n* Fix comments on poly_tobytes() and poly_frombytes()\r\n\r\nComments now specify exact ranges of input and outputs.\r\n\r\nTo be promoted to being proper contracts in a future PR.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Update mlkem/poly.c\r\n\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>\r\nSigned-off-by: Roderick Chapman <rodchap@amazon.com>\r\n\r\n* Correct typo in comment only. Fixes #52\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\nSigned-off-by: Roderick Chapman <rodchap@amazon.com>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-10T09:58:31+01:00",
          "tree_id": "dc03fd0170a49ceef7abb0406c0cb453cc5f6954",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/1912ae84ba269f7886c767c19efd8e708ccecc0e"
        },
        "date": 1725958820549,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118597,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138320,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178171,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200522,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223337,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275995,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306103,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330938,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396425,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "bc53aafed8422548860cad92c6f0c778f40a7292",
          "message": "Add cpucap.h header and detect AArch64 systems (#113)\n\n* Add cpucap.h header and detect AArch64 systems\r\n\r\nAlso, allow `FORCE_AARCH64` to double-check that a system is recognized\r\nas AArch64. Use this in all AArch64-based CI builds.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Don't run CBMC on free ubuntu-latest runner\r\n\r\nWe seem to be hitting resource limitations and need to consider\r\nre-enabling it on a self-hosted runner (likely EC2).\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-11T04:48:12+01:00",
          "tree_id": "b5b5c6ba6d6ad24a7b56be7d3f8bd152b4e956c0",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/bc53aafed8422548860cad92c6f0c778f40a7292"
        },
        "date": 1726026602945,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118630,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138342,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178187,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200627,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223387,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276043,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306221,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330878,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396469,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "e3d21eb770ecc527b7b18d4e78f2806ec4e5f63d",
          "message": "Hoist CI components into reusable actions and workflows (#122)\n\n* Hoist functional tests into composite action\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hoist benchmarking into reusable job\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Hoist CI components into reusable workflows\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Add triggerable workflow for CI on EC2\r\n\r\nFixes #118\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Move reusable workflows into actions\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Reduce nix output\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Address review feedback\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-11T11:14:08+01:00",
          "tree_id": "8cf293d0f60c389cfe3c8b4a07bbc733a9b331e1",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/e3d21eb770ecc527b7b18d4e78f2806ec4e5f63d"
        },
        "date": 1726049759612,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118509,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138277,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178236,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200592,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223396,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275747,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 306136,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 331041,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 396483,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "489959ced9ed2997e41293509114589a219a2900",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/489959ced9ed2997e41293509114589a219a2900"
        },
        "date": 1726153626484,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93266,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95380,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112633,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162680,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164675,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187764,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254795,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255379,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285425,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "1b8da6bfccfed736f2ea945cb441f79b38b2c2c9",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/1b8da6bfccfed736f2ea945cb441f79b38b2c2c9"
        },
        "date": 1726156128935,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93296,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95404,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112638,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162647,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164691,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187788,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254837,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255418,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285478,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "6896e1ae5a48bffe3d2e7f12fb5d4ad929c45a57",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/6896e1ae5a48bffe3d2e7f12fb5d4ad929c45a57"
        },
        "date": 1726156301260,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93265,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95380,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112629,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162667,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164725,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187801,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254712,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255328,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285319,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b50083388b43c0562fd336dcd065a4ec7b036ab0",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/b50083388b43c0562fd336dcd065a4ec7b036ab0"
        },
        "date": 1726156529309,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93261,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95309,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162725,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164686,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187781,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254857,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255385,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285428,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "ad617bf86b504169a96dcec72219a93149bcecf2",
          "message": "Run opt/non-opt in CI (#125)\n\n* run opt/non-opt bench in ci\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* run opt/non-opt in ci\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make ci_ec2_any always lint\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix ci reusable ami id\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* wip fix store_results\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* remove inputs boolean check\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix if argument is empty string\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* update bench matrix jobs name\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* update ci opt/non-opt functest names\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-12T18:12:43+01:00",
          "tree_id": "ecbb51bba55c773f44b0aeb502aa0163efa56210",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ad617bf86b504169a96dcec72219a93149bcecf2"
        },
        "date": 1726161260421,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93156,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95370,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112639,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162533,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164631,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187956,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 255205,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255760,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285934,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "740bbe29f53f53b24baaa3d1a66eedfdc9bac65a",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/740bbe29f53f53b24baaa3d1a66eedfdc9bac65a"
        },
        "date": 1726163765482,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93176,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95508,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112615,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162756,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164571,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187942,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254864,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255526,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285554,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "36c8f10a51eb420162f8ea938708c193987bb53b",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/36c8f10a51eb420162f8ea938708c193987bb53b"
        },
        "date": 1726163890872,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93197,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95453,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112563,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162772,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164527,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187927,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254986,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255489,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285585,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b811694874d1dcf60be121841a37b49c681d9fac",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/b811694874d1dcf60be121841a37b49c681d9fac"
        },
        "date": 1726164173267,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93212,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112714,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162765,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164577,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187974,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254951,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255379,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285426,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "5543151c04108d76829e496c994749b6583a5aeb",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/5543151c04108d76829e496c994749b6583a5aeb"
        },
        "date": 1726164278059,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93216,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95457,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112568,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162811,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164543,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187941,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254726,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255330,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285407,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "f272655395f09f3811f184dbbc054d3a8930bec2",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/f272655395f09f3811f184dbbc054d3a8930bec2"
        },
        "date": 1726165974965,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93294,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95341,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112607,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162657,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164626,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187734,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254867,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255458,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285458,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "ec360c30d92c817070b79d7d453dfb4c60125a53",
          "message": "Disambiguate opt vs non-opt in benchmarking stats (#126)\n\n* Disambiguate opt vs non-opt in benchmarking stats\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Compactify bench_ec2_all.yml\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Only store optimized benchmark results\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-13T04:03:20+01:00",
          "tree_id": "e91a6ff6a461ac385aebd9bd24d8c910d760b105",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ec360c30d92c817070b79d7d453dfb4c60125a53"
        },
        "date": 1726196694367,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93194,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95479,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112741,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162462,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164555,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187853,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 255221,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255671,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285878,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-13T03:03:24Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9"
        },
        "date": 1726198413992,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93253,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95351,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112598,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162675,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164686,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187756,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 255025,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255517,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285611,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "71b83a80d2e4e2e1ca08c2fc457a0bedfe8f51e3",
          "message": "Add native x86_64 test to CI (#127)\n\n* Add native x86_64 test to CI\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Make cross prefix configurable in benchmark action and workflow\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Don't provide default archflags in dispatchable EC2 bench flow\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-13T07:26:29+01:00",
          "tree_id": "4c694faa42f2b77fe8552cf048c82acb34d27369",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/71b83a80d2e4e2e1ca08c2fc457a0bedfe8f51e3"
        },
        "date": 1726208882288,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93139,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95387,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112653,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162540,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164616,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187929,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 255173,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255680,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285864,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "e4b002498cab20c6675a268320af5a7cf5f86c23",
          "message": "update DeterminateSystems to latest version",
          "timestamp": "2024-09-13T06:26:32Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/129/commits/e4b002498cab20c6675a268320af5a7cf5f86c23"
        },
        "date": 1726210591739,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93298,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95374,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112648,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162565,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164628,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187702,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254740,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255355,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285450,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "7f39c0ab7b962022f18ec2c9e614fe3081b1c56e",
          "message": "update DeterminateSystems to latest version (#129)\n\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-13T08:26:12+01:00",
          "tree_id": "92bc3a39254c2cabeaebab612a4d90c07d9c3c71",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/7f39c0ab7b962022f18ec2c9e614fe3081b1c56e"
        },
        "date": 1726212470265,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93159,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95479,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112741,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162517,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164579,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187879,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 255194,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255708,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285903,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "bc8569771e87ef66641996af0d400ca61d143c5f",
          "message": "X86 64 gcc",
          "timestamp": "2024-09-13T07:26:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/130/commits/bc8569771e87ef66641996af0d400ca61d143c5f"
        },
        "date": 1726461350546,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93268,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95422,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112693,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162734,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164717,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187810,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254890,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255458,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285495,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "3ed1b94f4be8f53b39a6620735a96c738c2975c0",
          "message": "Fix name propagation in manually triggered CI workflow (#131)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-16T05:50:28+01:00",
          "tree_id": "8b2900c86be870cfc6bc054d7fd6d0c3c3096f39",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/3ed1b94f4be8f53b39a6620735a96c738c2975c0"
        },
        "date": 1726462336897,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93144,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95463,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112729,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162502,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164550,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187904,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 255129,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255727,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285927,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "640005de83fa2b47ca23d7bf76193efd1d7ba6d7",
          "message": "X86 64 gcc (#130)\n\n* add native x86_64 gcc\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* remove warning for missing GNU-stack for x86_64\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* split nix shell for native and cross gcc on x86_64 linux\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* refactor use-nix -> nix-shell\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* update ci to use x86_64-linux-cross shell\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix nix flake\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* try fix string interpolation\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-16T06:50:11+01:00",
          "tree_id": "f6ec9096203030a564e6e165f1437623296a5677",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/640005de83fa2b47ca23d7bf76193efd1d7ba6d7"
        },
        "date": 1726465906431,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93159,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95340,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112628,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162534,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164584,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187909,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 255167,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 255666,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 285814,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "523d66140fd328a3eaf8272e164bfe9c9906e57b",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/523d66140fd328a3eaf8272e164bfe9c9906e57b"
        },
        "date": 1726544598348,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84335,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86795,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103999,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147790,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 149666,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 173007,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 232450,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 232500,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 262562,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "991ff695449eb2cb0c275ff8437e86bb1916571f",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/991ff695449eb2cb0c275ff8437e86bb1916571f"
        },
        "date": 1726558201927,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84154,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86668,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103875,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147504,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 149430,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172751,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 231931,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 232143,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 262198,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "861095be62d1b8db932f1c4c83bffdb28aebffd6",
          "message": "Add scalar AArch64 Keccak-f1600 ASM (#133)\n\n* Add first AArch64 Keccak-f1600 ASM\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Update scalar Keccak ASM with A55-optimized version\r\n\r\nThis should perform decent on most microarchitectures.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Minor cleanup of auto-generated scalar Keccak-f1600 assembly\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-17T16:20:25+01:00",
          "tree_id": "664de110674e734f8b0a1c4efcdb11acd0b89d80",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/861095be62d1b8db932f1c4c83bffdb28aebffd6"
        },
        "date": 1726586517131,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84054,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86672,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103949,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147512,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 149452,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172892,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 231698,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 231858,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 261929,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b699376c9a053b57207ec72fc29c77c549ba2e43",
          "message": "Update to FIPS203 (#96)\n\n* Update to FIPS203\r\n\r\nFollowing https://github.com/pq-crystals/kyber/commit/3c874cddd5fdaf4a7bd13f7e2e4d98a2a1eb8dc4\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* Update mlkem/indcpa.c\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:06+01:00",
          "tree_id": "850ec0275d88520f560cd46106d97d880cabeeb2",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/b699376c9a053b57207ec72fc29c77c549ba2e43"
        },
        "date": 1726628137002,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84112,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86694,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103929,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147421,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 149438,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172879,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 231873,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 231426,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 261412,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "caa9a053645e8b02d24a9137d9b24c4809bdd8d7",
          "message": "Fix string vs. boolean in store_results argument to bench action\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:59+01:00",
          "tree_id": "d3adfb465eac34bd521db4004ca2a6a81667c774",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/caa9a053645e8b02d24a9137d9b24c4809bdd8d7"
        },
        "date": 1726628234971,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84143,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86717,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103961,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147497,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 149476,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172922,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 231983,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 231685,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 261711,
            "unit": "cycles"
          }
        ]
      },
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
        "date": 1726724899720,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 70570,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 73834,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 91041,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 124812,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 126022,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 149595,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 195514,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 194788,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 224563,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton2": [
      {
        "commit": {
          "author": {
            "name": "Hanno Becker",
            "username": "hanno-becker",
            "email": "beckphan@amazon.co.uk"
          },
          "committer": {
            "name": "Hanno Becker",
            "username": "hanno-becker",
            "email": "beckphan@amazon.co.uk"
          },
          "id": "2c82074ecfea1bb8de4f005f101b59eb36f5bf35",
          "message": "Push EC2 benchmark results to GH pages\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-05T04:11:31Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/2c82074ecfea1bb8de4f005f101b59eb36f5bf35"
        },
        "date": 1725512989929,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118579,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138922,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178852,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200425,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223240,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275527,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305157,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330628,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395044,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "07bc1c0ab93459cf85d80d5fdf994ae422308714",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/07bc1c0ab93459cf85d80d5fdf994ae422308714"
        },
        "date": 1725525605293,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118564,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138897,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178826,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200438,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223315,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275579,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304903,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329714,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394687,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "07bc1c0ab93459cf85d80d5fdf994ae422308714",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/07bc1c0ab93459cf85d80d5fdf994ae422308714"
        },
        "date": 1725525895249,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118518,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138843,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178774,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200194,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223142,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275432,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304547,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329613,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394582,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "07bc1c0ab93459cf85d80d5fdf994ae422308714",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/07bc1c0ab93459cf85d80d5fdf994ae422308714"
        },
        "date": 1725526196309,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118597,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138961,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178875,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200033,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223037,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275399,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305103,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330027,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395001,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "07bc1c0ab93459cf85d80d5fdf994ae422308714",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/07bc1c0ab93459cf85d80d5fdf994ae422308714"
        },
        "date": 1725526458618,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138866,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178797,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200485,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223258,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275530,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305153,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330119,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395151,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "07bc1c0ab93459cf85d80d5fdf994ae422308714",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/07bc1c0ab93459cf85d80d5fdf994ae422308714"
        },
        "date": 1725526904436,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118566,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138903,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178826,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200316,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223130,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275397,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305022,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329877,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394897,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "07bc1c0ab93459cf85d80d5fdf994ae422308714",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/07bc1c0ab93459cf85d80d5fdf994ae422308714"
        },
        "date": 1725527524350,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118538,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138887,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178805,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200509,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223280,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275515,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304930,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329692,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394646,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "5c37d4e30b41ec5c1f4c60e5bc1ccec6dfc06824",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/5c37d4e30b41ec5c1f4c60e5bc1ccec6dfc06824"
        },
        "date": 1725528568245,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118591,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138965,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178889,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200571,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223304,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275563,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304818,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329690,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394708,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "16a4c696ba752cb7e669158785b61755d91a862c",
          "message": "Push EC2 benchmark results to GH pages (#101)\n\n* Push EC2 benchmark results to GH pages\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Switch Gv2 benchmark to t4g.small\r\n\r\nAlso, use archflags instead of cflags for -mcpu setting\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-05T10:53:09+01:00",
          "tree_id": "e7a0471c2b7da5d78d8a3f110473d1b34d2cf890",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/16a4c696ba752cb7e669158785b61755d91a862c"
        },
        "date": 1725530670628,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118630,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138923,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178855,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200511,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223396,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275669,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305164,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329939,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394989,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Hanno Becker",
            "username": "hanno-becker",
            "email": "beckphan@amazon.co.uk"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "16a4c696ba752cb7e669158785b61755d91a862c",
          "message": "Push EC2 benchmark results to GH pages (#101)\n\n* Push EC2 benchmark results to GH pages\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Switch Gv2 benchmark to t4g.small\r\n\r\nAlso, use archflags instead of cflags for -mcpu setting\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-05T09:53:09Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/16a4c696ba752cb7e669158785b61755d91a862c"
        },
        "date": 1725530994309,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118584,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138985,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178823,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200464,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223387,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275928,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305185,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330029,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395143,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "f87c9a1729b7966baa476d0d4c94d6bf61be62c8",
          "message": "[DO NOT MERGE] Test pr",
          "timestamp": "2024-09-05T09:53:13Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/103/commits/f87c9a1729b7966baa476d0d4c94d6bf61be62c8"
        },
        "date": 1725531347587,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118544,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138910,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178828,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200406,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223260,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275490,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305218,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330154,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395157,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "d313c18bfd649e90f6d0b26dfe6df8344f64ff05",
          "message": "Test pr",
          "timestamp": "2024-09-05T09:53:13Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/104/commits/d313c18bfd649e90f6d0b26dfe6df8344f64ff05"
        },
        "date": 1725531525823,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 119064,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138837,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178735,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200634,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223299,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275724,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304864,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330161,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395486,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9a44cdc93770b6afeb161be193c9d6e0bd8c30b8",
          "message": "update aws credential to v4 (#105)\n\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-05T11:21:30+01:00",
          "tree_id": "807d87749a67ce70769d0f1ac0b43b0d6f4b858b",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/9a44cdc93770b6afeb161be193c9d6e0bd8c30b8"
        },
        "date": 1725531931751,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118548,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138909,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178854,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200505,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223241,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275476,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305145,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329969,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395102,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "586ace356a5702d39ae4a30f4765ee6442943c92",
          "message": "Test pr",
          "timestamp": "2024-09-05T10:21:34Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/104/commits/586ace356a5702d39ae4a30f4765ee6442943c92"
        },
        "date": 1725532284695,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 119100,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138907,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178791,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200738,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223401,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275813,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304821,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330146,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395352,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "7037c9f4621d6231db916e5d022a4283c933f619",
          "message": "Refactor build system (duplicated)",
          "timestamp": "2024-09-05T10:21:34Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/102/commits/7037c9f4621d6231db916e5d022a4283c933f619"
        },
        "date": 1725532336172,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118493,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138954,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 179523,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200552,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223502,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275887,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304862,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 330187,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395366,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "4d58f198d6543c6758807352be214f4aff7d83fc",
          "message": "Hoist benchmarking steps into reusable Github action",
          "timestamp": "2024-09-08T04:58:37Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/110/commits/4d58f198d6543c6758807352be214f4aff7d83fc"
        },
        "date": 1725853384272,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118491,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138763,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178603,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200817,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223331,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275801,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304259,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329259,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394264,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "a5b57128fcf5079c21af3c52595fe96f1b41876e",
          "message": "Hoist benchmarking steps into reusable GH action (#110)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nSigned-off-by: Ry Jones <ry@linux.com>",
          "timestamp": "2024-09-09T08:01:11+01:00",
          "tree_id": "3444a5bd5ad8e18c4139cff55a32144195dfe712",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/a5b57128fcf5079c21af3c52595fe96f1b41876e"
        },
        "date": 1725865617094,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118453,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138692,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178664,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200480,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223198,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275556,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304675,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329474,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394738,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "807cf4e0deba488391ea1870179a479d13e55572",
          "message": "Basic ntt",
          "timestamp": "2024-09-09T07:01:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/109/commits/807cf4e0deba488391ea1870179a479d13e55572"
        },
        "date": 1725874184248,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118808,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138694,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178627,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200594,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223377,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275707,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304822,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329683,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395049,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "d170147ab09f9cf005bdaf22e8cb74e3205f7e01",
          "message": "Basic ntt",
          "timestamp": "2024-09-09T10:39:35Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/109/commits/d170147ab09f9cf005bdaf22e8cb74e3205f7e01"
        },
        "date": 1725879276708,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118486,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138792,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178682,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200531,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223420,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275959,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 302494,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 327782,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 393528,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "580c136b692ff8f4b68b823e1a90c89db17448a1",
          "message": "Update CBMC to version 6.2.0 (#112)\n\n* Update CBMC to version 6.2.0\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Update version number of CBMC to 6.2.0 in flake.nix and add reminder in cbmc/default.nix to do this in future.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>",
          "timestamp": "2024-09-09T11:39:30+01:00",
          "tree_id": "8bc367c010be48281edf81e455a1241762b38b87",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/580c136b692ff8f4b68b823e1a90c89db17448a1"
        },
        "date": 1725884182651,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118439,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138684,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178637,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200421,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223262,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275573,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304560,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329366,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394501,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "9d76e914972a066823bad46df936a73c1d2c2d37",
          "message": "Add cpucap.h header and detect AArch64 systems",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/113/commits/9d76e914972a066823bad46df936a73c1d2c2d37"
        },
        "date": 1725959525992,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118788,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138695,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178642,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200483,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223265,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275610,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304698,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329481,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394638,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b31b8d78cc66f0c2cefa7628a1759513dd40e922",
          "message": "Add cpucap.h header and detect AArch64 systems",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/113/commits/b31b8d78cc66f0c2cefa7628a1759513dd40e922"
        },
        "date": 1725963733533,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118751,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138629,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178574,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200559,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223370,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275695,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304742,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329272,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394532,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "9b4aa78fe5657fe9254bf56f6e77dca11e45d6bb",
          "message": "Add cpucap.h header and detect AArch64 systems",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/113/commits/9b4aa78fe5657fe9254bf56f6e77dca11e45d6bb"
        },
        "date": 1725996817040,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 119115,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138766,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178683,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200749,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223210,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275653,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 302654,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 327537,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 393208,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "207f19da6a30c3ccc4ae721b7d3446104180e777",
          "message": "Add cpucap.h header and detect AArch64 systems",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/113/commits/207f19da6a30c3ccc4ae721b7d3446104180e777"
        },
        "date": 1725998362774,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 119091,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138755,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178632,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200721,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223154,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275592,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304488,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329447,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394700,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "650f2f8fcd76b1a5a73c1dfa4b5b9fce49bfc72a",
          "message": "Add cpucap.h header and detect AArch64 systems",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/113/commits/650f2f8fcd76b1a5a73c1dfa4b5b9fce49bfc72a"
        },
        "date": 1725998949708,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118964,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138659,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178585,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200517,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223104,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275538,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304281,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329146,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394297,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "d6ccc55750763e0ee608fe95b3f0b6eed7c9f4f8",
          "message": "Hoist CI components into reusable actions and workflows",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/122/commits/d6ccc55750763e0ee608fe95b3f0b6eed7c9f4f8"
        },
        "date": 1726025175528,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118966,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138686,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178656,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200734,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223314,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275745,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304448,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329357,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394470,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "daac3707aa4299b913e8ada495172e78520f9bc2",
          "message": "Hoist CI components into reusable actions and workflows",
          "timestamp": "2024-09-11T03:48:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/122/commits/daac3707aa4299b913e8ada495172e78520f9bc2"
        },
        "date": 1726026852619,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 119082,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138721,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178623,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200603,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223173,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275580,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304174,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329030,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394254,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "fd31b31ff8786b76a56775a7562de36d15a3da7e",
          "message": "Hoist CI components into reusable actions and workflows",
          "timestamp": "2024-09-11T03:48:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/122/commits/fd31b31ff8786b76a56775a7562de36d15a3da7e"
        },
        "date": 1726040139048,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118819,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138724,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178653,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200089,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223178,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275715,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304056,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 328641,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 393841,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "726f0624a0ef0a935696847eb4c3e4d5bda89b53",
          "message": "Hoist CI components into reusable actions and workflows",
          "timestamp": "2024-09-11T03:48:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/122/commits/726f0624a0ef0a935696847eb4c3e4d5bda89b53"
        },
        "date": 1726040568524,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118683,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138636,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178613,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200503,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223372,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275704,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304770,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329603,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394870,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "cb9c3543e7cc96fe2a27742c3e1caea17c6e3a3d",
          "message": "Hoist CI components into reusable actions and workflows",
          "timestamp": "2024-09-11T03:48:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/122/commits/cb9c3543e7cc96fe2a27742c3e1caea17c6e3a3d"
        },
        "date": 1726049108232,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118825,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138683,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178603,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200587,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223324,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275668,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 303708,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 328379,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 393554,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "dc668f488c76ed0dd23074501d6e572aaef9b612",
          "message": "CI fixes",
          "timestamp": "2024-09-11T10:14:12Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/123/commits/dc668f488c76ed0dd23074501d6e572aaef9b612"
        },
        "date": 1726054961145,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118808,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138669,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178589,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200365,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223171,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275549,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304689,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329441,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394681,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Thing-han, Lim",
            "username": "potsrevennil",
            "email": "15379156+potsrevennil@users.noreply.github.com"
          },
          "committer": {
            "name": "Thing-han, Lim",
            "username": "potsrevennil",
            "email": "15379156+potsrevennil@users.noreply.github.com"
          },
          "id": "8b629dddfd0733db6c9724e471f0a2c1f2289ca1",
          "message": "wip fix store_results\n\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-12T06:58:13Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/8b629dddfd0733db6c9724e471f0a2c1f2289ca1"
        },
        "date": 1726126425567,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 92985,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95144,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112462,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162100,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 163994,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187066,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 253537,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 253532,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 283161,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Thing-han, Lim",
            "username": "potsrevennil",
            "email": "15379156+potsrevennil@users.noreply.github.com"
          },
          "committer": {
            "name": "Thing-han, Lim",
            "username": "potsrevennil",
            "email": "15379156+potsrevennil@users.noreply.github.com"
          },
          "id": "489959ced9ed2997e41293509114589a219a2900",
          "message": "fix if argument is empty string\n\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-12T07:51:55Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/489959ced9ed2997e41293509114589a219a2900"
        },
        "date": 1726153248378,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93168,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95255,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112507,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162593,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164210,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187290,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 253821,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 253927,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 283674,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "489959ced9ed2997e41293509114589a219a2900",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/489959ced9ed2997e41293509114589a219a2900"
        },
        "date": 1726153760158,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93065,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95254,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112529,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162473,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164081,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187357,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 253911,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 253602,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 283455,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "489959ced9ed2997e41293509114589a219a2900",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/489959ced9ed2997e41293509114589a219a2900"
        },
        "date": 1726153848044,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118396,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138659,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178639,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200179,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 222978,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275352,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304439,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329203,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394328,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b50083388b43c0562fd336dcd065a4ec7b036ab0",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/b50083388b43c0562fd336dcd065a4ec7b036ab0"
        },
        "date": 1726156654420,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93234,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95328,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112450,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162432,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 163866,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187322,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254167,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 254058,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 283919,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b50083388b43c0562fd336dcd065a4ec7b036ab0",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/b50083388b43c0562fd336dcd065a4ec7b036ab0"
        },
        "date": 1726156801550,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118473,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138758,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178599,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200335,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223772,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 276737,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304947,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329942,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395226,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b811694874d1dcf60be121841a37b49c681d9fac",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/b811694874d1dcf60be121841a37b49c681d9fac"
        },
        "date": 1726164321513,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118518,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138783,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178619,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200430,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223302,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275905,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305028,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329732,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394973,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "5543151c04108d76829e496c994749b6583a5aeb",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/5543151c04108d76829e496c994749b6583a5aeb"
        },
        "date": 1726164327689,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93234,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95332,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112441,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162559,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164084,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187497,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 252274,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 253075,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 283530,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "5543151c04108d76829e496c994749b6583a5aeb",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/5543151c04108d76829e496c994749b6583a5aeb"
        },
        "date": 1726164359965,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118531,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138825,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178683,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200463,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223364,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275922,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305117,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329900,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395191,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b811694874d1dcf60be121841a37b49c681d9fac",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/b811694874d1dcf60be121841a37b49c681d9fac"
        },
        "date": 1726164462976,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93201,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95294,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112422,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162368,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 163800,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187286,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 253821,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 253578,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 283332,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "f272655395f09f3811f184dbbc054d3a8930bec2",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/f272655395f09f3811f184dbbc054d3a8930bec2"
        },
        "date": 1726166097357,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118508,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138787,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178640,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200526,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223430,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275963,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 305150,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329938,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 395252,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Lim, Thing-han",
            "username": "potsrevennil",
            "email": "15379156+potsrevennil@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "ad617bf86b504169a96dcec72219a93149bcecf2",
          "message": "Run opt/non-opt in CI (#125)\n\n* run opt/non-opt bench in ci\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* run opt/non-opt in ci\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* make ci_ec2_any always lint\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix ci reusable ami id\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* wip fix store_results\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* remove inputs boolean check\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* fix if argument is empty string\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* update bench matrix jobs name\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n* update ci opt/non-opt functest names\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-12T17:12:43Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ad617bf86b504169a96dcec72219a93149bcecf2"
        },
        "date": 1726167069126,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93108,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95358,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112473,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162684,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164036,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187406,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 253972,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 253856,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 283780,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "ec360c30d92c817070b79d7d453dfb4c60125a53",
          "message": "Disambiguate opt vs non-opt in benchmarking stats (#126)\n\n* Disambiguate opt vs non-opt in benchmarking stats\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Compactify bench_ec2_all.yml\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Only store optimized benchmark results\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-13T04:03:20+01:00",
          "tree_id": "e91a6ff6a461ac385aebd9bd24d8c910d760b105",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ec360c30d92c817070b79d7d453dfb4c60125a53"
        },
        "date": 1726197029389,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93258,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95350,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112460,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162071,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 163637,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187264,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 252779,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 252645,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 282480,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-13T03:03:24Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9"
        },
        "date": 1726198557022,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93124,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95251,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112375,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162545,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 163918,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187352,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 252419,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 252349,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 282238,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-13T03:03:24Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9"
        },
        "date": 1726198561097,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118332,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138779,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178727,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200334,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223063,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275532,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304867,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329727,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394922,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "e4b002498cab20c6675a268320af5a7cf5f86c23",
          "message": "update DeterminateSystems to latest version",
          "timestamp": "2024-09-13T06:26:32Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/129/commits/e4b002498cab20c6675a268320af5a7cf5f86c23"
        },
        "date": 1726210799059,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118493,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138715,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178520,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200534,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223021,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275448,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304579,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329507,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394710,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "e4b002498cab20c6675a268320af5a7cf5f86c23",
          "message": "update DeterminateSystems to latest version",
          "timestamp": "2024-09-13T06:26:32Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/129/commits/e4b002498cab20c6675a268320af5a7cf5f86c23"
        },
        "date": 1726210868870,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93103,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95251,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112440,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162556,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 163993,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187474,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 253749,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 253547,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 283437,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "e4b002498cab20c6675a268320af5a7cf5f86c23",
          "message": "update DeterminateSystems to latest version",
          "timestamp": "2024-09-13T06:26:32Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/129/commits/e4b002498cab20c6675a268320af5a7cf5f86c23"
        },
        "date": 1726211763069,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93101,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95332,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112448,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162608,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 163912,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187274,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 252857,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 252649,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 282489,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "e4b002498cab20c6675a268320af5a7cf5f86c23",
          "message": "update DeterminateSystems to latest version",
          "timestamp": "2024-09-13T06:26:32Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/129/commits/e4b002498cab20c6675a268320af5a7cf5f86c23"
        },
        "date": 1726211879251,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118484,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138810,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178677,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200408,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223244,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275783,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304589,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329376,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394663,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "bc8569771e87ef66641996af0d400ca61d143c5f",
          "message": "X86 64 gcc",
          "timestamp": "2024-09-13T07:26:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/130/commits/bc8569771e87ef66641996af0d400ca61d143c5f"
        },
        "date": 1726461524781,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118519,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138776,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178622,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200480,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223420,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275983,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304559,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329337,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394498,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "bc8569771e87ef66641996af0d400ca61d143c5f",
          "message": "X86 64 gcc",
          "timestamp": "2024-09-13T07:26:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/130/commits/bc8569771e87ef66641996af0d400ca61d143c5f"
        },
        "date": 1726461653301,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93063,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95297,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112405,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162743,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 164118,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187474,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 251750,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 251974,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 282007,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "3ed1b94f4be8f53b39a6620735a96c738c2975c0",
          "message": "Fix name propagation in manually triggered CI workflow (#131)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-16T05:50:28+01:00",
          "tree_id": "8b2900c86be870cfc6bc054d7fd6d0c3c3096f39",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/3ed1b94f4be8f53b39a6620735a96c738c2975c0"
        },
        "date": 1726462490437,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 93253,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 95357,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 112502,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 162570,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 163987,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 187514,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 254380,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 254204,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 284025,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Hanno Becker",
            "username": "hanno-becker",
            "email": "beckphan@amazon.co.uk"
          },
          "committer": {
            "name": "Hanno Becker",
            "username": "hanno-becker",
            "email": "beckphan@amazon.co.uk"
          },
          "id": "523d66140fd328a3eaf8272e164bfe9c9906e57b",
          "message": "Add first AArch64 Keccak-f1600 ASM\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-16T19:04:24Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/523d66140fd328a3eaf8272e164bfe9c9906e57b"
        },
        "date": 1726515499539,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84204,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86688,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 104060,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 148624,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 149758,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 173399,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 229482,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 229822,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 259977,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "523d66140fd328a3eaf8272e164bfe9c9906e57b",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/523d66140fd328a3eaf8272e164bfe9c9906e57b"
        },
        "date": 1726544759703,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84150,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86727,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103927,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147272,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 149016,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172411,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 230769,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 230196,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 260252,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "523d66140fd328a3eaf8272e164bfe9c9906e57b",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/523d66140fd328a3eaf8272e164bfe9c9906e57b"
        },
        "date": 1726544850232,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118421,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138780,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178793,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200359,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223204,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275924,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304548,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329271,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394439,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "991ff695449eb2cb0c275ff8437e86bb1916571f",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/991ff695449eb2cb0c275ff8437e86bb1916571f"
        },
        "date": 1726558367115,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84021,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86636,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103804,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147411,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 149061,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172286,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 230928,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 230338,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 260234,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "991ff695449eb2cb0c275ff8437e86bb1916571f",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/991ff695449eb2cb0c275ff8437e86bb1916571f"
        },
        "date": 1726558379972,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118496,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138847,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178706,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200775,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223291,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275761,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 303096,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 328049,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 393232,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Hanno Becker",
            "username": "hanno-becker",
            "email": "beckphan@amazon.co.uk"
          },
          "committer": {
            "name": "Hanno Becker",
            "username": "hanno-becker",
            "email": "beckphan@amazon.co.uk"
          },
          "id": "991ff695449eb2cb0c275ff8437e86bb1916571f",
          "message": "Minor cleanup of auto-generated scalar Keccak-f1600 assembly\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-17T07:27:04Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/991ff695449eb2cb0c275ff8437e86bb1916571f"
        },
        "date": 1726559081558,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84249,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86705,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 104016,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 148385,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 149544,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 173251,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 228377,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 229065,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 259251,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "861095be62d1b8db932f1c4c83bffdb28aebffd6",
          "message": "Add scalar AArch64 Keccak-f1600 ASM (#133)\n\n* Add first AArch64 Keccak-f1600 ASM\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Update scalar Keccak ASM with A55-optimized version\r\n\r\nThis should perform decent on most microarchitectures.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Minor cleanup of auto-generated scalar Keccak-f1600 assembly\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-17T16:20:25+01:00",
          "tree_id": "664de110674e734f8b0a1c4efcdb11acd0b89d80",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/861095be62d1b8db932f1c4c83bffdb28aebffd6"
        },
        "date": 1726586671367,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 83971,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86437,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103629,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147615,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148936,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172169,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 229020,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 228508,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 258469,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "861095be62d1b8db932f1c4c83bffdb28aebffd6",
          "message": "Add scalar AArch64 Keccak-f1600 ASM (#133)\n\n* Add first AArch64 Keccak-f1600 ASM\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Update scalar Keccak ASM with A55-optimized version\r\n\r\nThis should perform decent on most microarchitectures.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Minor cleanup of auto-generated scalar Keccak-f1600 assembly\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-17T16:20:25+01:00",
          "tree_id": "664de110674e734f8b0a1c4efcdb11acd0b89d80",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/861095be62d1b8db932f1c4c83bffdb28aebffd6"
        },
        "date": 1726586703102,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118511,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138832,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178671,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200180,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223029,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275705,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 304540,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 329211,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 394465,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b699376c9a053b57207ec72fc29c77c549ba2e43",
          "message": "Update to FIPS203 (#96)\n\n* Update to FIPS203\r\n\r\nFollowing https://github.com/pq-crystals/kyber/commit/3c874cddd5fdaf4a7bd13f7e2e4d98a2a1eb8dc4\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* Update mlkem/indcpa.c\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:06+01:00",
          "tree_id": "850ec0275d88520f560cd46106d97d880cabeeb2",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/b699376c9a053b57207ec72fc29c77c549ba2e43"
        },
        "date": 1726628260785,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84110,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86576,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103753,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147589,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148980,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172229,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 229980,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 229362,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 259106,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b699376c9a053b57207ec72fc29c77c549ba2e43",
          "message": "Update to FIPS203 (#96)\n\n* Update to FIPS203\r\n\r\nFollowing https://github.com/pq-crystals/kyber/commit/3c874cddd5fdaf4a7bd13f7e2e4d98a2a1eb8dc4\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* Update mlkem/indcpa.c\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:06+01:00",
          "tree_id": "850ec0275d88520f560cd46106d97d880cabeeb2",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/b699376c9a053b57207ec72fc29c77c549ba2e43"
        },
        "date": 1726628301124,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 118490,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 138790,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 178641,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 200460,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 223211,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 275791,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 314339,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 334966,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 405135,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "caa9a053645e8b02d24a9137d9b24c4809bdd8d7",
          "message": "Fix string vs. boolean in store_results argument to bench action\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:59+01:00",
          "tree_id": "d3adfb465eac34bd521db4004ca2a6a81667c774",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/caa9a053645e8b02d24a9137d9b24c4809bdd8d7"
        },
        "date": 1726628317342,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84102,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86532,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103694,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147255,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148660,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 171891,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 228943,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 228547,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 258423,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "4262d514ad483c8e39be87455b4b4d955c703b16",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/4262d514ad483c8e39be87455b4b4d955c703b16"
        },
        "date": 1726640989825,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84122,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86600,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103765,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147388,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148928,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172208,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 230997,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 230430,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 260274,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "00b2cfec2172c00e789cf685058b79735399c165",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/00b2cfec2172c00e789cf685058b79735399c165"
        },
        "date": 1726647636254,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84094,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86575,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103781,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147448,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148938,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172238,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 230894,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 230320,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 260162,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "cc7e7686ded32046e8a7d6005d18cef028a0ee61",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/cc7e7686ded32046e8a7d6005d18cef028a0ee61"
        },
        "date": 1726652066096,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84098,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86574,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103774,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147257,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148733,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172006,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 230983,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 230332,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 260164,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "00b2cfec2172c00e789cf685058b79735399c165",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/00b2cfec2172c00e789cf685058b79735399c165"
        },
        "date": 1726655935153,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84097,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86573,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103767,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147430,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148918,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172196,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 230222,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 229502,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 259400,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "be360b371042dbbc01fd655fed02ed8a11aeb679",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/be360b371042dbbc01fd655fed02ed8a11aeb679"
        },
        "date": 1726658171589,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84116,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86587,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103780,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147405,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148933,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172215,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 230959,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 230463,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 260309,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "c828defe7e099389bc428a5984898e828f7ae672",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/c828defe7e099389bc428a5984898e828f7ae672"
        },
        "date": 1726659699372,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84077,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86535,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103737,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 146907,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148447,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 171818,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 231176,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 230585,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 260414,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b235606ed2def0ae8a43a389d19b74cfce70325b",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/b235606ed2def0ae8a43a389d19b74cfce70325b"
        },
        "date": 1726665850021,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84100,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86586,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103794,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147395,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148822,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172083,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 231073,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 230666,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 260496,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "17afb81634bd3991d7c05f450875e185b6e116fd",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/17afb81634bd3991d7c05f450875e185b6e116fd"
        },
        "date": 1726666628098,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84112,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86600,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103765,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147427,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148800,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172101,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 231011,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 230546,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 260419,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "a8362423aaf292e4ca412537a793ba38b4fbd60e",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/a8362423aaf292e4ca412537a793ba38b4fbd60e"
        },
        "date": 1726666941400,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 83976,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86665,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 104100,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147236,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148904,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172224,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 228961,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 228806,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 258864,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "08f9c50bd926dcf28c317c221a973fd02b4029e5",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/08f9c50bd926dcf28c317c221a973fd02b4029e5"
        },
        "date": 1726667727898,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84107,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86583,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103767,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 146859,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148579,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172019,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 228393,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 228389,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 258607,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "9fb8c22ade8309298c12e51be9e021ebaed96049",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/9fb8c22ade8309298c12e51be9e021ebaed96049"
        },
        "date": 1726667763094,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84089,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103763,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 146991,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148570,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 171893,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 230838,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 230296,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 260157,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "29b727eaccaf45928f11bc2e9c0cd505ba3ef9bd",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/29b727eaccaf45928f11bc2e9c0cd505ba3ef9bd"
        },
        "date": 1726678324464,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 84067,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86534,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103717,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 146979,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148616,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 171956,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 228961,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 228623,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 258613,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "bdb21c1b3b8a76d934ef650daa89343253007245",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/bdb21c1b3b8a76d934ef650daa89343253007245"
        },
        "date": 1726678595856,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 83921,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 86540,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 103877,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 147386,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 148887,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 172202,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 230988,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 230460,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 260280,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "ef9f482bf9740c8b74365c01efb90a3b6b054ac5",
          "message": "Add batched Keccak ASM",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/137/commits/ef9f482bf9740c8b74365c01efb90a3b6b054ac5"
        },
        "date": 1726717813862,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 70645,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 74416,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 91570,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 124578,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 125765,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 149147,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 193702,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 192662,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 222488,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "2dfa2212b326312a7412684c0650315af035522a",
          "message": "Add hybrid Neon/Neon Keccak-f1600, don't use scalar ASM on Cortex-A72",
          "timestamp": "2024-09-19T04:51:50Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/139/commits/2dfa2212b326312a7412684c0650315af035522a"
        },
        "date": 1726724626064,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 79575,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 83069,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 100404,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 139754,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 140800,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 164313,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 217630,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 217343,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 247003,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton3": [
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "07bc1c0ab93459cf85d80d5fdf994ae422308714",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/07bc1c0ab93459cf85d80d5fdf994ae422308714"
        },
        "date": 1725525567957,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 75554,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 87404,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 111926,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127956,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141864,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174147,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192438,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209207,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249735,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "07bc1c0ab93459cf85d80d5fdf994ae422308714",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/07bc1c0ab93459cf85d80d5fdf994ae422308714"
        },
        "date": 1725525860088,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 75541,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 87427,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 111945,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127965,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141875,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174154,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192427,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209187,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249731,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "07bc1c0ab93459cf85d80d5fdf994ae422308714",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/07bc1c0ab93459cf85d80d5fdf994ae422308714"
        },
        "date": 1725526142922,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 75553,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 87428,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 111950,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127984,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141915,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174165,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192450,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209178,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249743,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "07bc1c0ab93459cf85d80d5fdf994ae422308714",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/07bc1c0ab93459cf85d80d5fdf994ae422308714"
        },
        "date": 1725526867296,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 75561,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 87402,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 111911,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127969,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141886,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174182,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192429,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209157,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249705,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "07bc1c0ab93459cf85d80d5fdf994ae422308714",
          "message": "Push EC2 benchmark results to GH pages",
          "timestamp": "2024-09-05T03:59:59Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/101/commits/07bc1c0ab93459cf85d80d5fdf994ae422308714"
        },
        "date": 1725527488351,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 75556,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 87406,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 111926,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127965,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141868,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174141,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192435,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209186,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249693,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Hanno Becker",
            "username": "hanno-becker",
            "email": "beckphan@amazon.co.uk"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "16a4c696ba752cb7e669158785b61755d91a862c",
          "message": "Push EC2 benchmark results to GH pages (#101)\n\n* Push EC2 benchmark results to GH pages\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Switch Gv2 benchmark to t4g.small\r\n\r\nAlso, use archflags instead of cflags for -mcpu setting\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-05T09:53:09Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/16a4c696ba752cb7e669158785b61755d91a862c"
        },
        "date": 1725530984260,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 75590,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 87570,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 111881,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127878,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 142131,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174421,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192244,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209146,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249633,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "d313c18bfd649e90f6d0b26dfe6df8344f64ff05",
          "message": "Test pr",
          "timestamp": "2024-09-05T09:53:13Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/104/commits/d313c18bfd649e90f6d0b26dfe6df8344f64ff05"
        },
        "date": 1725531489592,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 82364,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89854,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 117614,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128051,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141768,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174107,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192264,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209169,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249695,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "f87c9a1729b7966baa476d0d4c94d6bf61be62c8",
          "message": "[DO NOT MERGE] Test pr",
          "timestamp": "2024-09-05T09:53:13Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/103/commits/f87c9a1729b7966baa476d0d4c94d6bf61be62c8"
        },
        "date": 1725531515866,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 75552,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 87399,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 111943,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127956,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141882,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174154,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192455,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209181,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249705,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "15379156+potsrevennil@users.noreply.github.com",
            "name": "Lim, Thing-han",
            "username": "potsrevennil"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9a44cdc93770b6afeb161be193c9d6e0bd8c30b8",
          "message": "update aws credential to v4 (#105)\n\nSigned-off-by: Thing-han, Lim <15379156+potsrevennil@users.noreply.github.com>",
          "timestamp": "2024-09-05T11:21:30+01:00",
          "tree_id": "807d87749a67ce70769d0f1ac0b43b0d6f4b858b",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/9a44cdc93770b6afeb161be193c9d6e0bd8c30b8"
        },
        "date": 1725531896711,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 75553,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 87400,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 111909,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127944,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141890,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174134,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192486,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209182,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249696,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "586ace356a5702d39ae4a30f4765ee6442943c92",
          "message": "Test pr",
          "timestamp": "2024-09-05T10:21:34Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/104/commits/586ace356a5702d39ae4a30f4765ee6442943c92"
        },
        "date": 1725532251595,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 82353,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89826,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 117595,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128055,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141773,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174114,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192285,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209178,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249719,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "a5b57128fcf5079c21af3c52595fe96f1b41876e",
          "message": "Hoist benchmarking steps into reusable GH action (#110)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nSigned-off-by: Ry Jones <ry@linux.com>",
          "timestamp": "2024-09-09T08:01:11+01:00",
          "tree_id": "3444a5bd5ad8e18c4139cff55a32144195dfe712",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/a5b57128fcf5079c21af3c52595fe96f1b41876e"
        },
        "date": 1725865668703,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80570,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89922,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116938,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128028,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141872,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174122,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192376,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209170,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249701,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "807cf4e0deba488391ea1870179a479d13e55572",
          "message": "Basic ntt",
          "timestamp": "2024-09-09T07:01:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/109/commits/807cf4e0deba488391ea1870179a479d13e55572"
        },
        "date": 1725874193348,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80582,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89946,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116869,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127887,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 142065,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174338,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192493,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209435,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249964,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "d170147ab09f9cf005bdaf22e8cb74e3205f7e01",
          "message": "Basic ntt",
          "timestamp": "2024-09-09T10:39:35Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/109/commits/d170147ab09f9cf005bdaf22e8cb74e3205f7e01"
        },
        "date": 1725879240740,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 81029,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89787,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116864,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127981,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141857,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174150,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192460,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209349,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249897,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "rodchap@amazon.com",
            "name": "Roderick Chapman",
            "username": "rod-chapman"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "580c136b692ff8f4b68b823e1a90c89db17448a1",
          "message": "Update CBMC to version 6.2.0 (#112)\n\n* Update CBMC to version 6.2.0\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n* Update version number of CBMC to 6.2.0 in flake.nix and add reminder in cbmc/default.nix to do this in future.\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>\r\n\r\n---------\r\n\r\nSigned-off-by: Rod Chapman <rodchap@amazon.com>",
          "timestamp": "2024-09-09T11:39:30+01:00",
          "tree_id": "8bc367c010be48281edf81e455a1241762b38b87",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/580c136b692ff8f4b68b823e1a90c89db17448a1"
        },
        "date": 1725883939337,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80566,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89868,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116884,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128037,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141868,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174129,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192393,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209156,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249692,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "9d76e914972a066823bad46df936a73c1d2c2d37",
          "message": "Add cpucap.h header and detect AArch64 systems",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/113/commits/9d76e914972a066823bad46df936a73c1d2c2d37"
        },
        "date": 1725959505313,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 81012,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89829,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116954,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127932,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141852,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174151,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192430,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209216,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249728,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b31b8d78cc66f0c2cefa7628a1759513dd40e922",
          "message": "Add cpucap.h header and detect AArch64 systems",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/113/commits/b31b8d78cc66f0c2cefa7628a1759513dd40e922"
        },
        "date": 1725963808809,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 81005,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89809,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116941,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127926,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141840,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174149,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192428,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209220,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249710,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "9b4aa78fe5657fe9254bf56f6e77dca11e45d6bb",
          "message": "Add cpucap.h header and detect AArch64 systems",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/113/commits/9b4aa78fe5657fe9254bf56f6e77dca11e45d6bb"
        },
        "date": 1725996784976,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 82299,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89790,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 117583,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128030,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141789,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174083,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192231,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209111,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249602,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "207f19da6a30c3ccc4ae721b7d3446104180e777",
          "message": "Add cpucap.h header and detect AArch64 systems",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/113/commits/207f19da6a30c3ccc4ae721b7d3446104180e777"
        },
        "date": 1725998192161,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 82312,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 90062,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 117960,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128013,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141773,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174063,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192298,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209288,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249741,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "650f2f8fcd76b1a5a73c1dfa4b5b9fce49bfc72a",
          "message": "Add cpucap.h header and detect AArch64 systems",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/113/commits/650f2f8fcd76b1a5a73c1dfa4b5b9fce49bfc72a"
        },
        "date": 1725998898483,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 82311,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89774,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 117578,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128021,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 142107,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174519,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192264,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209114,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249589,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "d6ccc55750763e0ee608fe95b3f0b6eed7c9f4f8",
          "message": "Hoist CI components into reusable actions and workflows",
          "timestamp": "2024-09-10T08:58:53Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/122/commits/d6ccc55750763e0ee608fe95b3f0b6eed7c9f4f8"
        },
        "date": 1726025175239,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 82310,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89779,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 117571,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128011,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141757,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174075,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192309,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209275,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249698,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "daac3707aa4299b913e8ada495172e78520f9bc2",
          "message": "Hoist CI components into reusable actions and workflows",
          "timestamp": "2024-09-11T03:48:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/122/commits/daac3707aa4299b913e8ada495172e78520f9bc2"
        },
        "date": 1726026831428,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 82312,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89798,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 117589,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128025,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141738,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174094,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192319,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209302,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249732,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "fd31b31ff8786b76a56775a7562de36d15a3da7e",
          "message": "Hoist CI components into reusable actions and workflows",
          "timestamp": "2024-09-11T03:48:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/122/commits/fd31b31ff8786b76a56775a7562de36d15a3da7e"
        },
        "date": 1726040337142,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80994,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 90050,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 117273,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127927,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141839,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174124,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192524,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209228,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249700,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "726f0624a0ef0a935696847eb4c3e4d5bda89b53",
          "message": "Hoist CI components into reusable actions and workflows",
          "timestamp": "2024-09-11T03:48:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/122/commits/726f0624a0ef0a935696847eb4c3e4d5bda89b53"
        },
        "date": 1726040560258,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 81004,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89819,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116952,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127919,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141851,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174133,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192424,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209262,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249765,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "cb9c3543e7cc96fe2a27742c3e1caea17c6e3a3d",
          "message": "Hoist CI components into reusable actions and workflows",
          "timestamp": "2024-09-11T03:48:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/122/commits/cb9c3543e7cc96fe2a27742c3e1caea17c6e3a3d"
        },
        "date": 1726049178149,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80997,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89802,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116922,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127925,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141834,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174140,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192446,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209195,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249706,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "dc668f488c76ed0dd23074501d6e572aaef9b612",
          "message": "CI fixes",
          "timestamp": "2024-09-11T10:14:12Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/123/commits/dc668f488c76ed0dd23074501d6e572aaef9b612"
        },
        "date": 1726054945827,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 81001,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89785,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116907,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127930,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141840,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174129,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192422,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209230,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249730,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "489959ced9ed2997e41293509114589a219a2900",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/489959ced9ed2997e41293509114589a219a2900"
        },
        "date": 1726153744749,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 59633,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60627,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 70990,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104133,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 104940,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 118991,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160710,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162213,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180551,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "489959ced9ed2997e41293509114589a219a2900",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/489959ced9ed2997e41293509114589a219a2900"
        },
        "date": 1726153873423,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80427,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89858,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116952,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127927,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141843,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174104,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192594,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209465,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249967,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b50083388b43c0562fd336dcd065a4ec7b036ab0",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/b50083388b43c0562fd336dcd065a4ec7b036ab0"
        },
        "date": 1726156691726,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 59686,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60847,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 71005,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104037,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 105091,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 119216,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160718,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162196,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180528,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b50083388b43c0562fd336dcd065a4ec7b036ab0",
          "message": "Run opt/non-opt in CI",
          "timestamp": "2024-09-12T06:22:06Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/125/commits/b50083388b43c0562fd336dcd065a4ec7b036ab0"
        },
        "date": 1726156706079,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80528,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89997,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116884,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127841,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141983,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174298,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192559,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209447,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249936,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b811694874d1dcf60be121841a37b49c681d9fac",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/b811694874d1dcf60be121841a37b49c681d9fac"
        },
        "date": 1726164273284,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 59695,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60839,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 71019,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104025,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 105084,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 119201,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160717,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162229,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180543,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "5543151c04108d76829e496c994749b6583a5aeb",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/5543151c04108d76829e496c994749b6583a5aeb"
        },
        "date": 1726164346467,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80532,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 90029,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116887,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127850,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 142010,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174331,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192575,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209510,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249984,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b811694874d1dcf60be121841a37b49c681d9fac",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/b811694874d1dcf60be121841a37b49c681d9fac"
        },
        "date": 1726164353010,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80541,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 90034,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116921,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127847,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 142009,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174365,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192578,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209449,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249929,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "5543151c04108d76829e496c994749b6583a5aeb",
          "message": "Disambiguate opt vs non-opt in benchmarking stats",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/126/commits/5543151c04108d76829e496c994749b6583a5aeb"
        },
        "date": 1726164450166,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 59677,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60876,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 71006,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104031,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 105088,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 119231,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160704,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162195,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180523,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "f272655395f09f3811f184dbbc054d3a8930bec2",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/f272655395f09f3811f184dbbc054d3a8930bec2"
        },
        "date": 1726166070335,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 59637,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60648,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 70999,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104141,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 104931,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 118993,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160728,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162234,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180533,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "f272655395f09f3811f184dbbc054d3a8930bec2",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-12T17:12:47Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/f272655395f09f3811f184dbbc054d3a8930bec2"
        },
        "date": 1726166100511,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80550,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 90033,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116917,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127851,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 142011,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174331,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192564,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209442,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249917,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "ec360c30d92c817070b79d7d453dfb4c60125a53",
          "message": "Disambiguate opt vs non-opt in benchmarking stats (#126)\n\n* Disambiguate opt vs non-opt in benchmarking stats\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Compactify bench_ec2_all.yml\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Only store optimized benchmark results\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-13T04:03:20+01:00",
          "tree_id": "e91a6ff6a461ac385aebd9bd24d8c910d760b105",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/ec360c30d92c817070b79d7d453dfb4c60125a53"
        },
        "date": 1726197072906,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 60195,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60626,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 70986,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104139,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 104950,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 119029,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160666,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162152,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180517,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-13T03:03:24Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9"
        },
        "date": 1726198517966,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 59671,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60580,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 71040,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104152,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 104849,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 118997,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160505,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162519,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180176,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9",
          "message": "Add native x86_64 test to CI",
          "timestamp": "2024-09-13T03:03:24Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/127/commits/1777c7cf8abf10ea2e95bc71d7a943e85a8b54c9"
        },
        "date": 1726198548256,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80490,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89745,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116905,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128015,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141732,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174136,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192304,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209817,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249644,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "71b83a80d2e4e2e1ca08c2fc457a0bedfe8f51e3",
          "message": "Add native x86_64 test to CI (#127)\n\n* Add native x86_64 test to CI\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Make cross prefix configurable in benchmark action and workflow\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Don't provide default archflags in dispatchable EC2 bench flow\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-13T07:26:29+01:00",
          "tree_id": "4c694faa42f2b77fe8552cf048c82acb34d27369",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/71b83a80d2e4e2e1ca08c2fc457a0bedfe8f51e3"
        },
        "date": 1726208995603,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 60172,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60617,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 70975,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104149,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 104943,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 119022,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160650,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162153,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180517,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "e4b002498cab20c6675a268320af5a7cf5f86c23",
          "message": "update DeterminateSystems to latest version",
          "timestamp": "2024-09-13T06:26:32Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/129/commits/e4b002498cab20c6675a268320af5a7cf5f86c23"
        },
        "date": 1726210778469,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80496,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89766,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116920,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128009,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141748,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174101,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192312,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209840,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249597,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "e4b002498cab20c6675a268320af5a7cf5f86c23",
          "message": "update DeterminateSystems to latest version",
          "timestamp": "2024-09-13T06:26:32Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/129/commits/e4b002498cab20c6675a268320af5a7cf5f86c23"
        },
        "date": 1726211048811,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 59683,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60847,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 71010,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104019,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 105090,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 119193,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160503,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162526,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180179,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "e4b002498cab20c6675a268320af5a7cf5f86c23",
          "message": "update DeterminateSystems to latest version",
          "timestamp": "2024-09-13T06:26:32Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/129/commits/e4b002498cab20c6675a268320af5a7cf5f86c23"
        },
        "date": 1726211767773,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80528,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 90043,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116891,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127822,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 142076,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174343,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192279,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209795,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249629,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "e4b002498cab20c6675a268320af5a7cf5f86c23",
          "message": "update DeterminateSystems to latest version",
          "timestamp": "2024-09-13T06:26:32Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/129/commits/e4b002498cab20c6675a268320af5a7cf5f86c23"
        },
        "date": 1726211808671,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 59676,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60822,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 71001,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104018,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 105092,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 119209,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160502,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162530,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180170,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "bc8569771e87ef66641996af0d400ca61d143c5f",
          "message": "X86 64 gcc",
          "timestamp": "2024-09-13T07:26:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/130/commits/bc8569771e87ef66641996af0d400ca61d143c5f"
        },
        "date": 1726461469017,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 59660,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60595,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 71037,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104165,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 104861,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 118981,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160496,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162515,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180190,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "bc8569771e87ef66641996af0d400ca61d143c5f",
          "message": "X86 64 gcc",
          "timestamp": "2024-09-13T07:26:16Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/130/commits/bc8569771e87ef66641996af0d400ca61d143c5f"
        },
        "date": 1726461475116,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80541,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 90316,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 117304,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127846,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141994,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174324,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192289,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209799,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249585,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "3ed1b94f4be8f53b39a6620735a96c738c2975c0",
          "message": "Fix name propagation in manually triggered CI workflow (#131)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-16T05:50:28+01:00",
          "tree_id": "8b2900c86be870cfc6bc054d7fd6d0c3c3096f39",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/3ed1b94f4be8f53b39a6620735a96c738c2975c0"
        },
        "date": 1726462428496,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 60160,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 60615,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 70976,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 104128,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 104945,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 119028,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 160656,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 162152,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 180527,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "3ed1b94f4be8f53b39a6620735a96c738c2975c0",
          "message": "Fix name propagation in manually triggered CI workflow (#131)\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-16T05:50:28+01:00",
          "tree_id": "8b2900c86be870cfc6bc054d7fd6d0c3c3096f39",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/3ed1b94f4be8f53b39a6620735a96c738c2975c0"
        },
        "date": 1726462437330,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 81005,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89796,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116923,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127956,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141894,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174179,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192548,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209452,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249950,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "523d66140fd328a3eaf8272e164bfe9c9906e57b",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/523d66140fd328a3eaf8272e164bfe9c9906e57b"
        },
        "date": 1726544731036,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56314,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57445,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 67897,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98467,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99292,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113471,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152026,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153358,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171633,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "523d66140fd328a3eaf8272e164bfe9c9906e57b",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/523d66140fd328a3eaf8272e164bfe9c9906e57b"
        },
        "date": 1726544878303,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80501,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89819,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116932,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128025,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141777,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174124,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192775,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209283,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249740,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "991ff695449eb2cb0c275ff8437e86bb1916571f",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/991ff695449eb2cb0c275ff8437e86bb1916571f"
        },
        "date": 1726558314019,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56373,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57477,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 67939,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98564,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99364,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152126,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153478,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171786,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "991ff695449eb2cb0c275ff8437e86bb1916571f",
          "message": "Add first AArch64 Keccak-f1600 ASM",
          "timestamp": "2024-09-16T05:50:15Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/133/commits/991ff695449eb2cb0c275ff8437e86bb1916571f"
        },
        "date": 1726558325120,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80505,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89792,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116909,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 128005,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141746,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174118,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192746,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209296,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 249745,
            "unit": "cycles"
          }
        ]
      },
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
          "id": "861095be62d1b8db932f1c4c83bffdb28aebffd6",
          "message": "Add scalar AArch64 Keccak-f1600 ASM (#133)\n\n* Add first AArch64 Keccak-f1600 ASM\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Update scalar Keccak ASM with A55-optimized version\r\n\r\nThis should perform decent on most microarchitectures.\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n* Minor cleanup of auto-generated scalar Keccak-f1600 assembly\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-17T16:20:25+01:00",
          "tree_id": "664de110674e734f8b0a1c4efcdb11acd0b89d80",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/861095be62d1b8db932f1c4c83bffdb28aebffd6"
        },
        "date": 1726586636591,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56376,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57604,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 67834,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98588,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99648,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113497,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152143,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153435,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171762,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b699376c9a053b57207ec72fc29c77c549ba2e43",
          "message": "Update to FIPS203 (#96)\n\n* Update to FIPS203\r\n\r\nFollowing https://github.com/pq-crystals/kyber/commit/3c874cddd5fdaf4a7bd13f7e2e4d98a2a1eb8dc4\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* Update mlkem/indcpa.c\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:06+01:00",
          "tree_id": "850ec0275d88520f560cd46106d97d880cabeeb2",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/b699376c9a053b57207ec72fc29c77c549ba2e43"
        },
        "date": 1726628251978,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56495,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57530,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 67849,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98770,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99587,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113488,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152150,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153425,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171731,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "caa9a053645e8b02d24a9137d9b24c4809bdd8d7",
          "message": "Fix string vs. boolean in store_results argument to bench action\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:59+01:00",
          "tree_id": "d3adfb465eac34bd521db4004ca2a6a81667c774",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/caa9a053645e8b02d24a9137d9b24c4809bdd8d7"
        },
        "date": 1726628309231,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56477,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57511,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 67829,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98772,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99573,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113474,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152163,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153462,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171775,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b699376c9a053b57207ec72fc29c77c549ba2e43",
          "message": "Update to FIPS203 (#96)\n\n* Update to FIPS203\r\n\r\nFollowing https://github.com/pq-crystals/kyber/commit/3c874cddd5fdaf4a7bd13f7e2e4d98a2a1eb8dc4\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\n\r\n* Update mlkem/indcpa.c\r\n\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\n\r\n---------\r\n\r\nSigned-off-by: Matthias J. Kannwischer <matthias@kannwischer.eu>\r\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>\r\nCo-authored-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2024-09-18T03:54:06+01:00",
          "tree_id": "850ec0275d88520f560cd46106d97d880cabeeb2",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/commit/b699376c9a053b57207ec72fc29c77c549ba2e43"
        },
        "date": 1726628320241,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 80992,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 89803,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 116931,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 127929,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 141811,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 174109,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 192582,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 209757,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 250236,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "4262d514ad483c8e39be87455b4b4d955c703b16",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/4262d514ad483c8e39be87455b4b4d955c703b16"
        },
        "date": 1726640970145,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56358,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57514,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68057,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98571,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99391,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113695,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152175,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153500,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171787,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "00b2cfec2172c00e789cf685058b79735399c165",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/00b2cfec2172c00e789cf685058b79735399c165"
        },
        "date": 1726647594542,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56357,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57510,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68061,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98574,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99470,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113711,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152168,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153527,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171811,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "cc7e7686ded32046e8a7d6005d18cef028a0ee61",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/cc7e7686ded32046e8a7d6005d18cef028a0ee61"
        },
        "date": 1726652306103,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56359,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57520,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68056,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98576,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99459,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113724,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152150,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153504,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171783,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "00b2cfec2172c00e789cf685058b79735399c165",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/00b2cfec2172c00e789cf685058b79735399c165"
        },
        "date": 1726656065668,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56373,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57528,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68058,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98565,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99449,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113700,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152137,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153495,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171783,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "be360b371042dbbc01fd655fed02ed8a11aeb679",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/be360b371042dbbc01fd655fed02ed8a11aeb679"
        },
        "date": 1726657914825,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56362,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57512,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68055,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98572,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99465,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113737,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152177,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153517,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171805,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "c828defe7e099389bc428a5984898e828f7ae672",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/c828defe7e099389bc428a5984898e828f7ae672"
        },
        "date": 1726659439762,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56360,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57510,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68049,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98569,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99467,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113720,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152162,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153504,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171799,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "b235606ed2def0ae8a43a389d19b74cfce70325b",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/b235606ed2def0ae8a43a389d19b74cfce70325b"
        },
        "date": 1726665628144,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56379,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57520,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68051,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98575,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99443,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113687,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152143,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153492,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171794,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "17afb81634bd3991d7c05f450875e185b6e116fd",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/17afb81634bd3991d7c05f450875e185b6e116fd"
        },
        "date": 1726666526477,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56366,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57521,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68080,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99457,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113721,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152163,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153524,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171798,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "a8362423aaf292e4ca412537a793ba38b4fbd60e",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/a8362423aaf292e4ca412537a793ba38b4fbd60e"
        },
        "date": 1726666865980,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56349,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57511,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68064,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98582,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99469,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113748,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152142,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153519,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171789,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "08f9c50bd926dcf28c317c221a973fd02b4029e5",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/08f9c50bd926dcf28c317c221a973fd02b4029e5"
        },
        "date": 1726667569699,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56364,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57524,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68049,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98549,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99449,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113712,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152140,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153485,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171764,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "9fb8c22ade8309298c12e51be9e021ebaed96049",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/9fb8c22ade8309298c12e51be9e021ebaed96049"
        },
        "date": 1726667755755,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56353,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57510,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68041,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98562,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99443,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113701,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152144,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153509,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171779,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "29b727eaccaf45928f11bc2e9c0cd505ba3ef9bd",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/29b727eaccaf45928f11bc2e9c0cd505ba3ef9bd"
        },
        "date": 1726678354456,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56350,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57507,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68054,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98568,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99455,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113699,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152173,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153508,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171790,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "bdb21c1b3b8a76d934ef650daa89343253007245",
          "message": "Fix nix installer cache issue",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/138/commits/bdb21c1b3b8a76d934ef650daa89343253007245"
        },
        "date": 1726678560689,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 56362,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57529,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 68069,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 98571,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 99449,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 113709,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 152145,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 153516,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 171797,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "ef9f482bf9740c8b74365c01efb90a3b6b054ac5",
          "message": "Add batched Keccak ASM",
          "timestamp": "2024-09-18T02:55:03Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/137/commits/ef9f482bf9740c8b74365c01efb90a3b6b054ac5"
        },
        "date": 1726717802147,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 47534,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49209,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 59651,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 83314,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 84132,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 98461,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 128635,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 129813,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 148078,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "2dfa2212b326312a7412684c0650315af035522a",
          "message": "Add hybrid Neon/Neon Keccak-f1600, don't use scalar ASM on Cortex-A72",
          "timestamp": "2024-09-19T04:51:50Z",
          "url": "https://github.com/pq-code-package/mlkem-c-aarch64/pull/139/commits/2dfa2212b326312a7412684c0650315af035522a"
        },
        "date": 1726724493371,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 50740,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 52280,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 62815,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 88711,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 89403,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 103787,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 136670,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 138687,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 156345,
            "unit": "cycles"
          }
        ]
      },
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
        "date": 1726725134152,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 47624,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49239,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 59577,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 83532,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 84266,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 98361,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 128588,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 129804,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 148078,
            "unit": "cycles"
          }
        ]
      }
    ]
  }
}