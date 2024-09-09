window.BENCHMARK_DATA = {
  "lastUpdate": 1725865414644,
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
            "name": "MLKEM512 keypair",
            "value": 139737,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 173440,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 223995,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 240688,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 284687,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 351714,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 378520,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 430122,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 139839,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 173467,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 224224,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 240948,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 285582,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 352382,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 378944,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 429900,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 139915,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 173680,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 224975,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 240880,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 285430,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 351945,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 377966,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 429291,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 139886,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 173481,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 224078,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 240657,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 284898,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 351440,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 378984,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 429791,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 139832,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 173610,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 224400,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 240903,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 285424,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 351957,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 378461,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 429532,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 149852,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 176107,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 226776,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 255603,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 287623,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 354589,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 398973,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 433080,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 149776,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 176138,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 226913,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 255578,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 288305,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 355219,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 398096,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 431517,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 150101,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 175718,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 226211,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 258716,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 288241,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 354840,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 396398,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 429277,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 150230,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 175756,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 226412,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 259071,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 288597,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 356202,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 397000,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 432161,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 150407,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 175918,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 226465,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 259388,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 289112,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 355689,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 0,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 0,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 150228,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 175632,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 226255,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 258722,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 288887,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 355243,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 395725,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 429493,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 150522,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 176088,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 226842,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 258759,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 288144,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 355911,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 397968,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 433383,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 150840,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 176811,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 227668,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 260115,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 290365,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 357533,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 398566,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 432980,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 151081,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 176875,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 227702,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 260160,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 289728,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 357066,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 399334,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 433846,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 150893,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 176973,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 227730,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 260992,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 290944,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 358150,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 399436,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 433645,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 150815,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 176282,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 227272,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 260188,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 289840,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 356795,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 399279,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 432938,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 151103,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 176557,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 227203,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 259800,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 289597,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 356890,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 399613,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 432509,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 150883,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 176290,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 227130,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 261718,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 291721,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 358658,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 398859,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 432881,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 151170,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 176804,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 227770,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 261260,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 290632,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 357753,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 399219,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 433029,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
            "value": 517773,
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
            "name": "MLKEM512 keypair",
            "value": 277828,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 366730,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 493524,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 475274,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 588825,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 755774,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 737681,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 870690,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 296007,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 369669,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 496425,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 502643,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 591725,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 758702,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 773765,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 873690,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 295941,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 369599,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 496383,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 502648,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 591741,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 758637,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 773910,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 873782,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297654,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368849,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495721,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510738,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 596249,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 763549,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771226,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 871364,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297689,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368839,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495698,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510702,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 596238,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 763525,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771276,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 871212,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297671,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368799,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495633,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510681,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 596082,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 763122,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771353,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 871145,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297667,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368846,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495724,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510714,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 596150,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 763296,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771263,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 871029,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297629,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368825,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495646,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510649,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 596072,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 763235,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771184,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 871126,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297682,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368827,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495748,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510680,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 596102,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 763225,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771118,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 871075,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297672,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368820,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495708,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510691,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 596116,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 763366,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771158,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 871081,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297656,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368814,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495660,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510623,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 596033,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 763162,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771113,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 870908,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297640,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368562,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495391,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510698,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 595805,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 762904,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771222,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 870837,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297707,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368579,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495457,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510734,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 595970,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 763078,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771161,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 870865,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297817,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368581,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495486,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510707,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 595892,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 762966,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771377,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 870845,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 297741,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 368541,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 495412,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 510819,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 595928,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 762984,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 771295,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 870773,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
            "value": 1078141,
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
            "name": "MLKEM512 keypair",
            "value": 117802,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138685,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178585,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 197305,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 222097,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 274374,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305313,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330894,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 123401,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 140697,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 183055,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200762,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 224161,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276268,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 306095,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 331024,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 123429,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 140757,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 183174,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200806,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 224259,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276362,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 306033,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 331041,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 123420,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 140747,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 183113,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200744,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 224285,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276376,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 306209,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 331135,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 123412,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 140721,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 183097,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200750,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 224173,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276299,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305952,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330958,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 123418,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 140718,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 183099,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200724,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 224130,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276202,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305842,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330897,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 123442,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 140757,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 183131,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200759,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 224225,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276334,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 306057,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330954,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 123423,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 140798,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 183180,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200799,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 224205,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276322,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305949,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330943,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 123427,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 140740,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 183120,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200754,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 224174,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276250,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 306039,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330959,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 123391,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 140620,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 183015,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200716,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223948,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276074,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 306038,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 331366,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 123377,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 140683,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 182880,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200966,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223857,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276229,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 306177,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 331524,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118629,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138360,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178228,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200511,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223382,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275998,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 306054,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330715,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118644,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138473,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178331,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200592,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223410,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276003,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305935,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330745,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118660,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138447,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178313,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200635,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223484,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 276128,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 306012,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330711,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
            "value": 396155,
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
            "name": "MLKEM512 keypair",
            "value": 118579,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138922,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178852,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200425,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223240,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275527,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305157,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330628,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118564,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138897,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178826,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200438,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223315,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275579,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 304903,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 329714,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118518,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138843,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178774,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200194,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223142,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275432,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 304547,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 329613,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118597,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138961,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178875,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200033,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223037,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275399,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305103,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330027,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118581,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138866,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178797,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200485,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223258,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275530,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305153,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330119,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118566,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138903,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178826,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200316,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223130,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275397,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305022,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 329877,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118538,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138887,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178805,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200509,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223280,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275515,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 304930,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 329692,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118591,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138965,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178889,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200571,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223304,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275563,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 304818,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 329690,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118630,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138923,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178855,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200511,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223396,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275669,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305164,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 329939,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118584,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138985,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178823,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200464,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223387,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275928,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305185,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330029,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118544,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138910,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178828,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200406,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223260,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275490,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305218,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330154,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 119064,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138837,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178735,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200634,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223299,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275724,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 304864,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330161,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118548,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138909,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178854,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200505,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223241,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275476,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 305145,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 329969,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 119100,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138907,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178791,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200738,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223401,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275813,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 304821,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330146,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118493,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138954,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 179523,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200552,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223502,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275887,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 304862,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 330187,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 118491,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 138763,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 178603,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 200817,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 223331,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 275801,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 304259,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 329259,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
            "value": 394264,
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
            "name": "MLKEM512 keypair",
            "value": 75554,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 87404,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 111926,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 127956,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 141864,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 174147,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 192438,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 209207,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 75541,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 87427,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 111945,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 127965,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 141875,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 174154,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 192427,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 209187,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 75553,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 87428,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 111950,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 127984,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 141915,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 174165,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 192450,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 209178,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 75561,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 87402,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 111911,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 127969,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 141886,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 174182,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 192429,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 209157,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 75556,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 87406,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 111926,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 127965,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 141868,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 174141,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 192435,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 209186,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 75590,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 87570,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 111881,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 127878,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 142131,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 174421,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 192244,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 209146,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 82364,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 89854,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 117614,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 128051,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 141768,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 174107,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 192264,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 209169,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 75552,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 87399,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 111943,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 127956,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 141882,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 174154,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 192455,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 209181,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 75553,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 87400,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 111909,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 127944,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 141890,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 174134,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 192486,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 209182,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
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
            "name": "MLKEM512 keypair",
            "value": 82353,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 encaps",
            "value": 89826,
            "unit": "cycles"
          },
          {
            "name": "MLKEM512 decaps",
            "value": 117595,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 keypair",
            "value": 128055,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 encaps",
            "value": 141773,
            "unit": "cycles"
          },
          {
            "name": "MLKEM768 decaps",
            "value": 174114,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 keypair",
            "value": 192285,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 encaps",
            "value": 209178,
            "unit": "cycles"
          },
          {
            "name": "MLKEM1024 decaps",
            "value": 249719,
            "unit": "cycles"
          }
        ]
      }
    ]
  }
}