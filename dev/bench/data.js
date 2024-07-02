window.BENCHMARK_DATA = {
  "lastUpdate": 1719945615043,
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
      }
    ]
  }
}