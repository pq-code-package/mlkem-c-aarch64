window.BENCHMARK_DATA = {
  "lastUpdate": 1719406260044,
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
      }
    ]
  }
}