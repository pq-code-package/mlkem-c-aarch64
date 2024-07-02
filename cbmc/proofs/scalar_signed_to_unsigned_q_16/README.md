# SPDX-License-Identifier: Apache-2.0

scalar_signed_to_unsigned_q_16 proof
==============

This directory contains a memory safety proof for scalar_signed_to_unsigned_q_16.

To run the proof.
-------------
* Follow these [tool installation instructions](https://github.com/awslabs/aws-templates-for-cbmc-proofs/wiki/Installation) to install cbmc and cbmc-viewer.
* Add `cbmc`, `goto-cc`, `goto-instrument`, `goto-analyzer`, and `cbmc-viewer`
  to your path.
* Run `make`.
* Open `report/html/index.html` in a web browser.
