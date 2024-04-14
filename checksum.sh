#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
set -o xtrace

# This script executes a binary file, captures its output, then generates and compares its SHA-256 hash with a provided one.

output_hash=$(./$1 | sha256sum | awk '{ print $4 }')

if [[ ${output_hash} == "${2}" ]]; then
	echo "${1} Hashes match."
	exit 0
else
	echo "${1} Hashes do not match: ${output_hash} vs ${2}"
	exit 1
fi
