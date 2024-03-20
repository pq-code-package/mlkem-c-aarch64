#!/bin/bash

# This script executes a binary file, captures its output, then generates and compares its SHA-256 hash with a provided one.
output=$(./$1)

output_hash=$(echo "$output" | sha256sum | awk '{ print $1 }')

if [ "$output_hash" == "$2" ]; then
    echo "Hashes match."
else
    echo "Hashes do not match."
fi