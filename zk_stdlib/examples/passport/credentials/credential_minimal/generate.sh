#!/bin/sh
# Generate credential_minimal: smallest possible SOD, CSCA key 3.
cd "$(dirname "$0")/.." && python3 generate.py \
  --surname "A" --given-names "B" \
  --num-dg-hashes 1 --dn-padding 0 \
  --csca-key-index 3 \
  --output-dir ./credential_minimal
