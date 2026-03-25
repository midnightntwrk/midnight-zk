#!/bin/sh
# Generate credential_minimal: smallest possible SOD (1 DG hash, short DNs).
cd "$(dirname "$0")/.." && python3 generate.py \
  --surname "A" --given-names "B" \
  --num-dg-hashes 1 --dn-padding 0 \
  --output-dir ./credential_minimal
