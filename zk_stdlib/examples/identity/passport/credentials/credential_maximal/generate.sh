#!/bin/sh
# Generate credential_maximal: largest SOD that fits in SOD_M, CSCA key 4.
cd "$(dirname "$0")/.." && python3 generate.py \
  --surname "WOLFESCHLEGELSTEINHAUSENBERGERDORFF" --given-names "JOHANN GAMBOLPUTTY" \
  --num-dg-hashes 16 --dn-padding 3 \
  --csca-key-index 4 \
  --output-dir ./credential_maximal
