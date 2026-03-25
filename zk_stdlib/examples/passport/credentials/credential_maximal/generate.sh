#!/bin/sh
# Generate credential_maximal: largest SOD that fits in SOD_M=2688
# (16 DG hashes, padded certificate DNs).
cd "$(dirname "$0")/.." && python3 generate.py \
  --surname "WOLFESCHLEGELSTEINHAUSENBERGERDORFF" --given-names "JOHANN GAMBOLPUTTY" \
  --num-dg-hashes 16 --dn-padding 3 \
  --output-dir ./credential_maximal
