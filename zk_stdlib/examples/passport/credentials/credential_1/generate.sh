#!/bin/sh
# Generate credential_1: Steins;Gate themed, CSCA key 0.
cd "$(dirname "$0")/.." && python3 generate.py \
  --surname "OKABE" --given-names "RINTARO" \
  --passport-number "12AB34567" --nationality "JPN" --issuing-country "JPN" \
  --dob "100812" --sex "M" --expiry "310101" \
  --passport-type "PP" --optional-data "EL PSY CONGROO" \
  --csca-key-index 0 \
  --output-dir ./credential_1
