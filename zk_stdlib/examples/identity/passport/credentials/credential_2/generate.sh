#!/bin/sh
# Generate credential_2: Spanish passport, CSCA key 1.
cd "$(dirname "$0")/.." && python3 generate.py \
  --surname "DE LA CRUZ" --given-names "MARIA" \
  --passport-number "UH87G9901" --nationality "ESP" --issuing-country "ESP" \
  --dob "911214" --sex "F" --expiry "310101" \
  --passport-type "PE" --optional-data "XXV789" \
  --csca-key-index 1 \
  --output-dir ./credential_2
