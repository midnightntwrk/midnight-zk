#!/bin/sh
# Generate credential_3: Malagasy passport with a very long name, CSCA key 2.
cd "$(dirname "$0")/.." && python3 generate.py \
  --surname "GANDRIANAMPOINIMERINATOMPOLOINDRINDRA" --given-names "" \
  --passport-number "RBDL3820H" --nationality "FRA" --issuing-country "DMD" \
  --dob "450101" --sex "<" --expiry "600101" \
  --passport-type "PD" \
  --csca-key-index 2 \
  --output-dir ./credential_3
