#!/bin/sh
# Generate credential_3: Malagasy passport with a very long name, 2 DG hashes (default).
cd "$(dirname "$0")/.." && python3 generate.py \
  --surname "GANDRIANAMPOINIMERINATOMPOLOINDRINDRA" --given-names "" \
  --passport-number "RBDL3820H" --nationality "FRA" --issuing-country "DMD" \
  --dob "450101" --sex "<" --expiry "600101" \
  --passport-type "PD" \
  --output-dir ./credential_3
