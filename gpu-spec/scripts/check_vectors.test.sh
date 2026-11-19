#!/usr/bin/env bash
# This file is part of MIDNIGHT-ZK.
# Copyright (C) Midnight Foundation
# SPDX-License-Identifier: Apache-2.0
# Licensed under the Apache License, Version 2.0 (the "License");
# You may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


# Negative test of the vector gate: check_vectors.sh must fail on a stale
# file, on a hand-edited value, on a deleted file and on an extra file, and
# pass on the untouched tree. Works on a copy; the tree is not changed.
set -euo pipefail
cd "$(dirname "$0")/.."
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
(cd oracle && lake build --wfail >/dev/null)

fresh() {  # a copy of gpu-spec that shares the built oracle
  local d="$work/$1"
  mkdir -p "$d"
  cp -r scripts vectors "$d/"
  mkdir -p "$d/oracle"
  for f in oracle/*; do ln -s "$PWD/$f" "$d/oracle/"; done
  ln -s "$PWD/oracle/.lake" "$d/oracle/.lake"
  echo "$d"
}
expect_fail() {
  if "$1/scripts/check_vectors.sh" >/dev/null 2>&1; then
    echo "check_vectors.test: FAILED: the gate passed with $2"; exit 1
  fi
  echo "check_vectors.test: the gate fails with $2 (expected)"
}

d=$(fresh clean)
"$d/scripts/check_vectors.sh" >/dev/null
echo "check_vectors.test: the gate passes on the untouched vectors"

d=$(fresh edited)   # one digit of one expected value changed by hand
python3 -I - "$d/vectors/ntt.json" <<'PY'
import pathlib, re, sys
p = pathlib.Path(sys.argv[1]); t = p.read_text()
m = re.search(r'"ntt": \[\s*"(\d)', t)
i = m.start(1); t = t[:i] + ("1" if t[i] != "1" else "2") + t[i + 1:]
p.write_text(t)
PY
expect_fail "$d" "a hand-edited value in ntt.json"

d=$(fresh stale)    # a service trace from an older oracle: one state field changed
sed -i '0,/"served": 0/s//"served": 7/' "$d/vectors/service/ladder-gpu.json"
expect_fail "$d" "a stale service trace"

d=$(fresh missing)
rm "$d/vectors/msm.json"
expect_fail "$d" "a missing vector file"

d=$(fresh extra)
echo '{}' > "$d/vectors/handmade.json"
expect_fail "$d" "a vector file that the oracle does not write"
