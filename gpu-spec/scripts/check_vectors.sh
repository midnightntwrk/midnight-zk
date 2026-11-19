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

# Vector gate: build the oracle, export the golden vectors into a temporary
# directory and fail when they differ from gpu-spec/vectors.
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_ABORT_ON_PANIC=1
(cd oracle && lake build --wfail >/dev/null)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
oracle/.lake/build/bin/oracle --vectors "$tmp"
cp vectors/README.md "$tmp/README.md"
# Each check is its own command, so `set -e` stops on a failure. (As the left
# side of `&&` a failing diff would be ignored and the script would exit 0.)
diff -r "$tmp" vectors
echo "vectors: up to date"
# A second export must give the same bytes (the generator is deterministic).
tmp2=$(mktemp -d)
trap 'rm -rf "$tmp" "$tmp2"' EXIT
oracle/.lake/build/bin/oracle --vectors "$tmp2"
cp vectors/README.md "$tmp2/README.md"
diff -r "$tmp" "$tmp2"
echo "vectors: regeneration is byte-stable"
python3 -I scripts/check_step_codec.py oracle/.lake/build/bin/oracle vectors >/dev/null
echo "codec checks: ok"
