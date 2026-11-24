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
#
# Fetches the benchmark programs listed in suite.json (each file pinned by repository,
# commit and sha256), applies the recorded patches, fetches compactc 0.36.0 and builds every
# program: ZKIR, prover keys and verifier keys.
#
# Usage: ./fetch-suite.sh [program-id ...]
#
# Environment:
#   WORK       output directory (default: ./work). Writes $WORK/programs/<id>/,
#              $WORK/build/<id>/ and $WORK/compactc/.
#   COMPACTC   use this compactc 0.36.0 binary instead of fetching the release.
#   SKIP_ZK=1  pass --skip-zk to compactc: ZKIR only, no keys (fast check of the sources).
#
# Needs: bash 4 or newer, curl, unzip, python3, sha256sum (or shasum), patch.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORK="${WORK:-$HERE/work}"
SUITE="$HERE/suite.json"
COMPACTC_VERSION="0.36.0"
RELEASE="https://github.com/LFDT-Minokawa/compact/releases/download/compactc-v$COMPACTC_VERSION"

sha256() {
  if command -v sha256sum >/dev/null; then sha256sum "$1" | cut -d' ' -f1; else shasum -a 256 "$1" | cut -d' ' -f1; fi
}

# sha256 of the public compactc 0.36.0 release archives.
compactc_asset() {
  case "$(uname -s)-$(uname -m)" in
    Linux-x86_64) echo "x86_64-unknown-linux-musl 7017b6121ebb9d53a562984bca616d143ef84fc7ee18b4da6c3a0a6615cb5e97" ;;
    Linux-aarch64) echo "aarch64-unknown-linux-musl 87740ca24c7f99fc2200fd398c57ddfaa55eb60f6bdcf971869b0b543a7722ad" ;;
    Darwin-x86_64) echo "x86_64-darwin 2c671aed1d65b27945f3f32bad109971ce1f26f50ee238538d269050e4043bff" ;;
    Darwin-arm64) echo "aarch64-darwin a8126b2cc06230ed2c6558059a8945119e370ff222930e6a52f90870e8cc3c5d" ;;
    *) echo "unsupported platform $(uname -s)-$(uname -m)" >&2; exit 1 ;;
  esac
}

fetch_compactc() {
  if [[ -n "${COMPACTC:-}" ]]; then
    echo "$COMPACTC"
    return
  fi
  local dir="$WORK/compactc" asset want zip
  read -r asset want < <(compactc_asset)
  zip="$dir/compactc_v${COMPACTC_VERSION}_$asset.zip"
  if [[ ! -x "$dir/compactc" ]]; then
    mkdir -p "$dir"
    curl -fsSL -o "$zip" "$RELEASE/compactc_v${COMPACTC_VERSION}_$asset.zip"
    [[ "$(sha256 "$zip")" == "$want" ]] || { echo "compactc archive sha256 mismatch" >&2; exit 1; }
    unzip -oq "$zip" -d "$dir"
  fi
  echo "$dir/compactc"
}

# One line per file: id repo commit main source_path path sha256 patch patched_sha256
list_files() {
  python3 -I - "$SUITE" "$@" <<'EOF'
import json, sys
suite = json.load(open(sys.argv[1]))
want = set(sys.argv[2:])
for p in suite["programs"]:
    if want and p["id"] not in want:
        continue
    for f in p["files"]:
        print(p["id"], p["repo"], p["commit"], p["main"], f["source_path"], f["path"], f["sha256"],
              f.get("patch", "-"), f.get("patched_sha256", "-"))
EOF
}

mkdir -p "$WORK/programs" "$WORK/build"
COMPACTC_BIN="$(fetch_compactc)"
version="$("$COMPACTC_BIN" --version)"
[[ "$version" == "$COMPACTC_VERSION"* ]] || { echo "compactc is $version, need $COMPACTC_VERSION" >&2; exit 1; }

declare -A MAIN=()
while read -r id repo commit main src path want patch patched; do
  dest="$WORK/programs/$id/$path"
  mkdir -p "$(dirname "$dest")"
  curl -fsSL -o "$dest" "https://raw.githubusercontent.com/$repo/$commit/$src"
  [[ "$(sha256 "$dest")" == "$want" ]] || { echo "$id/$path: sha256 mismatch against suite.json" >&2; exit 1; }
  if [[ "$patch" != "-" ]]; then
    patch -s -d "$WORK/programs/$id" -p1 < "$HERE/$patch"
    [[ "$(sha256 "$dest")" == "$patched" ]] || { echo "$id/$path: patched sha256 mismatch" >&2; exit 1; }
  fi
  MAIN[$id]="$main"
done < <(list_files "$@")

skip=()
[[ "${SKIP_ZK:-0}" == 1 ]] && skip=(--skip-zk)
for id in $(printf '%s\n' "${!MAIN[@]}" | sort); do
  start=$(date +%s)
  # compactc runs in the program directory, so that `import "Inner"` and module paths resolve.
  (cd "$WORK/programs/$id" && "$COMPACTC_BIN" "${skip[@]}" "${MAIN[$id]}" "$WORK/build/$id" >/dev/null)
  echo "$id: built in $(( $(date +%s) - start )) s"
done
echo "compactc $version; ${#MAIN[@]} programs in $WORK/build"
