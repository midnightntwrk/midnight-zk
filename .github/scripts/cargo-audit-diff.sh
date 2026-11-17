#!/usr/bin/env bash

# This file is part of midnight-zk.
# Copyright (C) Midnight Foundation
# SPDX-License-Identifier: Apache-2.0
# Licensed under the Apache License, Version 2.0 (the "License");
# You may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# http://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# PR-level `cargo audit` that only fails on advisories the PR introduces.
#
# Advisories that also affect the base branch's Cargo.lock (typically one
# published after the base was last audited) are reported as warnings: they
# are not the PR's doing, and fixing them on the PR would invalidate its
# approvals. The Cargo Audit Fix workflow resolves them on the base branch.
#
# Findings are compared as (advisory id, crate name) pairs, so bumping an
# already-vulnerable crate to another vulnerable version does not count as new.
#
# Args: $1  path to the base branch's Cargo.lock
# Run from the repo root, so .cargo/audit.toml applies to both lockfiles.
set -euo pipefail

BASE_LOCK="${1:?usage: cargo-audit-diff.sh <base Cargo.lock>}"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# findings <lockfile> <out> [cargo audit args...]
# Writes the sorted "<advisory id> <crate>" pairs found in <lockfile> to <out>.
findings() {
  local lock="$1" out="$2"; shift 2
  local rc=0
  cargo audit --json --file "$lock" "$@" > "$out.json" || rc=$?
  # cargo audit exits non-zero both when it finds something and when it fails
  # outright (e.g. the advisory DB fetch); only the former produces a report.
  if ! jq -e '.vulnerabilities' "$out.json" > /dev/null 2>&1; then
    echo "::error::cargo audit failed on ${lock} (exit ${rc})"
    cat "$out.json"
    exit 1
  fi
  jq -r '.vulnerabilities.list[] | "\(.advisory.id) \(.package.name)"' "$out.json" | sort -u > "$out"
}

findings Cargo.lock "$tmp/head"
# Same advisory DB snapshot for both, so the comparison is consistent.
findings "$BASE_LOCK" "$tmp/base" --no-fetch

comm -12 "$tmp/head" "$tmp/base" > "$tmp/inherited"
comm -23 "$tmp/head" "$tmp/base" > "$tmp/new"

while read -r id crate; do
  echo "::warning title=${id} (${crate})::Already present on the base branch, so not blocking this PR. The Cargo Audit Fix workflow resolves it there; no change is needed here."
done < "$tmp/inherited"

if [ -s "$tmp/new" ]; then
  # Human-readable report for the log; the summary follows.
  cargo audit --no-fetch || true
  while read -r id crate; do
    echo "::error title=${id} (${crate})::Introduced by this PR. Update the crate (cargo update -p ${crate}), or, if no fix exists, add a justified ignore to .cargo/audit.toml."
  done < "$tmp/new"
  exit 1
fi

echo "No advisories introduced by this PR ($(wc -l < "$tmp/inherited") inherited from the base branch)."
