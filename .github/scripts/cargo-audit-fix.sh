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

# Resolve RustSec vulnerabilities in Cargo.lock with `cargo audit fix`.
#
# `cargo audit fix` only runs `cargo update <pkgid>` for each vulnerable crate,
# so it touches Cargo.lock alone and stays within the semver ranges the
# manifests already allow; a fix that needs a breaking bump is reported as
# remaining instead. The updated Cargo.lock is left in the working tree.
#
# Args: $1  file to write a markdown summary to (used as the PR body)
# Exit: 0 no vulnerabilities remain; 3 some remain (need manual action);
#       anything else is an error.
set -euo pipefail

SUMMARY="${1:?usage: cargo-audit-fix.sh <summary.md>}"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# audit_json <out> [cargo audit args...]
audit_json() {
  local out="$1"; shift
  local rc=0
  cargo audit --json "$@" > "$out" || rc=$?
  if ! jq -e '.vulnerabilities' "$out" > /dev/null 2>&1; then
    echo "::error::cargo audit failed (exit ${rc})"
    cat "$out"
    exit 1
  fi
}

# table <report.json>: one markdown row per finding.
table() {
  echo "| Advisory | Crate | Version | Patched | Title |"
  echo "| --- | --- | --- | --- | --- |"
  jq -r '.vulnerabilities.list[]
    | "| [\(.advisory.id)](https://rustsec.org/advisories/\(.advisory.id)) | \(.package.name) | \(.package.version) | \(.versions.patched | join(", ") | if . == "" then "none" else . end) | \(.advisory.title) |"' "$1"
}

audit_json "$tmp/before.json"
if [ "$(jq '.vulnerabilities.count' "$tmp/before.json")" -eq 0 ]; then
  echo "No vulnerabilities found."
  : > "$SUMMARY"
  exit 0
fi

# Exits non-zero when anything is left unfixed; the re-audit below is what
# decides the outcome.
cargo audit fix || true

audit_json "$tmp/after.json" --no-fetch
remaining="$(jq '.vulnerabilities.count' "$tmp/after.json")"

{
  echo "Automated \`cargo audit fix\` of advisories affecting this branch's \`Cargo.lock\`."
  echo
  echo "Only \`Cargo.lock\` changes, and only within the version ranges the manifests already allow."
  echo
  echo "### Advisories found"
  echo
  table "$tmp/before.json"
  echo
  if [ "$remaining" -gt 0 ]; then
    echo "### Not fixable automatically"
    echo
    echo "No semver-compatible patched version exists for these. Upgrade the dependency in a \`Cargo.toml\`, or add a justified ignore to \`.cargo/audit.toml\`:"
    echo
    table "$tmp/after.json"
  else
    echo "All advisories are resolved by this lockfile update."
  fi
} > "$SUMMARY"
cat "$SUMMARY"

if [ "$remaining" -gt 0 ]; then
  exit 3
fi
