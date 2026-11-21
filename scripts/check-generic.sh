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

# Genericity check.
#
# Fails (exit 1) when a tracked file contains a private name or a
# machine-local path. Prints one "file:line: reason" row per finding.
#
# How it works
# ------------
# The banned names are not stored in clear text. The file
# scripts/generic-denylist.sha256 holds one lowercase hex SHA-256 digest per
# line (lines that start with "#" are comments). The script splits every
# tracked file name and every line of every tracked text file into tokens,
# lowercases each token and compares its SHA-256 digest with the list.
#
# Tokens are:
#   * each maximal run of [A-Za-z0-9_-] (so "a-b" is one token),
#   * each part of that run split at "-" and "_",
#   * each sequence of 2 to 4 neighbouring parts joined with "-" (so
#     "x-a_b-y" gives "a-b"),
#   * each camelCase / digit part of those parts ("FooBar" -> "foo", "bar").
# A token matches only as a whole word, so a short banned name never matches
# inside a longer, unrelated word (for example "encoding").
#
# The script also fails on these clear-text path patterns, which are never
# correct in a generic tree: "/home/", "~/", "/Users/", "/mnt/c",
# ".cache/mgpu". The Rust tool homes "~/.cargo" and "~/.rustup" are allowed
# because they are the same on every machine (upstream CI caches them).
#
# Add a token
# -----------
#   printf %s 'newtoken' | tr '[:upper:]' '[:lower:]' | sha256sum | cut -d' ' -f1 \
#     >> scripts/generic-denylist.sha256
# Use the bare word with no newline. Write a token of several words with "-"
# ("a-b"); it then also matches "a_b" and "x-a-b-y". Then run
# scripts/check-generic.test.sh and this script.
#
# Exclusions
# ----------
# Binary files (files that contain a NUL byte) are skipped. Paths listed in
# EXCLUDE_PATHS below are skipped; each entry must give its reason. The
# files in PATTERN_EXEMPT (this script, its test and scripts/README.md) skip
# only the path patterns, because they must spell them out.
#
# Usage: scripts/check-generic.sh [repo-root]
#   GENERIC_DENYLIST=<file> overrides the digest list (used by the test).
#   CHECK_GENERIC_UNTRACKED=1 also checks untracked files that git does not
#   ignore.

set -euo pipefail

root="${1:-$(git rev-parse --show-toplevel)}"
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
denylist="${GENERIC_DENYLIST:-$script_dir/generic-denylist.sha256}"

if [[ ! -f "$denylist" ]]; then
  echo "check-generic: digest list not found: $denylist" >&2
  exit 2
fi

cd "$root"

ls_flags=()
if [[ "${CHECK_GENERIC_UNTRACKED:-0}" == 1 ]]; then
  # Also check untracked, not ignored files (useful before a commit).
  ls_flags=(--cached --others --exclude-standard)
fi

git ls-files -z "${ls_flags[@]}" | python3 -I -c '
import hashlib, re, sys

denylist_path = sys.argv[1]

# Path prefixes that are skipped, with the reason for each.
EXCLUDE_PATHS = {
    # The digest list itself holds only hex digests.
    "scripts/generic-denylist.sha256": "digest list",
}

# Files that define or test the path patterns. Names are still checked.
PATTERN_EXEMPT = {
    "scripts/check-generic.sh",
    "scripts/check-generic.test.sh",
    "scripts/README.md",
}

PATH_PATTERNS = ["/home/", "~/", "/Users/", "/mnt/c", ".cache/mgpu"]
# Standard tool homes that every machine has; upstream CI caches them.
TOOL_HOME = re.compile(r"~/\.(?:cargo|rustup)\b")

digests = set()
with open(denylist_path, encoding="utf-8") as fh:
    for line in fh:
        line = line.strip().lower()
        if line and not line.startswith("#"):
            digests.add(line)

RUN = re.compile(r"[A-Za-z0-9_-]+")
SPLIT = re.compile(r"[-_]+")
CAMEL = re.compile(r"[A-Z]+(?![a-z])|[A-Z]?[a-z]+|[0-9]+")

cache = {}

def banned(tok):
    t = tok.lower()
    hit = cache.get(t)
    if hit is None:
        hit = hashlib.sha256(t.encode()).hexdigest() in digests
        cache[t] = hit
    return hit

def tokens(text):
    for run in RUN.findall(text):
        yield run
        parts = [p for p in SPLIT.split(run) if p]
        if len(parts) > 1:
            yield from parts
            # Joined neighbours ("a-b" in "x-a_b-y"), "-" as the separator,
            # up to 4 parts.
            for i in range(len(parts)):
                for j in range(i + 2, min(i + 4, len(parts)) + 1):
                    yield "-".join(parts[i:j])
        for p in parts:
            sub = CAMEL.findall(p)
            if len(sub) > 1:
                yield from sub
            # keep letter+digit words such as "ab12" whole as well
            if len(sub) > 1 and p.isalnum():
                yield p

def check_text(name, lineno, text, out):
    seen = set()
    for tok in tokens(text):
        tl = tok.lower()
        if tl not in seen and banned(tl):
            seen.add(tl)
            out.append(f"{name}:{lineno}: banned name \"{tok}\"")
    if name in PATTERN_EXEMPT:
        return
    scrubbed = TOOL_HOME.sub("", text)
    for pat in PATH_PATTERNS:
        if pat in scrubbed:
            out.append(f"{name}:{lineno}: machine-local path \"{pat}\"")

findings = []
names = sys.stdin.buffer.read().split(b"\0")
for raw in names:
    if not raw:
        continue
    name = raw.decode("utf-8", "surrogateescape")
    if any(name == p or name.startswith(p.rstrip("/") + "/") for p in EXCLUDE_PATHS):
        continue
    check_text(name, 0, name, findings)
    try:
        with open(raw, "rb") as fh:
            data = fh.read()
    except (IsADirectoryError, FileNotFoundError):
        continue  # submodule or file deleted in the work tree
    if b"\0" in data:
        continue
    text = data.decode("utf-8", "replace")
    for i, line in enumerate(text.splitlines(), 1):
        check_text(name, i, line, findings)

for f in findings:
    print(f)
if findings:
    print(f"check-generic: {len(findings)} finding(s)", file=sys.stderr)
    sys.exit(1)
print("check-generic: OK", file=sys.stderr)
' "$denylist"
