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

# Test for scripts/check-generic.sh.
#
# The fixtures are made at run time in a temporary git repository, with a
# temporary digest list for made-up tokens. No real banned name is written
# to the tree.

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
check="$script_dir/check-generic.sh"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# Made-up tokens: one plain word, one short word that is a substring of
# "encoding", and one hyphenated run.
printf '%s' zqxjkw | sha256sum | cut -d' ' -f1 >"$work/deny"
printf '%s' codi | sha256sum | cut -d' ' -f1 >>"$work/deny"
printf '%s' vvq-box | sha256sum | cut -d' ' -f1 >>"$work/deny"
export GENERIC_DENYLIST="$work/deny"

pass=0
fail=0

# expect <name> <expected-exit> <expected-output-regex|-> <file> <content>
# Makes a fresh repo with one tracked file and runs the check on it.
expect() {
  local name="$1" want="$2" pattern="$3" file="$4" content="$5"
  local repo="$work/repo-$pass-$fail"
  rm -rf "$repo"
  mkdir -p "$repo/$(dirname "$file")"
  git -C "$repo" init -q
  printf '%b' "$content" >"$repo/$file"
  git -C "$repo" add -- "$file"
  local out rc=0
  out="$("$check" "$repo" 2>&1)" || rc=$?
  if [[ "$rc" != "$want" ]]; then
    echo "FAIL $name: exit $rc, want $want"
    echo "$out" | sed 's/^/  /'
    fail=$((fail + 1))
    return
  fi
  if [[ "$pattern" != "-" ]] && ! grep -Eq -- "$pattern" <<<"$out"; then
    echo "FAIL $name: output does not match /$pattern/"
    echo "$out" | sed 's/^/  /'
    fail=$((fail + 1))
    return
  fi
  echo "ok   $name"
  pass=$((pass + 1))
}

expect "clean file passes" 0 "check-generic: OK" a.txt 'hello world\n'
expect "token on line 2 fails with file:line" 1 '^a\.rs:2: banned name "zqxjkw"' \
  a.rs 'fn main() {}\nlet zqxjkw = 1;\n'
expect "upper case token fails" 1 'a\.md:1: banned name "ZQXJKW"' a.md 'see ZQXJKW here\n'
expect "short token inside a word passes" 0 - a.txt 'encoding decoding\n'
expect "short token as a word fails" 1 'a\.txt:1: banned name "codi"' a.txt 'the codi box\n'
expect "token inside an identifier part fails" 1 'banned name "zqxjkw"' \
  a.rs 'let my_zqxjkw_path = 1;\n'
expect "token in camelCase fails" 1 'banned name "Zqxjkw"' a.rs 'struct ZqxjkwProver;\n'
expect "hyphenated token fails as a run" 1 'banned name "vvq-box"' a.sh 'run vvq-box now\n'
expect "hyphenated token needs both parts" 0 - a.sh 'run vvq now\n'
expect "hyphenated token inside a longer run fails" 1 'banned name "vvq-box"' \
  a.sh 'run my-vvq-box-wrapper now\n'
expect "underscore form of a hyphenated token fails" 1 'banned name "vvq-box"' \
  a.rs 'let vvq_box = 1;\n'
expect "token in a file name fails" 1 '^dir/zqxjkw\.txt:0: banned name' \
  dir/zqxjkw.txt 'nothing\n'
expect "home path fails" 1 'machine-local path "/home/"' a.txt 'cd /home/user\n'
expect "tilde path fails" 1 'machine-local path "~/"' a.txt 'cat ~/notes\n'
expect "macOS user path fails" 1 'machine-local path "/Users/"' a.txt '/Users/me\n'
expect "WSL drive path fails" 1 'machine-local path "/mnt/c"' a.txt '/mnt/c/x\n'
expect "private cache path fails" 1 'machine-local path "\.cache/mgpu"' a.txt 'x/.cache/mgpu/y\n'
expect "cargo home passes" 0 - a.yml 'path: ~/.cargo\n  ~/.cargo/registry\n  ~/.rustup\n'
expect "binary file is skipped" 0 - a.bin 'zqxjkw\0\1\2'

# An untracked file is not checked.
repo="$work/untracked"
mkdir -p "$repo"
git -C "$repo" init -q
printf 'ok\n' >"$repo/a.txt"
printf 'zqxjkw\n' >"$repo/b.txt"
git -C "$repo" add a.txt
if "$check" "$repo" >/dev/null 2>&1; then
  echo "ok   untracked file is ignored"
  pass=$((pass + 1))
else
  echo "FAIL untracked file is ignored"
  fail=$((fail + 1))
fi

# The real digest list is well formed: comments or 64 lowercase hex digits.
if grep -Evq '^(#.*|[0-9a-f]{64})$' "$script_dir/generic-denylist.sha256"; then
  echo "FAIL digest list has a malformed line"
  fail=$((fail + 1))
else
  echo "ok   digest list is well formed"
  pass=$((pass + 1))
fi

echo "check-generic.test: $pass passed, $fail failed"
[[ "$fail" == 0 ]]
