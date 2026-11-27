#!/usr/bin/env bash
# This file is part of MIDNIGHT-ZK.
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

# Interleaved A/B measurement of the prover between two checkouts of the
# repository, typically two git worktrees: the merge base and the head of a
# pull request. Run with --help for the usage.

set -euo pipefail

usage() {
    cat <<'EOF'
Usage: ab.sh <base-dir> <head-dir> [--rounds N] [--out DIR] [--dry-run]
             [-- <runner args...>]

Builds midnight-benchmarks in both checkouts, then measures them alternately
for N rounds, merges the samples of each side and compares them.

Arguments:
  <base-dir>     checkout of the reference commit
  <head-dir>     checkout of the commit under test
  --rounds N     number of rounds, each measuring both sides (default 4)
  --out DIR      where the result files go (default ./ab-results/<timestamp>)
  --dry-run      print the commands without running them
  -- ARGS...     passed to `midnight-benchmarks run` on both sides

Environment:
  SRS_DIR        directory of the SRS files, read by both sides (default
                 <head-dir>/zk_stdlib/examples/assets, or that of <base-dir>
                 if only the base checkout has the files)
  AB_BUILD_ARGS  extra arguments of `cargo build`, split on whitespace,
                 for example "--locked"

Output in DIR:
  base-<round>.json, head-<round>.json   the samples of each round
  base.json, head.json                   all rounds of a side (needs jq)
  comparison.md                          their comparison as markdown, for a
                                         pull request (comparison-<round>.md
                                         per round without jq)
EOF
}

die() {
    echo "ab.sh: error: $*" >&2
    exit 2
}

warn() {
    echo "ab.sh: warning: $*" >&2
}

rounds=4
out=""
dry_run=0
positional=()
runner_args=()
while [ $# -gt 0 ]; do
    case "$1" in
        --rounds)
            [ $# -ge 2 ] || die "--rounds needs a value"
            rounds=$2
            shift 2
            ;;
        --out)
            [ $# -ge 2 ] || die "--out needs a value"
            out=$2
            shift 2
            ;;
        --dry-run)
            dry_run=1
            shift
            ;;
        -h | --help)
            usage
            exit 0
            ;;
        --)
            shift
            runner_args=("$@")
            break
            ;;
        -*)
            die "unknown option '$1' (runner arguments go after --)"
            ;;
        *)
            positional+=("$1")
            shift
            ;;
    esac
done

if [ "${#positional[@]}" -ne 2 ]; then
    usage >&2
    die "expected <base-dir> and <head-dir>"
fi
case "$rounds" in
    '' | *[!0-9]*) die "--rounds must be a positive integer, got '$rounds'" ;;
esac
rounds=$((10#$rounds))
[ "$rounds" -ge 1 ] || die "--rounds must be a positive integer, got '$rounds'"

# Resolves symbolic links, so that two spellings of one checkout are caught.
resolve_dir() {
    [ -d "$1" ] || die "'$1' is not a directory"
    (cd "$1" && pwd -P)
}

base_dir=$(resolve_dir "${positional[0]}")
head_dir=$(resolve_dir "${positional[1]}")
[ "$base_dir" != "$head_dir" ] || die "base and head are the same directory: $base_dir"
for dir in "$base_dir" "$head_dir"; do
    [ -f "$dir/benchmarks/Cargo.toml" ] || die "$dir has no benchmarks crate"
done

if [ -z "$out" ]; then
    out="ab-results/$(date +%Y%m%d-%H%M%S)"
fi
case "$out" in
    /*) ;;
    *) out="$PWD/$out" ;;
esac

commit_of() {
    local hash
    hash=$(git -C "$1" rev-parse HEAD 2>/dev/null) || {
        echo "unknown"
        return
    }
    if [ -n "$(git -C "$1" status --porcelain --untracked-files=no 2>/dev/null)" ]; then
        hash="$hash-dirty"
    fi
    echo "$hash"
}

base_commit=$(commit_of "$base_dir")
head_commit=$(commit_of "$head_dir")
echo "base: $base_commit  $base_dir"
echo "head: $head_commit  $head_dir"
if [ "$base_commit" = "$head_commit" ] && [ "$base_commit" != "unknown" ]; then
    warn "both checkouts are at the same commit"
fi

# Worktrees do not contain the SRS files, which are ignored by git, so both
# sides read them from one directory.
has_srs() {
    compgen -G "$1/bls_filecoin_2p*" >/dev/null
}

srs_default="$head_dir/zk_stdlib/examples/assets"
if [ -z "${SRS_DIR:-}" ]; then
    for dir in "$base_dir" "$head_dir"; do
        if ! has_srs "$dir/zk_stdlib/examples/assets"; then
            warn "no SRS files in $dir/zk_stdlib/examples/assets"
        fi
    done
    if ! has_srs "$srs_default" && has_srs "$base_dir/zk_stdlib/examples/assets"; then
        srs_default="$base_dir/zk_stdlib/examples/assets"
        warn "using the SRS files of the base checkout for both sides"
    fi
fi
export SRS_DIR="${SRS_DIR:-$srs_default}"
echo "SRS_DIR: $SRS_DIR"
if ! has_srs "$SRS_DIR"; then
    warn "no bls_filecoin_2p* file in SRS_DIR; the runs will fail to load the SRS." \
        "Set SRS_DIR to a directory that has them (see zk_stdlib/README.md)"
fi

build_args=()
if [ -n "${AB_BUILD_ARGS:-}" ]; then
    read -r -a build_args <<<"$AB_BUILD_ARGS"
fi

print_command() {
    printf '+'
    printf ' %q' "$@"
}

run() {
    print_command "$@"
    printf '\n'
    if [ "$dry_run" -eq 0 ]; then
        "$@"
    fi
}

# Like `run`, with the standard output written to the file given first.
run_to() {
    local file=$1
    shift
    print_command "$@"
    printf ' > %q\n' "$file"
    if [ "$dry_run" -eq 0 ]; then
        "$@" >"$file"
    fi
}

# Runs from inside the checkout, so that cargo picks up its toolchain file and
# its configuration.
run_in() {
    local dir=$1
    shift
    local command
    command=$(print_command "$@")
    printf '+ (cd %q &&%s)\n' "$dir" "${command#+}"
    if [ "$dry_run" -eq 0 ]; then
        (cd "$dir" && "$@")
    fi
}

binary_of() {
    echo "$1/target/release/midnight-benchmarks"
}

echo
echo "== Building both sides =="
for dir in "$base_dir" "$head_dir"; do
    # A shared target directory would make each build overwrite the other.
    run_in "$dir" env -u CARGO_TARGET_DIR \
        cargo build --release -p midnight-benchmarks ${build_args[@]+"${build_args[@]}"}
    if [ "$dry_run" -eq 0 ] && [ ! -x "$(binary_of "$dir")" ]; then
        die "the build did not produce $(binary_of "$dir")"
    fi
done

run mkdir -p "$out"

measure() {
    local side=$1 dir=$2 round=$3
    run "$(binary_of "$dir")" run --json "$out/$side-$round.json" \
        ${runner_args[@]+"${runner_args[@]}"}
}

for round in $(seq 1 "$rounds"); do
    echo
    echo "== Round $round of $rounds =="
    # The side that goes first alternates, which cancels a drift of the
    # machine over the session instead of attributing it to one side.
    if [ $((round % 2)) -eq 1 ]; then
        measure base "$base_dir" "$round"
        measure head "$head_dir" "$round"
    else
        measure head "$head_dir" "$round"
        measure base "$base_dir" "$round"
    fi
done

# Keeps the first round's metadata and case order and appends the samples of
# the later rounds.
merge_filter='
. as $rounds
| $rounds[0]
| .cases = (
    reduce ($rounds[] | .cases[]) as $c ([];
      (map(.workload == $c.workload and .pcs == $c.pcs and .threads == $c.threads)
       | index(true)) as $i
      | if $i == null then . + [$c]
        else .[$i].samples_ns += $c.samples_ns
        end))'

merge() {
    local side=$1 files=() round
    for round in $(seq 1 "$rounds"); do
        files+=("$out/$side-$round.json")
    done
    # shellcheck disable=SC2016
    printf '+ jq -s "$merge_filter"'
    printf ' %q' "${files[@]}"
    printf ' > %q\n' "$out/$side.json"
    if [ "$dry_run" -eq 0 ]; then
        jq -s "$merge_filter" "${files[@]}" >"$out/$side.json.tmp"
        mv "$out/$side.json.tmp" "$out/$side.json"
    fi
}

compare_bin=$(binary_of "$head_dir")
echo
if command -v jq >/dev/null 2>&1; then
    echo "== Merging the rounds with jq and comparing =="
    merge base
    merge head
    run "$compare_bin" compare "$out/base.json" "$out/head.json"
    run_to "$out/comparison.md" "$compare_bin" compare --markdown "$out/base.json" "$out/head.json"
else
    echo "== jq not found: the rounds are not merged, comparing round by round =="
    for round in $(seq 1 "$rounds"); do
        echo
        echo "-- Round $round --"
        run "$compare_bin" compare "$out/base-$round.json" "$out/head-$round.json"
        run_to "$out/comparison-$round.md" "$compare_bin" compare --markdown \
            "$out/base-$round.json" "$out/head-$round.json"
    done
fi

echo
echo "Results are in $out"
