#!/usr/bin/env bash
set -euo pipefail
source gpu-prover/bench/rc1/scripts/common.sh

[[ $# == 2 && $1 =~ ^(cpu|gpu)$ && $2 =~ ^[123]$ ]] || { echo "usage: run-{cpu,gpu}.sh REP (1, 2, or 3)" >&2; exit 2; }
mode=$1
export RC1_REP=$2 RC1_K=21 RC1_WARM=${RC1_WARM:-1}
mkdir -p "$out_dir"
# Serialize both modes. Publish only complete, unique sets using a same-directory rename.
exec 9>"$out_dir/.rc1-set.lock"
flock -n 9 || { echo "another set is running" >&2; exit 1; }
raw="$out_dir/raw-$mode.tsv"
if [[ -s $raw ]] && awk -F '\t' -v rep="$RC1_REP" 'NR > 1 && $2 == rep {found=1} END {exit !found}' "$raw"; then
    echo "already recorded $mode repeat $RC1_REP" >&2
    exit 1
fi
tmp=$(mktemp -d "$out_dir/.set.XXXXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
"$bin_dir/rc1-$mode" run > "$tmp/set"
if [[ -s $raw ]]; then
    cmp <(head -n1 "$raw") <(head -n1 "$tmp/set")
    { cat "$raw"; tail -n +2 "$tmp/set"; } > "$tmp/merged"
else
    cp "$tmp/set" "$tmp/merged"
fi
mv -f "$tmp/merged" "$raw"
