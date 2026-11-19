#!/usr/bin/env bash
set -euo pipefail

# All entry points run from the workspace root.
[[ -f gpu-prover/bench/rc1/main.rs ]] || { echo "run from the repository root" >&2; exit 2; }
export RC1_WORK_DIR=${RC1_WORK_DIR:-"$PWD/../rc1-results"}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-"$RC1_WORK_DIR/target"}
export CARGO_BUILD_JOBS=8
export RC1_CACHE=${RC1_CACHE:-"$RC1_WORK_DIR/key-cache"}
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8}
bin_dir="$RC1_WORK_DIR/bin"
out_dir="$RC1_WORK_DIR/box-out"
export RC1_STOCK_BIN="$bin_dir/rc1-cpu"
