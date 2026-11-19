#!/usr/bin/env bash
set -euo pipefail
source gpu-prover/bench/rc1/scripts/common.sh

mkdir -p "$bin_dir"
build=(cargo build --release --locked --offline -p midnight-gpu-prover --bin rc1-bench)
"${build[@]}" --features rc1-bench
install -m755 "$CARGO_TARGET_DIR/release/rc1-bench" "$RC1_STOCK_BIN"

# An explicit target avoids querying a device during compilation.
export MIDNIGHT_GPU_ARCHS=${MIDNIGHT_GPU_ARCHS:-120}
[[ $MIDNIGHT_GPU_ARCHS != native ]] || { echo "set an explicit SM number" >&2; exit 2; }
MIDNIGHT_GPU_REQUIRE_CUDA=1 "${build[@]}" --features rc1-bench-cuda
install -m755 "$CARGO_TARGET_DIR/release/rc1-bench" "$bin_dir/rc1-gpu"
