#!/usr/bin/env bash
set -euo pipefail
source gpu-prover/bench/rc1/scripts/common.sh

# The stock executable verifies the proofs and prepares the key cache (see build.sh);
# the Metal executable proves. No toolkit setting is needed: `xcrun metal` builds the
# shaders, or the embedded source is compiled at first use.
mkdir -p "$bin_dir"
build=(cargo build --release --locked --offline -p midnight-gpu-prover --bin rc1-bench)
"${build[@]}" --features rc1-bench
install -m755 "$CARGO_TARGET_DIR/release/rc1-bench" "$RC1_STOCK_BIN"
"${build[@]}" --features rc1-bench-metal
install -m755 "$CARGO_TARGET_DIR/release/rc1-bench" "$bin_dir/rc1-metal"
