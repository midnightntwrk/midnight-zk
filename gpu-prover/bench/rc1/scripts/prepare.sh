#!/usr/bin/env bash
set -euo pipefail
source gpu-prover/bench/rc1/scripts/common.sh
export RC1_K=21
exec "$RC1_STOCK_BIN" prepare
