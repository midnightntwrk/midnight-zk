#!/usr/bin/env bash
set -euo pipefail
exec bash gpu-prover/bench/rc1/scripts/run-set.sh cpu "$@"
