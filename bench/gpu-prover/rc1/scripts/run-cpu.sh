#!/usr/bin/env bash
set -euo pipefail
exec bash bench/gpu-prover/rc1/scripts/run-set.sh cpu "$@"
