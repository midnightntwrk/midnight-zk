#!/usr/bin/env bash
set -euo pipefail
# Include the load gate, key loading, verification and publication in the lease.
exec timeout --kill-after=3s 690s bash gpu-prover/bench/rc1/scripts/run-set.sh gpu "$@"
