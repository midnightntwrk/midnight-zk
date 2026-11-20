#!/usr/bin/env bash
set -euo pipefail
# Include the load gate, key loading, verification and publication in the lease.
# macOS has no `timeout`: use GNU coreutils' `gtimeout`, else no limit.
limit=(timeout --kill-after=3s 690s)
if ! command -v timeout >/dev/null; then
    limit=()
    ! command -v gtimeout >/dev/null || limit=(gtimeout --kill-after=3s 690s)
fi
exec "${limit[@]}" bash gpu-prover/bench/rc1/scripts/run-set.sh metal "$@"
