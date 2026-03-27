#!/usr/bin/env bash
# Run k=15 and k=17 prove benchmarks at each commit from the benchmark base
# to HEAD, saving Criterion baselines named after each commit's short SHA.
#
# Usage: ./bench_commits.sh

set -uo pipefail

BASE="c3fc0f37"
BRANCH=$(git rev-parse HEAD)

# Check turbo boost.
NO_TURBO=$(cat /sys/devices/system/cpu/intel_pstate/no_turbo 2>/dev/null || echo "unknown")
if [ "$NO_TURBO" = "1" ]; then
    echo "WARNING: CPU turbo boost is DISABLED. Results may be slower than expected."
elif [ "$NO_TURBO" = "0" ]; then
    echo "CPU turbo boost: enabled."
else
    echo "WARNING: Could not determine turbo boost status."
fi

COMMITS=$(git rev-list --reverse "$BASE"^.."$BRANCH")
echo "Running"
echo $COMMITS

for SHA in $COMMITS; do
    SHORT=$(git rev-parse --short "$SHA")
    MSG=$(git log -1 --format='%s' "$SHA" | head -c 60)
    echo ""
    echo "=== [$SHORT] $MSG ==="

    git checkout --quiet "$SHA"

    echo "  -> k=15 (bitcoin_sig) baseline=$SHORT"
    cargo bench -p midnight-zk-stdlib --bench prove -- --save-baseline "$SHORT" 2>&1 | tail -3

    echo "  -> k=17 (cred_full) baseline=$SHORT"
    cargo bench -p midnight-zk-stdlib --bench prove_cred -- --save-baseline "$SHORT" 2>&1 | tail -3
done

git checkout --quiet "$BRANCH"
echo ""
echo "Done. Baselines saved in target/criterion/."
