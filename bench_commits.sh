#!/usr/bin/env bash
# Compile k=15 (prove) and k=17 (prove_cred) bench binaries at each commit
# in the COMMITS array into a staging directory, then run them all back-to-back
# after the CPU has reached a steady thermal state. Each run saves a Criterion
# baseline named after the commit's short SHA.
#
# Usage:
#   ./bench_commits.sh            # both phases (default)
#   ./bench_commits.sh compile    # Phase 1 only — compile + stage
#   ./bench_commits.sh run        # Phase 2 only — run staged binaries
#   ./bench_commits.sh all        # both phases (explicit)

set -uo pipefail

MODE="${1:-all}"
case "$MODE" in
    compile|run|all) ;;
    -h|--help)
        sed -n '1,12p' "$0"
        exit 0
        ;;
    *)
        echo "Unknown mode: $MODE (expected: compile | run | all)" >&2
        exit 2
        ;;
esac

BRANCH=$(git rev-parse HEAD)
REPO_ROOT=$(git rev-parse --show-toplevel)

# Phase 18 (delta-basis commit): bench the introduction of the optimization.
# Fill these SHAs in once the perf-relevant commits exist on this branch. The
# first entry must be the baseline — a commit that contains the bench
# infrastructure (this script + zk_stdlib/benches/prove*.rs + the [[bench]]
# entries in zk_stdlib/Cargo.toml) but no perf-relevant change. Each
# subsequent entry should be a successive perf-relevant commit.
COMMITS=(
 08800448 # bench infrastructure on top of main, no perf change.
 244952e7 # LagrangeDelta wired for perm_z + multiplicities.
 1c364bb8 # LagrangeDoubleDelta wired for logup_aggregator.
)

# Check turbo boost.
NO_TURBO=$(cat /sys/devices/system/cpu/intel_pstate/no_turbo 2>/dev/null || echo "unknown")
if [ "$NO_TURBO" = "1" ]; then
    echo "WARNING: CPU turbo boost is DISABLED. Results may be slower than expected."
elif [ "$NO_TURBO" = "0" ]; then
    echo "CPU turbo boost: enabled."
else
    echo "WARNING: Could not determine turbo boost status."
fi

STAGE_DIR="$HOME/Desktop/bench_binaries"
mkdir -p "$STAGE_DIR"
echo "Staging binaries in $STAGE_DIR"

# ---------------------------------------------------------------------------
# Phase 1: compile at each commit, stage binaries.
# ---------------------------------------------------------------------------

if [ "$MODE" = "compile" ] || [ "$MODE" = "all" ]; then
    extract_bench_bin() {
        # Parse `Executable benches/X.rs (target/release/deps/X-<hash>)` from
        # cargo's stderr and print the path.
        sed -nE 's|.*Executable benches/'"$1"'\.rs \(([^)]+)\).*|\1|p'
    }

    for SHA in "${COMMITS[@]}"; do
        SHORT=$(git rev-parse --short "$SHA")
        MSG=$(git log -1 --format='%s' "$SHA" | head -c 60)
        echo ""
        echo "=== Phase 1: [$SHORT] $MSG ==="

        # Skip if both staged binaries already exist.
        if [ -f "$STAGE_DIR/prove_${SHORT}" ] && [ -f "$STAGE_DIR/prove_cred_${SHORT}" ]; then
            echo "  (staged binaries present — skipping compile)"
            continue
        fi

        git -C "$REPO_ROOT" checkout --quiet "$SHA"

        for BENCH in prove prove_cred; do
            if [ -f "$STAGE_DIR/${BENCH}_${SHORT}" ]; then
                echo "  (${BENCH}_${SHORT} already staged)"
                continue
            fi
            output=$(cd "$REPO_ROOT" && cargo bench -p midnight-zk-stdlib --bench "$BENCH" --no-run 2>&1)
            bin=$(printf '%s\n' "$output" | extract_bench_bin "$BENCH")
            if [ -z "$bin" ] || [ ! -f "$REPO_ROOT/$bin" ]; then
                echo "  ERROR: could not locate compiled $BENCH binary for $SHORT"
                printf '%s\n' "$output" | tail -20
                git -C "$REPO_ROOT" checkout --quiet "$BRANCH"
                exit 1
            fi
            cp "$REPO_ROOT/$bin" "$STAGE_DIR/${BENCH}_${SHORT}"
            echo "  -> $STAGE_DIR/${BENCH}_${SHORT}"
        done
    done

    git -C "$REPO_ROOT" checkout --quiet "$BRANCH"
fi

# ---------------------------------------------------------------------------
# Phase 2: run all staged binaries back-to-back.
# ---------------------------------------------------------------------------

if [ "$MODE" = "run" ] || [ "$MODE" = "all" ]; then
    echo ""
    echo "=== Phase 2: Running benchmarks ==="

    cd "$REPO_ROOT"
    export SRS_DIR="$REPO_ROOT/zk_stdlib/examples/assets"

    # Sanity check: verify every listed commit has both binaries staged.
    missing=()
    for SHA in "${COMMITS[@]}"; do
        SHORT=$(git rev-parse --short "$SHA")
        [ -f "$STAGE_DIR/prove_${SHORT}" ]      || missing+=("prove_${SHORT}")
        [ -f "$STAGE_DIR/prove_cred_${SHORT}" ] || missing+=("prove_cred_${SHORT}")
    done
    if [ "${#missing[@]}" -gt 0 ]; then
        echo "ERROR: Phase 2 requires all binaries to be staged first." >&2
        echo "Missing:" >&2
        printf '  %s\n' "${missing[@]}" >&2
        echo "Run './bench_commits.sh compile' first." >&2
        exit 1
    fi

    for SHA in "${COMMITS[@]}"; do
        SHORT=$(git rev-parse --short "$SHA")
        echo ""
        echo "--- $SHORT (k=15) ---"
        "$STAGE_DIR/prove_${SHORT}" --bench --save-baseline "$SHORT"

        echo "--- $SHORT (k=17) ---"
        "$STAGE_DIR/prove_cred_${SHORT}" --bench --save-baseline "$SHORT"
    done

    echo ""
    echo "Done. Baselines saved in target/criterion/."
fi
