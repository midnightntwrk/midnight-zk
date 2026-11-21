#!/usr/bin/env bash
# This file is part of MIDNIGHT-ZK.
# Copyright (C) Midnight Foundation
# SPDX-License-Identifier: Apache-2.0
# Licensed under the Apache License, Version 2.0 (the "License");
# You may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Runs the timed proofs until every job has all its repetitions, and yields the machine to
# other users between proofs.
#
# Usage: scripts/run-bench.sh BINARY JOBS PARAMS_DIR RAW_TSV [compact-bench prove options]
#
# Before each start of compact-bench, the script waits until the 1-minute load is below
# BENCH_MAX_LOAD; this wait is outside any lock. compact-bench then does not wait: it stops
# with exit 75 when the machine is busy at start, after a proof during which other processes
# used more than BENCH_YIELD_FOREIGN cores, or before a proof when another process holds
# BENCH_LOCK. On exit 75 the script waits again and resumes; finished rows are skipped.
#
# Environment:
#   BENCH_LOCK      lock file shared with other GPU or benchmark jobs (default: none).
#                   compact-bench takes it before each proof and releases it after.
#   BENCH_MAX_LOAD  1-minute load gate (default 2).
#   BENCH_YIELD_FOREIGN  CPU cores of other processes that end a run (default 2).
#   BENCH_SPLIT     number of repetitions (warm-up + timed, default: unset). When set, each
#                   repetition runs in its own process (`--rep R`), so that other jobs on a
#                   shared machine can run between repetitions.
#   RAYON_NUM_THREADS  prover threads; set it, so that the thread count is fixed and recorded.
set -euo pipefail
bin="${1:?binary}" jobs="${2:?jobs}" params="${3:?params dir}" raw="${4:?raw tsv}"
shift 4
max_load="${BENCH_MAX_LOAD:-2}"
lock_args=()
if [[ -n "${BENCH_LOCK:-}" ]]; then lock_args=(--lock "$BENCH_LOCK"); fi

gate() {
  until awk -v m="$max_load" '{ exit !($1 < m) }' /proc/loadavg; do sleep 30; done
  if [[ -n "${BENCH_LOCK:-}" ]]; then
    until flock -n "$BENCH_LOCK" true; do sleep 60; done
  fi
}

run() {
  while true; do
    gate
    set +e
    "$bin" prove --jobs "$jobs" --params "$params" --raw "$raw" \
      --max-load "$max_load" --yield-foreign "${BENCH_YIELD_FOREIGN:-2}" \
      "${lock_args[@]}" "$@"
    local code=$?
    set -e
    case "$code" in
      0) return 0 ;;
      75) echo "$(date -Is) machine or lock busy: waiting" ;;
      *) echo "compact-bench exited with $code" >&2; exit "$code" ;;
    esac
  done
}

if [[ -n "${BENCH_SPLIT:-}" ]]; then
  for ((r = 0; r < BENCH_SPLIT; r++)); do run "$@" --rep "$r"; done
else
  run "$@"
fi
echo "all jobs done"
