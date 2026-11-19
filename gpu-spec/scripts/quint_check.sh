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

# Quint gate of gpu-spec: typecheck, simulate every instance against `inv`,
# export ITF traces, replay them through the Lean oracle's --step mode, and
# check that the replay can fail (negative control).
#
# Usage: scripts/quint_check.sh [SAMPLES] [TRACES]   (defaults 10000 and 50)
# Needs: quint (0.32.0), lake (the toolchain of oracle/lean-toolchain), python3.
set -euo pipefail
cd "$(dirname "$0")/.."
SAMPLES=${1:-10000}
TRACES=${2:-50}
STEPS=40
SEED=20261117
MODEL=quint/gpu_service.qnt
INSTANCES="svc_default svc_keep svc_bench svc_nodevice svc_wsl svc_wsl_tight svc_limit1 \
  svc_flow svc_flow_keep svc_flow_wsl svc_accept svc_accept_keep svc_accept_flow \
  svc_accept_wsl svc_breaker1 svc_breaker0 svc_breaker_short svc_breaker_nocool \
  svc_container svc_container1"
TESTS="test_default test_keep test_wsl test_nodevice test_accept test_accept_keep \
  test_accept_nodevice test_accept_wsl test_breaker_short test_breaker1 test_breaker2 test_breaker0 test_container test_container1"
# Refusal tests (a terminal .fail()): run, not replayed, because Quint 0.32.0 exports
# an empty last frame for them.
REFUSALS="refuse_default refuse_nodevice refuse_accept"
WITNESSES="w_wait w_evict w_cpu w_queued w_busy w_stopped w_degraded w_served w_lease w_error \
  w_breaker_open w_breaker_skip w_breaker_closed w_breaker_after w_breaker_reopen \
  w_breaker_reset w_breaker_aged w_fail_reply w_fail_crash w_fail_two w_accept_refused \
  w_accept_shortcut w_accept_evict w_accept_fallback w_accept_served w_decline0 \
  w_decline1 w_decline2 w_decline3 w_decline4 w_decline5 w_decline6 w_keep_tables \
  w_keep_evict w_readback w_accept_unserved w_refused w_wipe_error w_overbound w_none \
  w_wsl_work w_run_failed w_restart_aged w_expected_served w_readback_proved \
  w_accept_expected_served w_expected_then_fault \
  w_served_open w_fail_open"
# `prev` is a ghost variable of the model (the state before the last step). It is
# not part of the wire contract, so it is not sent to the oracle.
DROP="--drop prev"
export LEAN_ABORT_ON_PANIC=1

(cd oracle && lake build --wfail >/dev/null)
ORACLE=oracle/.lake/build/bin/oracle

quint typecheck "$MODEL"
python3 -I scripts/quint_assignment_lint.py "$MODEL"

rm -rf quint/traces
for inst in $INSTANCES; do
  echo "== $inst"
  quint run "$MODEL" --main "$inst" --invariant inv --max-samples "$SAMPLES" \
    --max-steps "$STEPS" --seed "$SEED" --witnesses $WITNESSES 2>&1 \
    | grep -E '^\[ok\]|violat|witnessed' | sed 's/^/   /'
  mkdir -p "quint/traces/$inst"
  quint run "$MODEL" --main "$inst" --invariant inv --max-samples "$TRACES" \
    --n-traces "$TRACES" --max-steps "$STEPS" --seed "$SEED" \
    --out-itf "quint/traces/$inst/t_{seq}.itf.json" >/dev/null
  python3 -I scripts/quint_replay.py --oracle "$ORACLE" --traces "quint/traces/$inst" \
    --op-var lastOp --compare s $DROP
done

# Directed tests of the event-driven requirements, replayed as well.
for mod in $TESTS; do
  echo "== $mod (directed)"
  mkdir -p "quint/traces/$mod"
  quint test quint/gpu_service_test.qnt --main "$mod" --match 'Test$' \
    --out-itf "quint/traces/$mod/out_{test}_{seq}.itf.json" 2>&1 | grep -E 'passing|failing' | sed 's/^/   /'
  python3 -I scripts/quint_replay.py --oracle "$ORACLE" --traces "quint/traces/$mod" \
    --op-var lastOp --compare s $DROP
done

for mod in $REFUSALS; do
  echo "== $mod (refusals, not replayed)"
  quint test quint/gpu_service_test.qnt --main "$mod" --match 'Test$' 2>&1 \
    | grep -E 'passing|failing' | sed 's/^/   /'
done

# Negative control: change the resident size in the copied traces of the first
# instance. The model's states then disagree with what the oracle computes.
neg=$(mktemp -d)
trap 'rm -rf "$neg"' EXIT
python3 -I scripts/perturb_traces.py quint/traces/svc_default "$neg" resident 1
if python3 -I scripts/quint_replay.py --oracle "$ORACLE" --traces "$neg" --op-var lastOp \
    --compare s $DROP >"$neg/out.txt" 2>&1; then
  echo "negative control FAILED: a perturbed trace set agreed"; exit 1
fi
grep -q DISAGREE "$neg/out.txt" && echo "negative control: perturbed traces DISAGREE (expected)"

# Frame 0 of every trace must be the oracle's start state for that
# configuration (the replay compares transitions only), and the check must be
# able to fail: a clock moved by 1 in the copied traces differs.
python3 -I scripts/check_initial_states.py "$ORACLE" quint/traces/*/
python3 -I scripts/perturb_traces.py quint/traces/svc_default "$neg/init" clock 1
if python3 -I scripts/check_initial_states.py "$ORACLE" "$neg/init" >"$neg/init.txt" 2>&1; then
  echo "negative control FAILED: a perturbed start state passed"; exit 1
fi
echo "negative control: a perturbed start state differs (expected)"
