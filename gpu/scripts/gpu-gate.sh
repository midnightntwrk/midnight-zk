#!/usr/bin/env bash
# This file is part of MIDNIGHT-ZK.
# Copyright (C) Midnight Foundation
# SPDX-License-Identifier: Apache-2.0
# Licensed under the Apache License, Version 2.0 (the "License");
# You may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# http://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# The GPU gate of midnight-gpu: builds the CUDA core (a missing nvcc is an
# error here), then runs every device test, the ignored ones included (the
# 10,000-system quotient fuzz, with its node coverage), one test binary at a
# time, and the kernel harness, which writes a TSV.
#
# Usage: gpu/scripts/gpu-gate.sh [OUT_DIR]   (default target/gpu-gate)
#
# Environment:
#   CUDA_PATH / CUDA_HOME / nvcc on PATH   the CUDA toolkit (see build.rs)
#   MIDNIGHT_GPU_ARCHS                     architectures to build (see build.rs)
#   MIDNIGHT_GPU_GATE_WRAP                 a command prefix for each device run,
#                                          e.g. a device lock (default: none);
#                                          the harness's MSM time ratios need
#                                          the device to itself
#   MIDNIGHT_GPU_HARNESS_MAX_K             top size of the harness (default 21)
#   ORACLE_ITF_DIR                         frozen ITF directory, relative to the
#                                          repo root (defaults to the in-tree
#                                          Quint gate output, generated when
#                                          missing).
#                                          On a fresh checkout the Quint gate
#                                          produces the traces (needs quint/lake).
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
out=${1:-$root/target/gpu-gate}
mkdir -p "$out"
out=$(realpath --relative-to="$root" "$out")
cd "$root"
export MIDNIGHT_GPU_REQUIRE_CUDA=1
features=cuda,test-fault
wrap=${MIDNIGHT_GPU_GATE_WRAP:-}

traces=${ORACLE_ITF_DIR:-gpu-spec/quint/traces}
if [[ -z ${ORACLE_ITF_DIR:-} ]]; then
    if [[ ! -d $traces ]]; then
        echo "== generate the frozen model's ITF traces"
        bash gpu-spec/scripts/quint_check.sh 50 50 >"$out/quint-traces.log" 2>&1 || {
            tail -n 10 "$out/quint-traces.log" >&2
            exit 1
        }
    fi
fi
if [[ ! -d $traces ]]; then
    echo "Missing frozen ITF traces. Run gpu-spec/scripts/quint_check.sh 50 50 or set ORACLE_ITF_DIR." >&2
    exit 1
fi

digest=$(cd gpu-spec/vectors && export LC_ALL=C && sha256sum -- *.json | sha256sum)
if [[ ${digest%% *} != de054ca4572a2e7df5abf2eb39361da80c8f5b6c48c1de269c56605c16bd1ffb ]]; then
    echo "Unexpected e5b2e4dc v2 vector digest" >&2
    exit 1
fi

echo "== build"
# Read the artifacts from this build. pipefail propagates a partial build failure.
test_bins=$(cargo test --offline --locked --release -p midnight-gpu --features "$features" --tests --no-run \
    --message-format=json-render-diagnostics | sed -n 's/.*"executable":"\([^"]*\)".*/\1/p')
[[ -n $test_bins ]] || { echo "no test binary found"; exit 1; }
mapfile -t bins <<<"$test_bins"
cargo build --offline --locked --release -p midnight-gpu --features "$features" --example kernels 2>&1 | tail -n 1

status=0
for fixture in ntt msm coset quotient gate threshold datamove; do
    test -s "gpu-spec/vectors/$fixture.json" || { echo "Missing v2 fixture $fixture" >&2; exit 1; }
done

echo "== service vectors v2 and Quint ITF through the daemon adapter"
service_tests=service::oracle_conformance
# Cargo runs these two unit tests from gpu-prover/. Both use a test Device.
if ! ORACLE_VECTOR_DIR=../gpu-spec/vectors \
    ORACLE_ITF_DIR="$(realpath --relative-to=gpu-prover "$traces")" \
    ORACLE_ITF_EVIDENCE="$(realpath -m --relative-to=gpu-prover "$out/daemon-itf.jsonl")" \
    RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-2}" \
    cargo test --offline --locked --release -p midnight-gpu-prover --lib -- \
    --exact "${service_tests}::service_oracle_vectors" "${service_tests}::itf::quint_daemon_gate" \
    --include-ignored --test-threads=1 --nocapture >"$out/daemon-itf.log" 2>&1 ||
    ! grep -Fq 'test result: ok. 2 passed;' "$out/daemon-itf.log"; then
    status=1
fi
grep -E 'service traces,|daemon ITF:|^test result|FAILED|panicked' "$out/daemon-itf.log" || true

found_vectors=false
for b in "${bins[@]}"; do
    name=$(basename "$b")
    # The no-CUDA workflow runs this binary against the stub.
    [[ $name == stub-* ]] && continue
    log="$out/$name.log"
    if [[ $name == oracle_arithmetic-* ]]; then
        found_vectors=true
        log="$out/oracle-arithmetic-v2.log"
        echo "== oracle arithmetic v2 (including gate and threshold)"
    else
        echo "== $name"
    fi
    # These prebuilt binaries run from the repository root.
    # shellcheck disable=SC2086
    if ! ORACLE_VECTOR_DIR=gpu-spec/vectors $wrap "$b" --include-ignored --test-threads=1 --nocapture \
        >"$log" 2>&1; then
        status=1
    fi
    if [[ $name == oracle_arithmetic-* ]]; then
        rows=$(grep -Ec 'vector gpu (pass|inapplicable) ' "$log" || true)
        if [[ $rows != 121 ]]; then
            echo "Incomplete or failed v2 GPU vector run ($rows of 121 rows passed or inapplicable)" >&2
            status=1
        fi
    fi
    grep -E '^test result|FAILED|panicked|node coverage|skipped' "$log" || true
done
if [[ $found_vectors != true ]]; then
    echo "Missing oracle_arithmetic test binary" >&2
    status=1
fi

echo "== kernel harness"
# shellcheck disable=SC2086
tdir=$(cargo metadata --offline --locked --format-version 1 --no-deps |
    sed -n 's/.*"target_directory":"\([^"]*\)".*/\1/p')
# With no usable device the harness exits successfully without writing a TSV.
: >"$out/kernels.tsv"
if ! $wrap "$tdir/release/examples/kernels" "$out/kernels.tsv" \
    >"$out/kernels.log" 2>&1 || [[ ! -s $out/kernels.tsv ]]; then
    status=1
fi
grep -E 'FAILED|wrote|no device|MSM skew|: max ' "$out/kernels.log" || true

if [ "$status" -ne 0 ]; then
    echo "GPU gate: FAILED (logs in $out)"
    exit 1
fi
echo "GPU gate: passed (logs and kernels.tsv in $out)"
