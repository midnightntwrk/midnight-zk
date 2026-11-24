#!/usr/bin/env bash

# This file is part of midnight-zk.
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

# Test of check-cdi.sh and of the start gate run-gpu.sh. Needs no GPU.
#
# Hermetic part: a temporary WSL2 driver root (CDI_WSL_DRIVERS_ROOT) with an
# old and a live driver directory, specs that name one or the other, and a
# stub nvidia-ctk (CDI_NVIDIA_CTK) that generates a spec for the live
# directory. Without nvidia-ctk, check-cdi.sh takes the one directory that
# holds libcuda.so.1.1 as the live driver and refuses when there is not
# exactly one. The command behind run-gpu.sh writes a marker file, so the test
# sees whether it ran.
#
# Host part (WSL2 only, skipped elsewhere): copies the host spec, renames its
# driver directory, and checks that run-gpu.sh refuses the copy. Set
# CDI_HOST_SPEC to choose the spec (default /etc/cdi/nvidia.yaml) or
# SKIP_HOST=1 to skip this part.
#
# Usage: gpu-prover/container/check-cdi.test.sh

set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
run_gpu="$here/run-gpu.sh"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
fail=0

root="$work/drivers"
live="$root/nvlive.inf_amd64_1111"
old="$root/nvold.inf_amd64_0000"
mkdir -p "$live" "$old" "$work/bin"
touch "$live/libcuda.so.1.1" "$live/nvidia-smi" "$old/libcuda.so.1.1" "$old/nvidia-smi"

spec_for() {
  # spec_for <driver dir>: a CDI spec in the layout of nvidia-ctk.
  cat <<SPEC
cdiVersion: 0.3.0
kind: nvidia.com/gpu
devices:
- name: all
  containerEdits:
    deviceNodes:
    - path: /dev/null
containerEdits:
  mounts:
  - hostPath: $1/libcuda.so.1.1
    containerPath: $1/libcuda.so.1.1
  - hostPath: $1/nvidia-smi
    containerPath: $1/nvidia-smi
SPEC
}

cat >"$work/bin/nvidia-ctk" <<STUB
#!/bin/sh
# stub: 'nvidia-ctk cdi generate' prints a spec for the live driver
[ "\$1 \$2" = "cdi generate" ] || exit 2
cat "$work/live.yaml"
STUB
chmod +x "$work/bin/nvidia-ctk"
spec_for "$live" >"$work/live.yaml"

# case_ <name> <want: run|refuse> <spec files> <nvidia-ctk command> [driver
# root]: runs run-gpu.sh with the spec list in MIDNIGHT_GPU_CDI_SPECS and
# checks whether the command ran.
case_() {
  local name="$1" want="$2" specs="$3" ctk="$4" droot="${5:-$root}"
  local marker="$work/ran.$name"
  local rc=0
  CDI_NVIDIA_CTK="$ctk" CDI_WSL_DRIVERS_ROOT="$droot" MIDNIGHT_GPU_CDI_SPECS="$specs" \
    "$run_gpu" touch "$marker" >"$work/out.$name" 2>&1 || rc=$?
  local got=refuse
  [[ -e "$marker" ]] && got=run
  if [[ "$got" == "$want" ]] && { [[ "$want" == run && $rc -eq 0 ]] || [[ "$want" == refuse && $rc -eq 1 ]]; }; then
    echo "ok   $name: $got (exit $rc)"
  else
    echo "FAIL $name: want $want, got $got (exit $rc)"
    sed 's/^/     /' "$work/out.$name"
    fail=1
  fi
}

with_ctk="$work/bin/nvidia-ctk"
no_ctk="$work/bin/absent-nvidia-ctk"

spec_for "$live" >"$work/current.yaml"
spec_for "$old" >"$work/stale-old-dir.yaml"
spec_for "$root/nvgone.inf_amd64_2222" >"$work/stale-missing-dir.yaml"

case_ current run "$work/current.yaml" "$with_ctk"
case_ stale-old-dir-still-on-disk refuse "$work/stale-old-dir.yaml" "$with_ctk"
case_ stale-missing-dir refuse "$work/stale-missing-dir.yaml" "$with_ctk"
case_ stale-missing-dir-no-nvidia-ctk refuse "$work/stale-missing-dir.yaml" "$no_ctk"
case_ stale-old-directory-no-ctk refuse "$work/stale-old-dir.yaml" "$no_ctk"
case_ no-spec-file refuse "$work/absent.yaml" "$with_ctk"
case_ one-current-one-stale refuse "$work/current.yaml $work/stale-old-dir.yaml" "$with_ctk"

# Without nvidia-ctk. In $root the old directory still holds its files,
# libcuda.so.1.1 included, so the live driver cannot be identified.
case_ no-ctk-stale-old-dir-still-on-disk refuse "$work/stale-old-dir.yaml" "$no_ctk"
case_ no-ctk-two-driver-dirs-current-spec refuse "$work/current.yaml" "$no_ctk"
# $root1: only the live directory holds libcuda.so.1.1; the old directory
# keeps other files.
root1="$work/drivers1"
mkdir -p "$root1/nvlive.inf_amd64_1111" "$root1/nvold.inf_amd64_0000"
touch "$root1/nvlive.inf_amd64_1111/libcuda.so.1.1" "$root1/nvlive.inf_amd64_1111/nvidia-smi" \
  "$root1/nvold.inf_amd64_0000/nvidia-smi"
spec_for "$root1/nvlive.inf_amd64_1111" >"$work/current1.yaml"
cat >"$work/stale1.yaml" <<SPEC
cdiVersion: 0.3.0
kind: nvidia.com/gpu
containerEdits:
  mounts:
  - hostPath: $root1/nvold.inf_amd64_0000/nvidia-smi
    containerPath: $root1/nvold.inf_amd64_0000/nvidia-smi
SPEC
case_ no-ctk-one-driver-dir-current-spec run "$work/current1.yaml" "$no_ctk" "$root1"
case_ no-ctk-stale-dir-paths-present refuse "$work/stale1.yaml" "$no_ctk" "$root1"
# $root2: no directory holds libcuda.so.1.1.
root2="$work/drivers2"
mkdir -p "$root2/nvold.inf_amd64_0000"
touch "$root2/nvold.inf_amd64_0000/nvidia-smi"
sed "s#$root1#$root2#g" "$work/stale1.yaml" >"$work/stale2.yaml"
case_ no-ctk-no-driver-dir refuse "$work/stale2.yaml" "$no_ctk" "$root2"

# --- host part ---------------------------------------------------------------
host_spec="${CDI_HOST_SPEC:-/etc/cdi/nvidia.yaml}"
if [[ "${SKIP_HOST:-0}" == 1 ]]; then
  echo "skip host: SKIP_HOST=1"
elif [[ ! -r "$host_spec" ]] || ! grep -q '/usr/lib/wsl/drivers/' "$host_spec" || ! command -v nvidia-ctk >/dev/null; then
  echo "skip host: no readable WSL2 CDI spec at $host_spec, or no nvidia-ctk"
else
  run_host() {
    local name="$1" want="$2" spec="$3" marker="$work/ran.host-$1" rc=0
    MIDNIGHT_GPU_CDI_SPECS="$spec" "$run_gpu" touch "$marker" >"$work/out.host-$name" 2>&1 || rc=$?
    local got=refuse
    [[ -e "$marker" ]] && got=run
    if [[ "$got" == "$want" ]]; then
      echo "ok   host-$name: $got (exit $rc)"
    else
      echo "FAIL host-$name: want $want, got $got (exit $rc)"
      sed 's/^/     /' "$work/out.host-$name"
      fail=1
    fi
  }
  run_host current run "$host_spec"
  sed -E 's#(/usr/lib/wsl/drivers/)[^/"[:space:]]+#\1nvstale.inf_amd64_0000000000000000#g' \
    "$host_spec" >"$work/host-stale.yaml"
  run_host renamed-driver-dir refuse "$work/host-stale.yaml"
  # the same without nvidia-ctk: the live driver comes from the driver root
  CDI_NVIDIA_CTK="$work/bin/absent-nvidia-ctk" run_host no-ctk-current run "$host_spec"
  CDI_NVIDIA_CTK="$work/bin/absent-nvidia-ctk" run_host no-ctk-renamed-driver-dir refuse "$work/host-stale.yaml"
fi

exit "$fail"
