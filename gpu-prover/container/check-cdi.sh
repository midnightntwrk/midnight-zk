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

# Checks that a CDI spec for NVIDIA GPUs matches the live driver on the host.
#
# On WSL2 the GPU driver files live in a versioned directory under
# /usr/lib/wsl/drivers/ whose name changes when the Windows driver is updated.
# A CDI spec made by `nvidia-ctk cdi generate` names that directory. After a
# driver update the spec is stale: containers start but find no GPU or load a
# wrong library. This script refuses (exit 1) when any host path in the spec
# is missing, or when the spec names another WSL2 driver directory than the
# live driver. It tells the operator to regenerate the spec.
#
# The live WSL2 driver directory comes from `nvidia-ctk cdi generate` when
# nvidia-ctk is installed. Without nvidia-ctk it is the one directory under
# the driver root that holds libcuda.so.1.1. If there is no such directory or
# more than one, the live driver is not known and the script refuses (fail
# closed).
#
# Usage: check-cdi.sh [spec-file ...]
#   Default spec files: /etc/cdi/nvidia.yaml /var/run/cdi/nvidia.yaml
#   CDI_WSL_DRIVERS_ROOT: the WSL2 driver root (default /usr/lib/wsl/drivers);
#   CDI_NVIDIA_CTK: the nvidia-ctk command (default nvidia-ctk).
#   The test check-cdi.test.sh sets both.
#
# Exit 0: every spec is current. Exit 1: a spec is missing, unreadable or
# stale. run-gpu.sh runs this script before it starts a GPU container.

set -euo pipefail

drivers_root="${CDI_WSL_DRIVERS_ROOT:-/usr/lib/wsl/drivers}"
drivers_root="${drivers_root%/}"
ctk="${CDI_NVIDIA_CTK:-nvidia-ctk}"
# The root as a literal in an extended regular expression.
root_re=$(printf '%s' "$drivers_root" | sed -e 's/[][\\.*^$+?(){}|#]/\\&/g')

specs=("$@")
if [[ ${#specs[@]} -eq 0 ]]; then
  for f in /etc/cdi/nvidia.yaml /var/run/cdi/nvidia.yaml; do
    [[ -f "$f" ]] && specs+=("$f")
  done
fi
if [[ ${#specs[@]} -eq 0 ]]; then
  echo "check-cdi: no CDI spec found; run: sudo nvidia-ctk cdi generate --output=/etc/cdi/nvidia.yaml" >&2
  exit 1
fi

status=0
for spec in "${specs[@]}"; do
  if [[ ! -r "$spec" ]]; then
    echo "check-cdi: cannot read $spec" >&2
    status=1
    continue
  fi
  # Host paths in a CDI spec are values of hostPath: or path: keys.
  mapfile -t paths < <(sed -nE 's/^[[:space:]-]*(hostPath|path):[[:space:]]*"?([^"[:space:]]+)"?.*/\2/p' "$spec" | sort -u)
  missing=0
  for p in "${paths[@]}"; do
    case "$p" in
      /*) ;;
      *) continue ;;
    esac
    if [[ ! -e "$p" ]]; then
      echo "check-cdi: $spec names $p, which does not exist" >&2
      missing=1
    fi
  done
  wsl_dirs=$(printf '%s\n' "${paths[@]}" | sed -nE "s#^(${root_re}/[^/]+)/.*#\\1#p" | sort -u)
  if [[ -n "$wsl_dirs" ]]; then
    echo "check-cdi: $spec uses WSL2 driver directory: $wsl_dirs"
    # An old driver directory can stay on disk after a driver update, so
    # existence alone does not prove the spec is current. When nvidia-ctk is
    # present, compare with a spec made from the live driver now.
    if command -v "$ctk" >/dev/null 2>&1; then
      # Without --output, nvidia-ctk writes the spec to stdout. Do not use
      # --output=/dev/stdout: nvidia-ctk writes a temporary file in the
      # directory of the output and renames it, which fails in /dev.
      live_spec=$("$ctk" cdi generate 2>/dev/null) || live_spec=""
      live_dirs=$(sed -nE "s#.*(${root_re}/[^/\"[:space:]]+)/.*#\\1#p" <<<"$live_spec" | sort -u)
      if [[ -z "$live_dirs" ]]; then
        echo "check-cdi: nvidia-ctk found no WSL2 driver directory; cannot confirm $spec" >&2
        missing=1
      elif [[ "$live_dirs" != "$wsl_dirs" ]]; then
        echo "check-cdi: $spec names $wsl_dirs, the live driver is $live_dirs" >&2
        missing=1
      fi
    else
      # No nvidia-ctk: the live driver is the one directory with libcuda.
      live_dirs=$(for d in "$drivers_root"/*/; do
        if [[ -e "${d}libcuda.so.1.1" ]]; then printf '%s\n' "${d%/}"; fi
      done | sort -u)
      n_live=$(grep -c . <<<"$live_dirs" || true)
      if [[ "$n_live" -ne 1 ]]; then
        echo "check-cdi: nvidia-ctk not found and $n_live driver directories under $drivers_root hold libcuda.so.1.1; cannot identify the live driver, refusing $spec" >&2
        missing=1
      elif [[ "$live_dirs" != "$wsl_dirs" ]]; then
        echo "check-cdi: $spec names $wsl_dirs, the live driver is $live_dirs (found without nvidia-ctk)" >&2
        missing=1
      fi
    fi
  fi
  if [[ $missing -ne 0 ]]; then
    echo "check-cdi: $spec is stale; regenerate it: sudo nvidia-ctk cdi generate --output=$spec" >&2
    status=1
  else
    echo "check-cdi: $spec OK (${#paths[@]} host paths present)"
  fi
done
exit "$status"
