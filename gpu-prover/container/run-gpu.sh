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

# Start gate for a GPU prover container that uses CDI.
#
# Runs check-cdi.sh on the CDI specs first. If a spec is missing or stale
# (for example a WSL2 driver directory that the driver update replaced), it
# refuses to start and exits 1 without running the command. Otherwise it
# replaces itself with the command.
#
# Usage: run-gpu.sh COMMAND [ARG ...]
#   run-gpu.sh docker run -d --device nvidia.com/gpu=all ... midnight-gpu-prover:local
#   run-gpu.sh docker compose -f gpu-prover/container/compose.yaml --profile cdi up -d prover-cdi
#
# MIDNIGHT_GPU_CDI_SPECS: space-separated spec files to check (default: the
# defaults of check-cdi.sh, /etc/cdi/nvidia.yaml and /var/run/cdi/nvidia.yaml).
# CHECK_CDI: the check script (default: check-cdi.sh next to this file).

set -euo pipefail

if [[ $# -eq 0 ]]; then
  echo "usage: run-gpu.sh COMMAND [ARG ...]" >&2
  exit 2
fi

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
check="${CHECK_CDI:-$here/check-cdi.sh}"

# Word splitting is intended: the variable holds a list of files.
# shellcheck disable=SC2086
if ! bash "$check" ${MIDNIGHT_GPU_CDI_SPECS:-}; then
  echo "run-gpu: refusing to start: the CDI spec is missing or stale" >&2
  exit 1
fi

exec "$@"
