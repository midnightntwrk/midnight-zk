#!/bin/sh

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

# Container health check: sends the daemon's `health` request over its Unix
# socket with midnight-gpu-prover-client. Exit 0 = healthy, any other exit =
# unhealthy.
#
# MIDNIGHT_GPU_PROVER_HEALTH_CMD overrides the command.

set -eu

socket="${MIDNIGHT_GPU_PROVER_SOCKET:-/run/midnight-gpu-prover/proverd.sock}"

if [ ! -S "$socket" ]; then
  echo "healthcheck: no socket at $socket" >&2
  exit 1
fi

if [ -n "${MIDNIGHT_GPU_PROVER_HEALTH_CMD:-}" ]; then
  # Word splitting is intended: the variable holds a command line.
  # shellcheck disable=SC2086
  exec $MIDNIGHT_GPU_PROVER_HEALTH_CMD
fi

exec /usr/local/bin/midnight-gpu-prover-client --socket "$socket" health
