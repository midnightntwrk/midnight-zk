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

# Container entrypoint for midnight-gpu-proverd.
#
# Checks the mounts, then runs the daemon as PID 1 (exec), so that signals
# and the exit code reach the container runtime and its restart policy.
# Arguments are passed to the daemon unchanged.

set -eu

socket="${MIDNIGHT_GPU_PROVER_SOCKET:-/run/midnight-gpu-prover/proverd.sock}"
socket_dir="$(dirname "$socket")"

# The SRS comes from MIDNIGHT_GPU_PROVER_SRS unless --srs or
# --insecure-test-srs is given on the command line.
srs_arg=no
for a in "$@"; do
  case "$a" in
    --srs | --srs=* | --insecure-test-srs) srs_arg=yes ;;
  esac
done
if [ "$srs_arg" = no ]; then
  srs="${MIDNIGHT_GPU_PROVER_SRS:-}"
  if [ -z "$srs" ]; then
    echo "entrypoint: set MIDNIGHT_GPU_PROVER_SRS to the SRS file (mounted read-only under /srv/midnight/srs)" >&2
    exit 64
  fi
  if [ ! -f "$srs" ] || [ ! -r "$srs" ]; then
    echo "entrypoint: SRS file $srs is missing or not readable" >&2
    exit 64
  fi
  if [ -w "$srs" ]; then
    echo "entrypoint: warning: SRS file $srs is writable; mount it read-only (:ro)" >&2
  fi
fi
if [ ! -d "$socket_dir" ] || [ ! -w "$socket_dir" ]; then
  echo "entrypoint: socket directory $socket_dir is missing or not writable by uid $(id -u)" >&2
  exit 64
fi

exec /usr/local/bin/midnight-gpu-proverd "$@"
