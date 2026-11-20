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
# Builds compact-bench.
#
# Usage: scripts/build.sh [--proof-server] stock                  # stock midnight-proofs (CPU)
#        scripts/build.sh [--proof-server] hooked PROOFS BACKEND  # GPU build
#
#   --proof-server  build the proof server 9.0.1 wrapper in proof-server/ (binary
#                   gpu-proof-server) instead of compact-bench.
#
#   PROOFS   a midnight-proofs 0.8.3 crate directory with the GPU hooks.
#   BACKEND  a crate named `compact-bench-gpu` with the API of gpu-backend-stub/
#            (install_hooks, counters, reset_counters) that registers its device
#            functions in the hooks of PROOFS.
#
# `[patch]` cannot depend on a cargo feature, so the hooked build passes both patches on the
# command line (`--config`) and builds into its own target directory. Cargo.lock stays the
# stock lock: the script restores it and keeps the hooked lock as target/hooked/Cargo.lock.
# The binary records the midnight-proofs source in every result row (`proofs_source`), and the
# backend label comes from the hooks that were installed at run time.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
bin=compact-bench
if [[ "${1:-}" == --proof-server ]]; then
  shift
  cd proof-server
  bin=gpu-proof-server
fi
mode="${1:?usage: build.sh stock | hooked PROOFS BACKEND}"
case "$mode" in
  stock)
    CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-target/stock}" cargo build --release --locked
    echo "binary: ${CARGO_TARGET_DIR:-target/stock}/release/$bin"
    ;;
  hooked)
    proofs="$(cd "${2:?hooked build needs the hooked midnight-proofs directory}" && pwd)"
    backend="$(cd "${3:?hooked build needs the backend crate directory}" && pwd)"
    target="${CARGO_TARGET_DIR:-target/hooked}"
    mkdir -p "$target"
    rev="$(git -C "$proofs" rev-parse --short HEAD 2>/dev/null || echo local)"
    cp Cargo.lock "$target/Cargo.lock.stock"
    trap 'cp "$target/Cargo.lock.stock" Cargo.lock' EXIT
    patches=(--config "patch.crates-io.midnight-proofs.path=\"$proofs\""
      --config "patch.crates-io.compact-bench-gpu.path=\"$backend\"")
    # A lock that pins another 0.8.x (the proof server's lock pins 0.8.2) keeps that version
    # unless it is moved to the patched crate first.
    locked="$(awk '$0 == "name = \"midnight-proofs\"" { getline; print }' Cargo.lock |
      grep -o '0\.8\.[0-9]*' | grep -vx 0.8.3 | head -1 || true)"
    if [[ -n "$locked" ]]; then
      cargo update "${patches[@]}" -p "midnight-proofs@$locked"
    fi
    BENCH_PROOFS_SOURCE="path:midnight-proofs-0.8.3-hooked@$rev" CARGO_TARGET_DIR="$target" \
      cargo build --release --features gpu "${patches[@]}"
    cp Cargo.lock "$target/Cargo.lock"
    echo "binary: $target/release/$bin"
    ;;
  *) echo "usage: build.sh stock | hooked PROOFS BACKEND" >&2; exit 2 ;;
esac
