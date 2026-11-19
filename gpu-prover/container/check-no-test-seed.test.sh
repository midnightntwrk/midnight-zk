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

# Test of check-no-test-seed.sh. Needs no GPU and no network.
#
# 1. --rootfs: a clean tree passes; a file named *seeded* fails; a binary
#    with the marker fails.
# 2. Image mode (skipped with SKIP_DOCKER=1 or without docker): the same
#    three cases as `FROM scratch` images built here and removed at the end.
# 3. Real binaries (when RELEASE_BIN and SEED_BIN are set): RELEASE_BIN, a
#    daemon built with default features, passes; SEED_BIN, a daemon built
#    with `--features test-seed`, fails.
#
# Usage: gpu-prover/container/check-no-test-seed.test.sh

set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
check="${here}/check-no-test-seed.sh"
marker="MIDNIGHT-GPU-PROVER-TEST-SEED-BUILD-NOT-FOR-RELEASE"
work="$(mktemp -d)"
images=()
cleanup() {
  for i in "${images[@]}"; do docker rmi -f "${i}" >/dev/null 2>&1 || true; done
  rm -rf "${work}"
}
trap cleanup EXIT

fail=0
expect() { # expect STATUS DESCRIPTION -- COMMAND...
  local want="$1" what="$2"
  shift 3
  local got=0
  "$@" >/dev/null 2>&1 || got=$?
  if [[ "${got}" -eq "${want}" ]]; then
    echo "ok   ${what}"
  else
    echo "FAIL ${what}: exit ${got}, expected ${want}"
    fail=1
  fi
}

mk_tree() { # mk_tree DIR KIND
  mkdir -p "$1/usr/local/bin"
  printf '\177ELF clean daemon\n' >"$1/usr/local/bin/midnight-gpu-proverd"
  case "$2" in
    seeded) printf '\177ELF\n' >"$1/usr/local/bin/seeded_prove" ;;
    marker) printf '\177ELF x %s y\n' "${marker}" >"$1/usr/local/bin/midnight-gpu-prover-client" ;;
  esac
}

for kind in clean seeded marker; do
  mk_tree "${work}/${kind}" "${kind}"
done
expect 0 "rootfs: clean tree passes" -- "${check}" --rootfs "${work}/clean"
expect 1 "rootfs: *seeded* file fails" -- "${check}" --rootfs "${work}/seeded"
expect 1 "rootfs: marker fails" -- "${check}" --rootfs "${work}/marker"
expect 2 "usage error" -- "${check}"

if [[ "${SKIP_DOCKER:-0}" != 1 ]] && command -v docker >/dev/null && docker info >/dev/null 2>&1; then
  for kind in clean seeded marker; do
    tag="midnight-gpu-prover-check-test:${kind}-$$"
    printf 'FROM scratch\nCOPY usr /usr\nCMD ["/usr/local/bin/midnight-gpu-proverd"]\n' \
      >"${work}/${kind}/Dockerfile"
    docker build -q -t "${tag}" "${work}/${kind}" >/dev/null
    images+=("${tag}")
  done
  expect 0 "image: clean passes" -- "${check}" "midnight-gpu-prover-check-test:clean-$$"
  expect 1 "image: *seeded* file fails" -- "${check}" "midnight-gpu-prover-check-test:seeded-$$"
  expect 1 "image: marker fails" -- "${check}" "midnight-gpu-prover-check-test:marker-$$"
  expect 2 "image: missing image" -- "${check}" "midnight-gpu-prover-check-test:none-$$"
else
  echo "skip image mode (no docker or SKIP_DOCKER=1)"
fi

if [[ -n "${RELEASE_BIN:-}" && -n "${SEED_BIN:-}" ]]; then
  for kind in release seed; do
    mkdir -p "${work}/real-${kind}/usr/local/bin"
  done
  cp "${RELEASE_BIN}" "${work}/real-release/usr/local/bin/midnight-gpu-proverd"
  cp "${SEED_BIN}" "${work}/real-seed/usr/local/bin/midnight-gpu-proverd"
  expect 0 "real: default-feature daemon passes" -- "${check}" --rootfs "${work}/real-release"
  expect 1 "real: test-seed daemon fails" -- "${check}" --rootfs "${work}/real-seed"
else
  echo "skip real binaries (set RELEASE_BIN and SEED_BIN)"
fi

exit "${fail}"
