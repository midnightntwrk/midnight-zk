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

# Checks that a built prover image holds no test-seed build. Fails when:
#
# - any file in the image has "seeded" in its name (the `seeded_prove`
#   example and any other seeded tool), or
# - any file under the scanned directories contains a test-seed marker. The
#   marker MIDNIGHT-GPU-PROVER-TEST-SEED-BUILD-NOT-FOR-RELEASE is
#   `midnight_gpu_prover::device::TEST_SEED_MARKER`. Only a build with the
#   `test-seed` feature compiles it in, and every binary of such a build
#   writes it at start, so it is never removed as dead code.
#
# The image is not run: it is created (`docker create`) and its file system
# exported (`docker export`), so no entrypoint, GPU or network is needed.
#
# Usage: check-no-test-seed.sh IMAGE
#        check-no-test-seed.sh --rootfs DIR     (an unpacked file system)
#
# Environment:
#   SCAN_DIRS      directories (relative to the image root) whose files are
#                  searched for markers; default "usr/local opt srv"
#   EXTRA_MARKERS  more marker strings, one per line
#   DOCKER         docker command; default "docker"
#
# Exit status: 0 clean, 1 test-seed content found, 2 usage or docker error.

set -euo pipefail

MARKERS="MIDNIGHT-GPU-PROVER-TEST-SEED-BUILD-NOT-FOR-RELEASE"
if [[ -n "${EXTRA_MARKERS:-}" ]]; then
  MARKERS+=$'\n'"${EXTRA_MARKERS}"
fi
SCAN_DIRS="${SCAN_DIRS:-usr/local opt srv}"
DOCKER="${DOCKER:-docker}"

usage() {
  sed -n '/^# Usage:/,/^# Exit status/p' "$0" | sed 's/^# \{0,1\}//' >&2
  exit 2
}

work="$(mktemp -d)"
cid=""
cleanup() {
  if [[ -n "${cid}" ]]; then
    "${DOCKER}" rm -f "${cid}" >/dev/null 2>&1 || true
  fi
  rm -rf "${work}"
}
trap cleanup EXIT

case "${1:-}" in
  --rootfs)
    [[ $# -eq 2 && -d "$2" ]] || usage
    root="$2"
    names() { (cd "${root}" && find . -mindepth 1 | sed 's|^\./||'); }
    ;;
  "" | -h | --help)
    usage
    ;;
  *)
    [[ $# -eq 1 ]] || usage
    image="$1"
    if ! cid="$("${DOCKER}" create "${image}" 2>"${work}/err")"; then
      echo "check-no-test-seed: cannot create a container from ${image}:" >&2
      cat "${work}/err" >&2
      exit 2
    fi
    if ! "${DOCKER}" export -o "${work}/fs.tar" "${cid}"; then
      echo "check-no-test-seed: docker export failed" >&2
      exit 2
    fi
    root="${work}/root"
    mkdir -p "${root}"
    names() { tar -tf "${work}/fs.tar" | sed 's|/$||'; }
    # extract only the scanned directories (no device nodes, no ownership)
    for d in ${SCAN_DIRS}; do
      tar -xf "${work}/fs.tar" -C "${root}" --no-same-owner --no-same-permissions \
        --wildcards "${d}" "${d}/*" 2>/dev/null || true
    done
    ;;
esac

found=0

seeded="$(names | awk -F/ 'tolower($NF) ~ /seeded/' || true)"
if [[ -n "${seeded}" ]]; then
  echo "check-no-test-seed: files named *seeded* in the image:" >&2
  printf '  /%s\n' ${seeded} >&2
  found=1
fi

for d in ${SCAN_DIRS}; do
  [[ -d "${root}/${d}" ]] || continue
  while IFS= read -r marker; do
    [[ -n "${marker}" ]] || continue
    hits="$(grep -r -l -a -F -e "${marker}" "${root}/${d}" 2>/dev/null || true)"
    if [[ -n "${hits}" ]]; then
      echo "check-no-test-seed: test-seed marker '${marker}' in:" >&2
      printf '  /%s\n' $(printf '%s\n' "${hits}" | sed "s|^${root}/||") >&2
      found=1
    fi
  done <<<"${MARKERS}"
done

if [[ "${found}" -ne 0 ]]; then
  exit 1
fi
echo "check-no-test-seed: clean (no *seeded* file; no marker under ${SCAN_DIRS})"
