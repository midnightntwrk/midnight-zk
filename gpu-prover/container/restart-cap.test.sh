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

# Restart-cap test. Needs no GPU.
#
# 1. systemd: runs a stub service that always exits 1 with the restart
#    settings of midnight-gpu-proverd.service (Restart, StartLimitBurst,
#    StartLimitIntervalSec read from the file) as a transient user unit, and
#    checks that systemd stops starting it after the burst and leaves it
#    failed with Result=start-limit-hit.
# 2. docker: runs a stub container with the restart policy of compose.yaml
#    (on-failure:3) and checks RestartCount == 3 and that the container stays
#    exited.
#
# Only the unit and container made here are touched; they are removed at the
# end. Set SKIP_SYSTEMD=1 or SKIP_DOCKER=1 to skip a part.
#
# Usage: gpu-prover/container/restart-cap.test.sh

set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
unit_file="$here/midnight-gpu-proverd.service"
compose_file="$here/compose.yaml"

# Tiny public image for the stub container, pinned by index digest.
STUB_IMAGE="${STUB_IMAGE:-docker.io/library/busybox:1.37.0@sha256:a7dbc319b1438115a207e11930dc4bb3e643dcb3ec0bdd694bb36cd8fad289ec}"

name="midnight-gpu-restart-cap-test-$$"
fail=0
work="$(mktemp -d)"
starts="$work/starts"

ini_value() {
  sed -nE "s/^$1=([^[:space:]]+).*/\1/p" "$unit_file" | tail -1
}

wait_for() {
  # wait_for <seconds> <command...>: polls once per second.
  local limit="$1"
  shift
  for ((i = 0; i < limit; i++)); do
    if "$@"; then return 0; fi
    sleep 1
  done
  return 1
}

cleanup() {
  if [[ "${SKIP_SYSTEMD:-0}" != 1 ]]; then
    systemctl --user stop "$name.service" >/dev/null 2>&1 || true
    systemctl --user reset-failed "$name.service" >/dev/null 2>&1 || true
  fi
  if [[ "${SKIP_DOCKER:-0}" != 1 ]]; then
    docker rm -f "$name" >/dev/null 2>&1 || true
  fi
  rm -rf "$work"
}
trap cleanup EXIT

# --- systemd ---------------------------------------------------------------
if [[ "${SKIP_SYSTEMD:-0}" != 1 ]]; then
  restart="$(ini_value Restart)"
  burst="$(ini_value StartLimitBurst)"
  interval="$(ini_value StartLimitIntervalSec)"
  echo "systemd: unit file has Restart=$restart StartLimitBurst=$burst StartLimitIntervalSec=$interval"

  systemd-run --user --quiet --unit="$name" \
    -p Restart="$restart" -p RestartSec=1s \
    -p StartLimitBurst="$burst" -p StartLimitIntervalSec="$interval" \
    /bin/sh -c "echo start >>'$starts'; exit 1"

  unit_failed() {
    [[ "$(systemctl --user show -p ActiveState --value "$name.service")" == failed ]]
  }
  if ! wait_for 60 unit_failed; then
    echo "FAIL systemd: unit did not reach failed state in 60 s"
    fail=1
  else
    sleep 3 # a further restart would show here
    show="$(systemctl --user show -p NRestarts,ActiveState,Result "$name.service")"
    nstarts="$(wc -l <"$starts")"
    echo "systemd: $(tr '\n' ' ' <<<"$show")starts=$nstarts"
    nrestarts="$(sed -n 's/^NRestarts=//p' <<<"$show")"
    state="$(sed -n 's/^ActiveState=//p' <<<"$show")"
    result="$(sed -n 's/^Result=//p' <<<"$show")"
    # StartLimitBurst=N allows N starts in the interval. The restart after the
    # Nth failure is refused; systemd counts it in NRestarts, so NRestarts=N.
    if [[ "$state" == failed && "$result" == start-limit-hit && "$nstarts" == "$burst" && "$nrestarts" == "$burst" ]]; then
      echo "ok   systemd: $nstarts starts in ${interval}s, then refused (NRestarts=$nrestarts, Result=start-limit-hit)"
    else
      echo "FAIL systemd: want ActiveState=failed Result=start-limit-hit starts=$burst NRestarts=$burst"
      fail=1
    fi
  fi
fi

# --- docker ----------------------------------------------------------------
if [[ "${SKIP_DOCKER:-0}" != 1 ]]; then
  policy="$(sed -nE 's/^[[:space:]]*restart:[[:space:]]*([^[:space:]#]+).*/\1/p' "$compose_file" | head -1)"
  max="${policy#on-failure:}"
  echo "docker: compose.yaml has restart: $policy"

  docker run -d --quiet --name "$name" --restart "$policy" --network none \
    "$STUB_IMAGE" sh -c 'exit 1' >/dev/null

  settled() {
    [[ "$(docker inspect -f '{{.State.Status}} {{.RestartCount}}' "$name")" == "exited $max" ]]
  }
  if ! wait_for 60 settled; then
    echo "FAIL docker: container did not settle at exited with RestartCount=$max in 60 s"
    docker inspect -f 'status={{.State.Status}} restarts={{.RestartCount}}' "$name" || true
    fail=1
  else
    sleep 5 # a further restart would show here
    got="$(docker inspect -f '{{.State.Status}} {{.RestartCount}} {{.State.ExitCode}}' "$name")"
    echo "docker: status, RestartCount, ExitCode = $got"
    if [[ "$got" == "exited $max 1" ]]; then
      echo "ok   docker: stopped after $max restarts ($((max + 1)) runs), container exited"
    else
      echo "FAIL docker: want 'exited $max 1'"
      fail=1
    fi
  fi
fi

exit "$fail"
