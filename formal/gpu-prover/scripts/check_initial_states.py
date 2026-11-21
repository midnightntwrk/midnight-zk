#!/usr/bin/env python3
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
"""Check frame 0 of every saved Quint trace against the oracle's start state.

The replay sends each state of a trace to `oracle --step`, so it compares
transitions; it would agree from a wrong start state. This check takes the
configuration of frame 0, asks the oracle for the end state of the empty run
(`init`), and compares every field of the record `s`.
Usage: check_initial_states.py ORACLE TRACES_DIR [TRACES_DIR ...]"""
import importlib.util
import json
import os
import pathlib
import subprocess
import sys

here = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("quint_replay", here / "quint_replay.py")
qr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(qr)

CONFIG = ["perProof", "resident", "reduced", "budget", "keep", "wsl", "device", "limit",
          "window", "bench", "acceptance", "brLimit", "brWindow", "brCooldown"]


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    oracle, dirs = sys.argv[1], sys.argv[2:]
    env = dict(os.environ, LEAN_ABORT_ON_PANIC="1")
    checked, bad = 0, []
    for d in dirs:
        for f in sorted(pathlib.Path(d).glob("*.itf.json")):
            frame = json.loads(f.read_text())["states"][0]
            key = [k for k in frame if qr.short(k) == "s"]
            if len(key) != 1:
                sys.exit(f"{f}: no state variable s in frame 0")
            s0 = qr.itf_value(frame[key[0]])
            req = {"protocol": "kink-implementation/1",
                   "inputs": {"config": {k: s0[k] for k in CONFIG}, "ops": []}}
            out = subprocess.run([oracle], input=json.dumps(req), capture_output=True,
                                 text=True, env=env, timeout=60)
            ans = json.loads(out.stdout)
            if ans.get("end") != "final":
                bad.append((str(f), "oracle: " + out.stdout.strip()[:120]))
                continue
            init = ans["cells"]["s"]
            diff = sorted(k for k in set(init) | set(s0) if init.get(k) != s0.get(k))
            checked += 1
            if diff:
                bad.append((str(f), "fields differ: " + ", ".join(diff)))
    for b in bad:
        print("initial state: %s: %s" % b)
    print(f"initial states: {checked} traces checked, {len(bad)} differ")
    sys.exit(1 if bad or checked == 0 else 0)


main()
