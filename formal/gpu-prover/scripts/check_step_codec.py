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
"""Codec checks of the oracle's --step and default modes.

The fixture is a non-initial state written here by hand from the spec
(design.md, "Request state machine"), not copied from the oracle: at 7 s the
daemon crashes with one request in flight and one waiting (two failures at 7,
two CPU proofs), restarts at 7, and at 12 s serves a third request that was
admitted at step gpu (need 6 + 8 = 14, free 20), made one permitted read-back
and one decline with reason 4 (memory). It holds every field kind: naturals,
booleans and the three lists (`restartTimes`, `brFails`, `declines`), each with
a non-default value. The state is sent through --step with op 106 (the proof
ends, the verifier accepts) and the answer is compared field by field with the
expected state, also written by hand. The golden trace `crash-with-waiting`
must hold the same two states.

Controls. Each refusal control states the exact list of refusal codes, in a
state where the op is otherwise enabled (device work is active). Decode
controls (a dropped field of each kind, a wrong type of each kind, an extra
key, a non-canonical number, a fraction, a truncated line) must give `error`.
A changed field value must come back changed (the decoder reads that field).
The default mode must reproduce the final state of every golden trace.
Usage: check_step_codec.py ORACLE VECTOR_DIR
"""
import json
import os
import pathlib
import subprocess
import sys

oracle, vdir = sys.argv[1], pathlib.Path(sys.argv[2])
env = {**os.environ, "LEAN_ABORT_ON_PANIC": "1"}


def step(lines):
    out = subprocess.run([oracle, "--step"], input="\n".join(lines) + "\n", capture_output=True,
                         text=True, env=env, timeout=60)
    if out.returncode != 0 or out.stderr:
        sys.exit(f"oracle --step failed: rc={out.returncode} stderr={out.stderr!r}")
    return [json.loads(x) for x in out.stdout.splitlines()]


FIXTURE = {
    # configuration (the defaults)
    "perProof": 6, "resident": 8, "reduced": 2, "budget": 0, "keep": False, "wsl": False,
    "device": True, "limit": 3, "window": 600, "bench": False, "acceptance": False,
    "brLimit": 3, "brWindow": 600, "brCooldown": 600,
    # daemon: proving at step gpu, device work active, one fallback
    "up": True, "stopped": False, "phase": 2, "waiting": 0, "onDev": True, "tables": True,
    "dirty": True, "ctx": True, "devUsed": True, "devWork": True, "step": 1, "admNeed": 14,
    "admFree": 20, "fallbacks": 1, "degraded": True, "leaseLost": False, "overBound": False,
    "verifyOk": False, "wipeOk": False, "lockHeld": False, "cold": True, "clock": 12,
    "restartTimes": [7],
    # client breaker: two failures at 7 s, closed
    "brFails": [7, 7], "brOpenUntil": 0,
    # counters
    "requests": 3, "served": 0, "clientCpu": 2, "errors": 0, "busyReplies": 0,
    "degradedServed": 0, "readbacks": 1, "badReadbacks": 0, "unverifiedReturned": 0,
    "verifyAccepts": 0, "declines": [0, 0, 0, 0, 1, 0, 0], "declined": 1, "breakerSkips": 0,
    "degradedRefused": 0, "runFailed": False,
}
# op 106: the device phases end, the answer is stored; the accept is counted at the reply
AFTER_106 = {**FIXTURE, "phase": 3, "devWork": False, "verifyOk": True}
# op 304: a permitted read-back (base-domain transform output) is counted
AFTER_304 = {**FIXTURE, "readbacks": 2}
# op 603: a decline with reason 6 (device-error)
AFTER_603 = {**FIXTURE, "fallbacks": 2, "declines": [0, 0, 0, 0, 1, 0, 1], "declined": 2}
# op 5: lease loss: no device work, one fallback, not counted as a decline
AFTER_5 = {**FIXTURE, "devWork": False, "leaseLost": True, "fallbacks": 2}


def req(state, op):
    return json.dumps({"state": {"s": state}, "op": op})


def without(key):
    return {k: v for k, v in FIXTURE.items() if k != key}


def is_state(expected):
    return lambda a: a == {"state": {"s": expected}}


def refused(*codes):
    return lambda a: a == {"refused": list(codes)}


def is_error(a):
    return list(a.keys()) == ["error"]


fails = 0
good = req(FIXTURE, 106)
cases = [
    ("round trip, every field", good, is_state(AFTER_106)),
    ("read-back kind 3 accepted", req(FIXTURE, 304), is_state(AFTER_304)),
    ("decline reason 6 counted", req(FIXTURE, 603), is_state(AFTER_603)),
    ("lease loss", req(FIXTURE, 5), is_state(AFTER_5)),
    ("changed nat value kept", req({**FIXTURE, "readbacks": 9}, 106), is_state({**AFTER_106, "readbacks": 9})),
    ("changed list value kept", req({**FIXTURE, "brFails": [3, 12]}, 106),
     is_state({**AFTER_106, "brFails": [3, 12]})),
    ("changed bool value kept", req({**FIXTURE, "lockHeld": True}, 106),
     is_state({**AFTER_106, "lockHeld": True})),
    ("decimal string natural", req({**FIXTURE, "clock": "12"}, 106), is_state(AFTER_106)),
    # refusals: exact codes, the op is otherwise enabled in this state
    ("read-back kind 4 refused", req(FIXTURE, 404), refused("readback-not-permitted")),
    ("read-back kind 5 refused", req(FIXTURE, 504), refused("readback-not-permitted")),
    ("decline reason 7 refused", req(FIXTURE, 703), refused("bad-argument")),
    ("verifier answer 2 refused", req(FIXTURE, 206), refused("bad-argument")),
    ("unknown op", req(FIXTURE, 99), refused("not-an-operation")),
    ("op code 0", req(FIXTURE, 0), refused("not-an-operation")),
    ("wipe before the proof ends", req(FIXTURE, 107), refused("not-enabled")),
    ("state outside the domain: two waiting", req({**FIXTURE, "waiting": 2}, 111),
     refused("outside-state-domain")),
    ("state outside the domain: six decline counts", req({**FIXTURE, "declines": [0, 0, 0, 0, 1, 0]}, 111),
     refused("outside-state-domain")),
    ("state outside the domain: decline total", req({**FIXTURE, "declined": 2}, 111),
     refused("outside-state-domain")),
    ("state outside the domain: failure in the future", req({**FIXTURE, "brFails": [7, 13]}, 111),
     refused("outside-state-domain")),
    ("state outside the domain: record at the limit", req({**FIXTURE, "brFails": [7, 7, 7]}, 111),
     refused("outside-state-domain")),
    ("state outside the domain: bad read-back", req({**FIXTURE, "badReadbacks": 1}, 111),
     refused("outside-state-domain")),
    ("state outside the domain: unverified proof", req({**FIXTURE, "unverifiedReturned": 1}, 111),
     refused("outside-state-domain")),
    # decode errors
    ("dropped nat field", req(without("clock"), 106), is_error),
    ("dropped bool field", req(without("acceptance"), 106), is_error),
    ("dropped list field declines", req(without("declines"), 106), is_error),
    ("dropped list field brFails", req(without("brFails"), 106), is_error),
    ("dropped list field restartTimes", req(without("restartTimes"), 106), is_error),
    ("wrong type: bool as number", req({**FIXTURE, "up": 1}, 106), is_error),
    ("wrong type: nat as bool", req({**FIXTURE, "brLimit": True}, 106), is_error),
    ("wrong type: list as number", req({**FIXTURE, "declines": 1}, 106), is_error),
    ("wrong type: list of booleans", req({**FIXTURE, "brFails": [True, False]}, 106), is_error),
    ("negative number", req({**FIXTURE, "clock": -1}, 106), is_error),
    ("non-canonical decimal string", req({**FIXTURE, "clock": "012"}, 106), is_error),
    ("extra key", req({**FIXTURE, "extra": 0}, 106), is_error),
    ("unknown key minK", req({**FIXTURE, "minK": 14}, 106), is_error),
    ("fraction", good.replace('"op": 106', '"op": 106.5'), is_error),
    ("truncated line", good[:-9], is_error),
    ("duplicate key", good.replace('"clock": 12', '"clock": 12, "clock": 12'), is_error),
]
assert '"op": 106.5' in cases[-3][1] and '"clock": 12, "clock": 12' in cases[-1][1]
answers = step([c[1] for c in cases])
if len(answers) != len(cases):
    sys.exit(f"oracle --step gave {len(answers)} answers for {len(cases)} lines")
for (name, _, ok), ans in zip(cases, answers):
    print(("ok   " if ok(ans) else "FAIL ") + name + ("" if ok(ans) else f": {json.dumps(ans)[:300]}"))
    fails += not ok(ans)

# the hand-written states are the states of the golden trace
trace = json.loads((vdir / "service" / "crash-with-waiting.json").read_text())
ok = trace["ops"][11] == 106 and trace["states"][11] == FIXTURE and trace["states"][12] == AFTER_106
print(("ok   " if ok else "FAIL ") + "fixture equals the golden trace state")
fails += not ok

files = sorted((vdir / "service").glob("*.json"))
if len(files) != 29:
    print(f"FAIL expected 29 service traces, found {len(files)}")
    fails += 1
for f in files:
    t = json.loads(f.read_text())
    ok = t["format"] == "midnight-gpu-vectors/2" and len(t["states"]) == len(t["ops"]) + 1 \
        and len(t["refused"]) == len(t["ops"])
    print(("ok   " if ok else "FAIL ") + f"trace shape {f.name}")
    fails += not ok
    # the default mode stops at the first refusal: send the ops that apply
    ops = [o for o, r in zip(t["ops"], t["refused"]) if not r]
    req_ = {"protocol": "kink-implementation/1", "inputs": {"config": t["config"], "ops": ops}}
    out = subprocess.run([oracle], input=json.dumps(req_), capture_output=True, text=True, env=env, timeout=60)
    ans = json.loads(out.stdout) if out.returncode == 0 and not out.stderr else {}
    ok = ans.get("end") == "final" and ans.get("cells") == {"s": t["states"][-1]}
    print(("ok   " if ok else "FAIL ") + f"default mode {f.name}")
    fails += not ok
    first = next((i for i, r in enumerate(t["refused"]) if r), None)
    if first is not None:
        req_["inputs"]["ops"] = t["ops"]
        out = subprocess.run([oracle], input=json.dumps(req_), capture_output=True, text=True, env=env,
                             timeout=60)
        ok = out.returncode == 0 and json.loads(out.stdout) == \
            {"end": "could-not-apply", "reason": "|".join(sorted(t["refused"][first]))}
        print(("ok   " if ok else "FAIL ") + f"default mode refusal {f.name}")
        fails += not ok


def default(config):
    req_ = {"protocol": "kink-implementation/1", "inputs": {"config": config, "ops": []}}
    out = subprocess.run([oracle], input=json.dumps(req_), capture_output=True, text=True, env=env, timeout=60)
    return out.returncode, (json.loads(out.stdout) if out.stdout else None)


config = {k: FIXTURE[k] for k in ["perProof", "resident", "reduced", "budget", "keep", "wsl", "device",
                                  "limit", "window", "bench", "acceptance", "brLimit", "brWindow",
                                  "brCooldown"]}
checks = [
    ("default mode accepts the configuration", default(config)[1] is not None
     and default(config)[1].get("end") == "final"
     and default(config)[1]["cells"]["s"]["declines"] == [0] * 7),
    ("default mode refuses keep on WSL2", default({**config, "wsl": True, "keep": True})
     == (0, {"end": "could-not-apply", "reason": "wsl-keep-refused"})),
    ("default mode: missing config key acceptance is an error",
     default({k: v for k, v in config.items() if k != "acceptance"}) == (2, None)),
    ("default mode: missing config key brLimit is an error",
     default({k: v for k, v in config.items() if k != "brLimit"}) == (2, None)),
    ("default mode: unknown config key is an error", default({**config, "minK": 14}) == (2, None)),
]
for name, ok in checks:
    print(("ok   " if ok else "FAIL ") + name)
    fails += not ok
sys.exit(1 if fails else 0)
