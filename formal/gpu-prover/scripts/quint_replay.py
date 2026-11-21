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

"""Replay Quint ITF traces through a Lean oracle's --step mode.

The Quint model is written from the spec and its EARS requirements; the Lean
oracle is the executable reference. Replaying the model's traces through the
oracle checks the oracle against the spec: every transition the model takes
must be the transition the oracle computes.

Protocol of the oracle's --step mode (JSON Lines on stdin/stdout):
  request  {"state": {...}, "op": <int>}
  answer   {"state": {...}}, {"refused": [CODE, ...]} or {"error": "..."}

"refused" answers a decoded line that the spec refuses, with the list of the
spec's refusal codes. "error" answers a line that does not decode.

A refusal of a state the model reached is a disagreement (exit 1): the model
and the oracle disagree on the domain. An error is a protocol failure (exit 2).
The oracle runs with LEAN_ABORT_ON_PANIC=1, so a Lean panic ends it instead of
returning a default value, and each answer must arrive within --timeout seconds.

Usage:
  quint_replay.py --oracle CMD... --traces DIR \
      --op-var lastOp --compare tokens,served,rejected \
      --const cap=3 --const rate=2 [--fill ops=0,len=0]

State fields the oracle needs but the model does not have are filled from
--const (fixed per instance) and --fill (defaults). Every normalized state is
checked against each supplied constant, including the final state.
Equal typed duplicates are valid. A changed constant is a usage error before
oracle execution and cannot be excused by a known gap. Model-only variables are
left out with --drop. Only --compare fields are
compared; values may be nested (records, tuples, sets, maps; see itf_value). Exit 0 when every transition agrees, 1 on the first disagreement,
2 on a usage or protocol error, 3 when exact known gaps are consumed.
Use --action-map action=integer instead of --op-var for MBT-only operations.
--known-gaps FILE declares exact audited divergences. Excused steps never
establish complete conformance. See references/quint-check.md for the schema.

--whole-run OPS,LEN also checks whole runs, for an oracle whose input is a
sequence of operations encoded as bits: operation i of the trace is bit i of
input OPS and the trace length is input LEN. Each trace becomes one
kink-implementation/1 request to the oracle's default mode (inputs: --const
plus OPS and LEN); the answer's cells must equal the trace's last state on the
--compare fields. This checks init, the stop condition and the input decoding,
which --step does not reach.
"""
import argparse
import hashlib
import json
import math
import os
import pathlib
import re
import select
import shutil
import subprocess
import sys
import time


def itf_value(v):
    """Decode an ITF value to plain JSON: integers, lists for tuples and lists,
    sorted lists for sets, objects for records, and objects or [key, value]
    lists for maps (objects when every key is a string or an integer)."""
    if isinstance(v, list):
        return [itf_value(x) for x in v]
    if not isinstance(v, dict):
        return v
    if "#bigint" in v:
        return int(v["#bigint"])
    if "#tup" in v:
        return [itf_value(x) for x in v["#tup"]]
    if "#set" in v:
        return sorted((itf_value(x) for x in v["#set"]), key=lambda x: json.dumps(x, sort_keys=True))
    if "#map" in v:
        pairs = [(itf_value(k), itf_value(x)) for k, x in v["#map"]]
        if all(isinstance(k, (str, int)) for k, _ in pairs):
            keys = [str(k) for k, _ in pairs]
            if len(keys) != len(set(keys)):
                raise ValueError("ITF map key collision after JSON conversion")
            return {str(k): x for k, x in pairs}
        return sorted(([k, x] for k, x in pairs), key=lambda kv: json.dumps(kv, sort_keys=True))
    if "#unserializable" in v:
        raise ValueError(f"unserializable ITF value: {v['#unserializable']}")
    return {k: itf_value(x) for k, x in v.items() if not k.startswith("#")}


def short(name):
    """Quint qualifies instance variables (`inst::module::var`); keep the last part."""
    return name.rsplit("::", 1)[-1]


def strict_json(text):
    def object_pairs(pairs):
        out = {}
        for key, value in pairs:
            if key in out:
                raise ValueError(f"duplicate JSON key: {key}")
            out[key] = value
        return out
    def invalid(value):
        raise ValueError(f"non-JSON number: {value}")
    return json.loads(text, object_pairs_hook=object_pairs, parse_constant=invalid)


# Check exact producer names before shortening. A model's m::nondetPicks is state.
MBT_METADATA = {"mbt::actionTaken", "mbt::nondetPicks"}


def normalize_state(raw, rename):
    if not isinstance(raw, dict):
        raise TypeError("ITF state must be an object")
    out = {}
    for key, value in raw.items():
        if key.startswith("#") or key in MBT_METADATA:
            continue
        name = rename.get(short(key), short(key))
        if name in out:
            raise ValueError(f"state name collision after shortening/renaming: {name}")
        out[name] = itf_value(value)
    return out


def identity(value):
    """Use JSON type identity too: true is not the integer 1."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def validate_constants(states, consts, trace_name):
    """Accept equal exported constants and reject changes before oracle execution."""
    for index, state in enumerate(states):
        for name, value in consts.items():
            if name in state and identity(state[name]) != identity(value):
                raise ValueError(f"{trace_name}: state {index}: constant {name} differs from --const")


class KnownGaps:
    def __init__(self, path):
        self.entries = strict_json(pathlib.Path(path).read_text()) if path else []
        self.used = set()
        fields = {"finding", "evidence", "trace_sha256", "step", "operation", "field", "expected", "actual"}
        if not isinstance(self.entries, list):
            raise TypeError("known gaps must be a list")
        seen = set()
        for gap in self.entries:
            if not isinstance(gap, dict) or set(gap) != fields:
                raise ValueError("known gap requires exactly " + ",".join(sorted(fields)))
            for key in ("finding", "evidence", "field"):
                if not isinstance(gap[key], str) or not gap[key].strip() or any(c in gap[key] for c in "*?[]"):
                    raise ValueError(f"known gap {key} must be an exact nonempty name/reference")
            if not re.fullmatch(r"[0-9a-f]{64}", str(gap["trace_sha256"])):
                raise ValueError("known gap trace_sha256 must be an exact SHA-256")
            if type(gap["step"]) is not int or gap["step"] < 0 or type(gap["operation"]) is not int:
                raise ValueError("known gap step and operation must be integers (step >= 0)")
            match = identity({k:v for k,v in gap.items() if k not in ("finding", "evidence")})
            if match in seen:
                raise ValueError("duplicate or ambiguous known gap")
            seen.add(match)

    def excuse(self, trace_hash, step, op, field, expected, actual):
        match = {"trace_sha256":trace_hash, "step":step, "operation":op, "field":field,
                 "expected":expected, "actual":actual}
        for index, gap in enumerate(self.entries):
            if identity(match) == identity({k:v for k,v in gap.items() if k in match}):
                if index in self.used:
                    raise ValueError("known gap matched more than once")
                self.used.add(index)
                print("EXCUSED " + identity(gap))
                return True
        return False

    def finish(self):
        if len(self.used) != len(self.entries):
            stale = [g["finding"] for i,g in enumerate(self.entries) if i not in self.used]
            raise ValueError(f"stale/unmatched known gaps: {stale}")


def pairs(spec):
    out = {}
    for item in spec or []:
        for kv in item.split(","):
            if kv:
                k, separator, v = kv.partition("=")
                k = k.strip()
                if not separator or not k or k in out:
                    raise ValueError(f"invalid or duplicate assignment: {kv}")
                out[k] = int(v)
    return out


def read_answer(stream, timeout):
    deadline = time.monotonic() + timeout
    data = b""
    while b"\n" not in data:
        remaining = deadline - time.monotonic()
        if remaining <= 0 or not select.select([stream], [], [], max(0, remaining))[0]:
            raise ValueError(f"oracle gave no complete answer within {timeout}s")
        chunk = os.read(stream.fileno(), 65536)
        if not chunk:
            raise ValueError("oracle closed its output before a complete answer")
        data += chunk
        if len(data) > 1024 * 1024:
            raise ValueError("oracle answer exceeds 1 MiB")
    line, _, trailing = data.partition(b"\n")
    if trailing.strip():
        raise ValueError("oracle emitted unsolicited extra answers")
    return strict_json(line)


def argv_json(text):
    argv = strict_json(text)
    if not isinstance(argv, list) or not argv or any(not isinstance(s, str) or not s.strip() or '\0' in s for s in argv):
        raise ValueError("command JSON must be a nonempty array of nonempty strings")
    return argv


def command_binding(argv):
    """Bind declared argv files; imports, environment and runtime dependencies remain external."""
    files = []
    for index, arg in enumerate(argv):
        path = pathlib.Path(shutil.which(arg) or arg) if index == 0 else pathlib.Path(arg)
        if path.is_file():
            files.append({"index": index, "path": str(path.absolute()),
                          "resolved_path": str(path.resolve()),
                          "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    return {"argv": argv, "files": files}


def finish_binding(binding):
    final = {}
    for name in ("projection", "oracle"):
        files = []
        for entry in binding[name]["files"]:
            arg = binding[name]["argv"][entry["index"]]
            path = pathlib.Path(shutil.which(arg) or arg) if entry["index"] == 0 else pathlib.Path(arg)
            digest = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
            files.append({"index": entry["index"], "path": str(path.absolute()),
                          "resolved_path": str(path.resolve()), "sha256": digest})
        final[name] = {"argv": binding[name]["argv"], "files": files}
    trace_files = []
    for entry in binding["traces"]:
        path = pathlib.Path(binding["trace_directory"]) / entry["name"]
        trace_files.append({**entry, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()
                            if path.is_file() else None})
    final["traces"] = trace_files
    changed = any(identity(binding[name]) != identity(final[name]) for name in ("projection", "oracle", "traces"))
    print("REPLAY_BINDING_FINAL " + identity({"protocol": "quint-replay-binding/1", "changed": changed, **final}))
    if changed:
        raise ValueError("declared projection/oracle/trace identity changed during replay")


class Census:
    def __init__(self, enabled, planned):
        self.enabled = enabled
        self.planned = planned
        self.rows = {}
        self.current = None
        self.visited = 0
        self.bounded = []
        self.failed = False

    def record(self, outcome):
        kind, op = self.current or ("process", None)
        counts = self.rows.setdefault((kind, op), dict.fromkeys(
            ("agreeing", "excused", "differing", "refused", "errored"), 0))
        counts[outcome] += 1
        if kind != "process":
            self.visited += 1
        self.current = None

    def emit(self):
        if not self.enabled:
            return
        outcomes = ("agreeing", "excused", "differing", "refused", "errored")
        totals = {key: sum(row[key] for row in self.rows.values()) for key in outcomes}
        rows = [{"kind": kind, "operation": op, **counts}
                for (kind, op), counts in sorted(self.rows.items(), key=lambda item: (item[0][0], item[0][1] or 0))]
        print("REPLAY_CENSUS " + identity({"protocol": "quint-replay-census/1", "totals": totals,
              "operations": rows, "planned": self.planned, "unvisited": self.planned - self.visited,
              "complete": not self.failed and not self.bounded and self.visited == self.planned,
              "bounded_traces": self.bounded}))


def project(argv, trace_name, trace_hash, index, cur, nxt, op, prior, compare, consts, timeout, env):
    request = {"protocol": "quint-replay-projection/1", "trace": {"name": trace_name, "sha256": trace_hash},
               "step": index, "model": {"before": cur, "after": nxt, "operation": op}, "oracle_state": prior}
    out = subprocess.run(argv, input=identity(request), capture_output=True, text=True,
                         timeout=timeout, env=env, check=False)
    if out.returncode != 0:
        raise ValueError(f"projection adapter exited {out.returncode}: {out.stderr.strip()}")
    answer = strict_json(out.stdout)
    keys = {"protocol", "operation", "expected"} | ({"initial_state"} if index == 0 else set())
    if not isinstance(answer, dict) or set(answer) != keys or answer["protocol"] != "quint-replay-projection/1":
        raise ValueError("projection answer has invalid protocol/keys (initial_state is allowed only at step 0)")
    if type(answer["operation"]) is not int:
        raise ValueError("projection operation must be an integer")
    expected = answer["expected"]
    if not isinstance(expected, dict) or set(expected) != set(compare):
        raise ValueError("projection expected must contain exactly the nonempty --compare fields")
    validate_constants([expected], consts, "projection expected")
    if index == 0:
        if not isinstance(answer["initial_state"], dict):
            raise ValueError("projection initial_state must be an object")
        validate_constants([answer["initial_state"]], consts, "projection initial_state")
        state = {**consts, **answer["initial_state"]}
    else:
        state = prior
    return state, answer["operation"], expected


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    oracle_options = ap.add_mutually_exclusive_group(required=True)
    oracle_options.add_argument("--oracle", nargs="+", help="oracle command; --step is appended")
    oracle_options.add_argument("--oracle-json", help="exact command argv as a JSON array; no shell; --step is appended")
    ap.add_argument("--projection-json", help="trusted projection adapter argv as a JSON array; see replay-adapters.md")
    ap.add_argument("--observation-field", help="compare oracle observation under this field (projection mode only)")
    ap.add_argument("--keep-going", action="store_true", help="collect operation census; errors still stop with exit 2")
    ap.add_argument("--traces", required=True, help="directory of *.itf.json files")
    ap.add_argument("--op-var", help="operation field, after shortening and renaming")
    ap.add_argument("--action-map", action="append", default=[], help="exact MBT action=integer, when no --op-var")
    ap.add_argument("--known-gaps", help="exact audited divergences JSON (exit 3 when consumed)")
    ap.add_argument("--compare", required=True)
    ap.add_argument("--const", action="append", default=[])
    ap.add_argument("--fill", action="append", default=[])
    ap.add_argument("--map", action="append", default=[], help="model=oracle field renames")
    ap.add_argument("--drop", action="append", default=[],
                    help="model-only variables not sent to the oracle (a strict oracle refuses unknown keys)")
    ap.add_argument("--whole-run", metavar="OPS,LEN", help="also replay each trace as one run (see above)")
    ap.add_argument("--timeout", type=float, default=30.0, help="seconds per oracle answer")
    a = ap.parse_args()

    a.oracle = argv_json(a.oracle_json) if a.oracle_json is not None else a.oracle
    projection = argv_json(a.projection_json) if a.projection_json is not None else None
    if projection and (a.whole_run is not None or a.known_gaps is not None or a.fill or a.map or a.drop):
        raise ValueError("--projection-json is incompatible with --whole-run, --known-gaps, --fill, --map and --drop")
    if a.whole_run is not None and not a.whole_run.strip():
        raise ValueError("--whole-run needs nonempty OPS,LEN")
    if a.known_gaps is not None and not a.known_gaps.strip():
        raise ValueError("--known-gaps needs a nonempty file path")
    if a.observation_field and not projection:
        raise ValueError("--observation-field requires --projection-json")

    consts, fill = pairs(a.const), pairs(a.fill)
    rename = dict(m.split("=", 1) for m in a.map)
    compare = [c.strip() for c in a.compare.split(",") if c.strip()]
    if not compare or len(set(compare)) != len(compare):
        raise ValueError("--compare must contain distinct nonempty fields")
    if len(rename) != len(a.map):
        raise ValueError("duplicate --map source")
    actions = pairs(a.action_map)
    if bool(a.op_var) == bool(actions):
        raise ValueError("provide exactly one of --op-var or explicit --action-map")
    if not math.isfinite(a.timeout) or a.timeout <= 0:
        raise ValueError("--timeout must be finite and positive")
    if a.observation_field is not None and (not a.observation_field.strip() or a.observation_field not in compare):
        raise ValueError("--observation-field must name a --compare field")
    gaps = KnownGaps(a.known_gaps)
    files = sorted(pathlib.Path(a.traces).glob("*.itf.json"))
    if not files:
        print(f"quint_replay: no *.itf.json under {a.traces}", file=sys.stderr)
        return 2

    traces = {}
    for f in files:
        trace_bytes = f.read_bytes()
        raw = strict_json(trace_bytes)["states"]
        if not isinstance(raw, list) or len(raw) < 2:
            raise ValueError(f"{f.name}: every trace needs at least one transition")
        states = [normalize_state(st, rename) for st in raw]
        validate_constants(states, consts, f.name)
        ops = []
        for st, original in zip(states[1:], raw[1:]):
            if a.op_var:
                if a.op_var not in st:
                    raise ValueError(f"{f.name}: no operation field {a.op_var}")
                op = st[a.op_var]
            else:
                action = original.get("mbt::actionTaken")
                if not isinstance(action, str) or action not in actions:
                    raise ValueError(f"{f.name}: MBT action {action!r} needs an explicit --action-map")
                op = actions[action]
            if type(op) is not int:
                raise ValueError("operation must be an integer")
            ops.append(op)
        if a.whole_run:
            ops_in, _, len_in = a.whole_run.partition(",")
            if not ops_in or not len_in:
                raise ValueError("--whole-run needs OPS,LEN")
            if any(op not in (0, 1) for op in ops):
                raise ValueError(f"{f.name}: whole-run operations must be a 0/1 sequence")
            generated = {ops_in: sum(op << i for i, op in enumerate(ops)), len_in: len(ops)}
            validate_constants([generated], consts, f"{f.name}: whole-run inputs")
        traces[f] = (states, ops, hashlib.sha256(trace_bytes).hexdigest())
    env = {**os.environ, "LEAN_ABORT_ON_PANIC": "1"}
    census = Census(a.keep_going, sum(len(item[1]) for item in traces.values()) + (len(files) if a.whole_run else 0))
    try:
        binding = None
        if projection:
            binding = {"protocol": "quint-replay-binding/1",
                  "projection": command_binding(projection), "oracle": command_binding(a.oracle),
                  "options": {"compare": compare, "const": consts, "op_var": a.op_var,
                              "action_map": actions, "observation_field": a.observation_field,
                              "timeout": a.timeout, "keep_going": a.keep_going},
                  "trace_directory": str(pathlib.Path(a.traces).absolute()),
                  "traces": [{"name": f.name, "sha256": traces[f][2]} for f in files]}
            print("REPLAY_BINDING " + identity(binding))
        result = replay(a, projection, compare, consts, fill, files, traces, gaps, env, census)
        if binding is not None:
            finish_binding(binding)
        return result
    except (ValueError, KeyError, TypeError, OSError, subprocess.SubprocessError):
        census.failed = True
        census.record("errored")
        raise
    finally:
        census.emit()


def replay(a, projection, compare, consts, fill, files, traces, gaps, env, census):
    proc = subprocess.Popen(a.oracle + ["--step"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, env=env)
    assert proc.stdin is not None and proc.stdout is not None
    checked = 0
    excused = 0
    disagreements = 0
    try:
        for f in files:
            states, ops, trace_hash = traces[f]
            prior = None
            for i, op in enumerate(ops):
                census.current = ("operation", op)
                cur, nxt = states[i], states[i + 1]
                if projection:
                    state, oracle_op, expected = project(projection, f.name, trace_hash, i, cur, nxt, op, prior,
                                                         compare, consts, a.timeout, env)
                else:
                    state = {**fill, **consts, **{k: v for k, v in cur.items() if k != a.op_var and k not in a.drop}}
                    oracle_op, expected = op, nxt
                proc.stdin.write(json.dumps({"state": state, "op": oracle_op}) + "\n")
                proc.stdin.flush()
                got = read_answer(proc.stdout, a.timeout)
                state_keys = {"state", "observation"} if a.observation_field else {"state"}
                if not isinstance(got, dict) or set(got) not in (state_keys, {"refused"}, {"error"}):
                    raise ValueError("oracle answer must contain exactly state, refused or error")
                if "state" in got and not isinstance(got["state"], dict):
                    raise ValueError("oracle state must be an object")
                if "refused" in got and (not isinstance(got["refused"], list) or not got["refused"] or
                                        any(not isinstance(code, str) for code in got["refused"])):
                    raise ValueError("oracle refused must be a nonempty list of codes")
                if "error" in got:
                    if not isinstance(got['error'], str):
                        raise ValueError("oracle error must be a string")
                    raise ValueError(f"oracle error at {f.name} step {i}: {got['error']}")
                if "refused" in got:
                    print(f"DISAGREE {f.name} step {i} op={op}: the oracle refuses a state the model reached: "
                          f"{'|'.join(map(str, got['refused'])) if isinstance(got['refused'], list) else got['refused']}")
                    print(f"  from state {state}")
                    disagreements += 1
                    census.record("refused")
                    if not a.keep_going:
                        return 1
                    if projection:
                        census.bounded.append({"trace": f.name, "step": i, "reason": "refused",
                                               "unvisited": len(ops) - i - 1})
                        break
                    continue
                actual = got["state"]
                if projection:
                    validate_constants([actual], consts, f"{f.name}: oracle state step {i}")
                    if any(name not in actual for name in consts):
                        raise ValueError("threaded oracle state is missing supplied constant fields")
                    prior = actual
                    if a.observation_field:
                        if a.observation_field in actual:
                            raise ValueError("observation field collides with oracle state")
                        actual = {**actual, a.observation_field: got["observation"]}
                missing = [k for k in compare if k not in expected or k not in actual]
                if missing:
                    # a misspelt or absent field would otherwise compare None with None and agree
                    raise ValueError(f"--compare field(s) {missing} missing from the trace or the oracle state")
                diff = {k: (expected[k], actual[k]) for k in compare if identity(expected[k]) != identity(actual[k])}
                remaining = {k:v for k,v in diff.items()
                             if not gaps.excuse(trace_hash, i, op, k, *v)}
                if remaining:
                    print(f"DISAGREE {f.name} step {i} op={op}: model vs oracle {remaining}")
                    print(f"  from state {state}")
                    disagreements += 1
                    census.record("differing")
                    if not a.keep_going:
                        return 1
                    continue
                if diff:
                    excused += 1
                    census.record("excused")
                else:
                    checked += 1
                    census.record("agreeing")
    finally:
        pending_error = sys.exc_info()[0] is not None
        proc.stdin.close()
        try:
            proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
            if not pending_error:
                raise ValueError("oracle did not exit normally after input closed") from None
        if proc.returncode != 0 and not pending_error:
            raise ValueError(f"oracle exited {proc.returncode} after replay")
    runs = 0
    if a.whole_run:
        ops_in, _, len_in = a.whole_run.partition(",")
        if not len_in:
            print("quint_replay: --whole-run needs OPS,LEN", file=sys.stderr)
            return 2
        for f in files:
            census.current = ("whole-run", None)
            states, seq, _ = traces[f]
            if len(seq) != len(states) - 1 or any(o not in (0, 1) for o in seq):
                print(f"quint_replay: {f.name}: {a.op_var} is not a 0/1 sequence", file=sys.stderr)
                return 2
            inputs = {**consts, ops_in: sum(o << i for i, o in enumerate(seq)), len_in: len(seq)}
            req = {"protocol": "kink-implementation/1", "program": f.name, "inputs": inputs}
            out = subprocess.run(a.oracle, input=json.dumps(req), capture_output=True, text=True, env=env, timeout=a.timeout, check=False)
            if out.returncode != 0:
                raise ValueError(f"oracle failed on whole run {f.name}: {out.stderr.strip()}")
            ans = strict_json(out.stdout)
            if not isinstance(ans, dict):
                raise TypeError("whole-run oracle answer must be an object")
            last = states[-1]
            cells = ans.get("cells", {})
            if ans.get("end") != "final" or any(k not in cells or k not in last for k in compare):
                raise ValueError(f"whole run {f.name}: answer {ans} lacks the --compare fields")
            diff = {k: (last[k], cells[k]) for k in compare if identity(last[k]) != identity(cells[k])}
            if diff:
                print(f"DISAGREE whole run {f.name} ({len(seq)} ops): model vs oracle {diff}")
                disagreements += 1
                census.record("differing")
                if not a.keep_going:
                    return 1
                continue
            runs += 1
            census.record("agreeing")
    gaps.finish()
    if disagreements:
        return 1
    if checked + excused == 0:
        print("quint_replay: no transition was checked (empty or one-state traces)", file=sys.stderr)
        return 2
    extra = f", and {runs} whole runs" if a.whole_run else ""
    print(f"quint_replay: {checked} agreeing transitions, {excused} excused transitions in {len(files)} traces{extra}; fields {','.join(compare)}")
    return 3 if excused else 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, TypeError, OSError, subprocess.SubprocessError) as err:
        print(f"quint_replay: {err}", file=sys.stderr)
        sys.exit(2)
