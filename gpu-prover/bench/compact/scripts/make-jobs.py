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
"""Writes the job list (JSON Lines) for compact-bench.

Usage: make-jobs.py --calls DIR --build DIR --out JOBS [--exclude ID,ID]

--calls DIR   holds <program>/transcripts/<label>.json, one file per scenario call, and the
              proof preimages <label>.<index>.preimage.bin next to it (see README.md, "Calls").
--build DIR   holds the full compactc build of each program: <program>/keys/<circuit>.prover,
              .verifier, <program>/zkir/<circuit>.bzkir and <program>/compiler/contract-info.json.

A call record gives, per proof-data entry: the circuit, the program whose keys prove it
(`zkir_id`; for a cross-contract call the callee's), the preimage file and the communication
commitment with its randomness. Calls with outcome other than `ok`, entries without a proof
circuit, and entries whose circuit contract-info.json marks as `proof: false` make no job.
"""
import argparse
import glob
import json
import os
import sys


def proof_circuit(build, program, circuit):
    """True when compactc's contract-info.json marks the circuit as one that needs a proof."""
    info = json.load(open(os.path.join(build, program, "compiler", "contract-info.json")))
    for c in info["circuits"]:
        if c["name"] == circuit:
            return bool(c.get("proof"))
    raise SystemExit(f"{program}: circuit {circuit} is not in contract-info.json")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--calls", required=True)
    ap.add_argument("--build", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--exclude", default="")
    a = ap.parse_args()
    exclude = {x for x in a.exclude.split(",") if x}
    calls = os.path.abspath(a.calls)
    build = os.path.abspath(a.build)
    n = 0
    missing = []
    with open(a.out, "w") as out:
        for rec_path in sorted(glob.glob(os.path.join(calls, "*", "transcripts", "*.json"))):
            if os.path.basename(rec_path).startswith("_"):
                continue
            rec = json.load(open(rec_path))
            pid = rec["id"]
            if pid in exclude or rec.get("outcome") != "ok":
                continue
            tdir = os.path.dirname(rec_path)
            for pd in rec.get("proof_data", []):
                if not pd.get("proof_circuit"):
                    continue
                kp = pd.get("zkir_id") or pid
                c = pd["circuit"]
                job = {
                    "job": f"{pid}/{rec['label']}.{pd['index']}",
                    "program": pid,
                    "circuit": c,
                    "key_program": kp,
                    "preimage": os.path.join(tdir, pd["preimage"]),
                    "prover_key": os.path.join(build, kp, "keys", c + ".prover"),
                    "verifier_key": os.path.join(build, kp, "keys", c + ".verifier"),
                    "ir": os.path.join(build, kp, "zkir", c + ".bzkir"),
                    "comm": pd.get("comm"),
                    "comm_rand": pd.get("comm_rand"),
                }
                if not proof_circuit(build, kp, c):
                    print(f"skip {job['job']}: {kp}/{c} is not a proof circuit", file=sys.stderr)
                    continue
                for f in ("preimage", "prover_key", "verifier_key", "ir"):
                    if not os.path.exists(job[f]):
                        missing.append(job[f])
                out.write(json.dumps(job) + "\n")
                n += 1
    print(f"{n} jobs -> {a.out}")
    if missing:
        print(f"{len(missing)} missing files, first: {missing[0]}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
