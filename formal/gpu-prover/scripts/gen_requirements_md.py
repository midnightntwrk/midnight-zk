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
"""Write requirements.md from requirements.json (the JSON is authoritative).
Usage: gen_requirements_md.py [--check]"""
import json
import pathlib
import sys

root = pathlib.Path(__file__).resolve().parent.parent
d = json.loads((root / "requirements.json").read_text())
titles = {
    "build": "Build and feature", "hooks": "Hook contract", "randomness": "Randomness and transcript",
    "fallback": "CPU fallback", "admission": "Device memory and admission", "wipe": "Witness erasure",
    "readback": "Device-to-host traffic", "verify": "Verification and keys", "service": "Service",
    "reporting": "Reporting", "wsl": "WSL2 profile", "container": "Containers",
    "harness": "Test and benchmark harness",
}
out = ["# GPU prover requirements", "",
       "Generated from `requirements.json` by `scripts/gen_requirements_md.py`. The JSON is",
       "authoritative. Each statement is one EARS sentence. The verification column names the",
       "Lean oracle declaration, the Quint artifact, the golden vectors or the Rust, harness or",
       "container check that covers it. `design.md` gives the context.", "",
       "Terms: a *device phase* is an upload, MSM, NTT or quotient kernel of a",
       "request. Zeroing and freeing buffers is not a device phase. *Configured* values have",
       "documented defaults and come from an environment variable or a config file.",
       "The *resident policy* is `evict` by default: the resident proving-key copies and the MSM",
       "tables are freed before each reply and uploaded again at the next request. `keep` is an",
       "opt-in for a card with no other user; it holds the key copies between requests. The MSM",
       "device contexts are freed at the end of every request under either policy.", ""]
sec = None
for r in d["requirements"]:
    if r["section"] != sec:
        sec = r["section"]
        out += ["", f"## {titles[sec]}", "", "| ID | Requirement | Verification |", "|---|---|---|"]
    ver = "<br>".join(v.replace("|", "\\|") for v in r["verification"])
    out.append(f"| {r['id']} | {r['statement']} | {ver} |")
text = "\n".join(out) + "\n"
target = root / "requirements.md"
if "--check" in sys.argv:
    sys.exit(0 if target.read_text() == text else "requirements.md is stale")
target.write_text(text)
