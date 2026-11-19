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
"""Check that requirements.json names things that exist.

For each verification entry:
* `oracle: ...`  every Lean name (GpuSpec.x, Service.x, DataMove.x or a bare
  name with an underscore) is a declaration of some module of oracle/GpuSpec;
* `quint: ...`   every inv_*, w_* and *Test name is in the Quint files;
* `vectors: ...` every *.json path is a file under vectors/.
Usage: check_refs.py   (exit 1 with the list of stale names)"""
import json
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parent.parent
lean = "\n".join(p.read_text() for p in sorted((root / "oracle" / "GpuSpec").glob("*.lean")))
decls = set(re.findall(r"^\s*(?:private\s+)?(?:theorem|def|abbrev|structure|inductive|instance)\s+([A-Za-z_][\w.']*)",
                       lean, re.M))
short = {d.split(".")[-1] for d in decls} | decls
quint = "\n".join(p.read_text() for p in sorted((root / "quint").glob("*.qnt")))
qnames = set(re.findall(r"^[ \t]*(?:pure[ \t]+)?(?:val|run|action|def)[ \t]+([A-Za-z_]\w*)", quint, re.M))
bad = []
for r in json.loads((root / "requirements.json").read_text())["requirements"]:
    for v in r["verification"]:
        kind, _, body = v.partition(":")
        kind = kind.split()[0]
        if kind == "oracle":
            names = re.findall(r"\b(?:GpuSpec|Service|DataMove)\.[\w.']+|\b[a-z][A-Za-z0-9]*_[\w']+", body)
            for n in names:
                base = n.rstrip(".").split(".")[-1]
                if base not in short:
                    bad.append((r["id"], "oracle", n))
        elif kind == "quint":
            for n in re.findall(r"\b(?:inv|w)_\w+|\b\w+Test\b", body):
                if n not in qnames:
                    bad.append((r["id"], "quint", n))
        elif kind == "vectors":
            for n in re.findall(r"[\w/-]+\.json", body):
                if not (root / "vectors" / n).is_file():
                    bad.append((r["id"], "vectors", n))
for b in bad:
    print("stale reference: %s %s %s" % b)
sys.exit(1 if bad else 0)
