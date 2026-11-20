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

"""Copy ITF traces and add DELTA to one integer field of the record `s` in
every state. Used as the negative control of scripts/quint_check.sh: the
replay must report DISAGREE on the copies."""
import json
import pathlib
import sys

src, dst, field, delta = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), sys.argv[3], int(sys.argv[4])
dst.mkdir(parents=True, exist_ok=True)
for f in sorted(src.glob("*.itf.json")):
    t = json.loads(f.read_text())
    for st in t["states"]:
        key = next(k for k in st if k == "s" or k.endswith("::s"))
        v = st[key][field]
        st[key][field] = {"#bigint": str(int(v["#bigint"]) + delta)}
    (dst / f.name).write_text(json.dumps(t))
