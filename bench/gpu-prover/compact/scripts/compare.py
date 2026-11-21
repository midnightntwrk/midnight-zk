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
"""Combines a CPU summary, a GPU summary and the stock verification of the GPU proofs.

Usage: compare.py --cpu CPU.tsv --gpu GPU.tsv --verify VERIFY.tsv --out COMBINED.tsv
                  [--exclude ID,ID] [--exclude-jobs FILE]

CPU.tsv and GPU.tsv are `compact-bench summarize` outputs of the same jobs with the same
RAYON_NUM_THREADS. VERIFY.tsv is `compact-bench verify` of the GPU proofs, run with a stock
binary against the statements of a stock run.

Comparison rule per proof:
- `bytes-equal`: the CPU proof is reproducible (one sha256 over all CPU repetitions), and every
  GPU repetition gives the same bytes as the stock proof and the CPU sha256.
- `verified`: the CPU proof is not reproducible; every GPU repetition verifies under the stock
  verifier and its public inputs equal those of the stock run.
- `FAIL`: anything else (also a reproducible proof whose GPU bytes differ).

--exclude drops whole programs. --exclude-jobs FILE names jobs (one per line, optionally
followed by a tab and a reason) whose timings are not used, for example because other processes
were busy while they ran. Their proofs are still checked by the rule above; they are written as
`# excluded:` lines and kept out of the table, the totals, the median and the p95.

Writes one row per proof to COMBINED.tsv and prints a Markdown table per k with totals.
"""
import argparse
import math
import statistics
import sys


def read_summary(path):
    rows = {}
    meta = {}
    header = None
    for line in open(path):
        line = line.rstrip("\n")
        if line.startswith("# "):
            k, _, v = line[2:].partition(": ")
            meta[k] = v
            continue
        f = line.split("\t")
        if header is None:
            header = f
            continue
        r = dict(zip(header, f))
        rows[r["job"]] = r
    return meta, rows


def p95(v):
    v = sorted(v)
    return v[max(1, math.ceil(0.95 * len(v))) - 1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cpu", required=True)
    ap.add_argument("--gpu", required=True)
    ap.add_argument("--verify", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--exclude", default="")
    ap.add_argument("--exclude-jobs")
    a = ap.parse_args()
    exclude = {x for x in a.exclude.split(",") if x}
    excluded_jobs = {}
    if a.exclude_jobs:
        with open(a.exclude_jobs) as f:
            for line in f:
                job, _, reason = line.rstrip("\n").partition("\t")
                if job:
                    excluded_jobs[job] = reason or "excluded"
    cmeta, cpu = read_summary(a.cpu)
    gmeta, gpu = read_summary(a.gpu)
    if cmeta.get("threads") != gmeta.get("threads"):
        sys.exit(f"thread counts differ: cpu {cmeta.get('threads')}, gpu {gmeta.get('threads')}")
    ver = {}
    lines = open(a.verify).read().splitlines()
    vh = lines[0].split("\t")
    for line in lines[1:]:
        r = dict(zip(vh, line.split("\t")))
        ver.setdefault(r["job"], []).append(r)

    out = []
    dropped = []
    for job, c in cpu.items():
        if c["program"] in exclude:
            continue
        g = gpu.get(job)
        v = ver.get(job, [])
        if g is None or not v:
            sys.exit(f"{job}: no GPU result or no verification")
        reproducible = not c["proof_sha256"].startswith("varies")
        ok_all = all(x["verified_server"] == "true" and x["verified_ledger"] == "true"
                     and x["statement_equal"] == "true" for x in v)
        if reproducible:
            same = all(x["proof_equal_stock"] == "true" and x["proof_sha256"] == c["proof_sha256"]
                       for x in v)
            check = "bytes-equal" if same and ok_all else "FAIL"
        else:
            check = "verified" if ok_all else "FAIL"
        cs, gs = float(c["median_s"]), float(g["median_s"])
        hits = "/".join(g.get(h, "0") for h in
                        ("hits_msm", "hits_ntt", "hits_coset", "hits_quotient", "fallbacks"))
        out.append({"program": c["program"], "job": job, "k": int(c["k"]), "cpu_s": cs,
                    "gpu_s": gs, "speedup": cs / gs, "check": check, "gpu_reps": len(v),
                    "hits": hits,
                    "hit": any(int(g.get(h, "0")) > 0 for h in
                               ("hits_msm", "hits_ntt", "hits_coset", "hits_quotient"))})
        if job in excluded_jobs:
            dropped.append((out.pop(), excluded_jobs[job]))
    missing = set(excluded_jobs) - {r["job"] for r, _ in dropped}
    if missing:
        sys.exit(f"--exclude-jobs names jobs that are not in the results: {sorted(missing)}")

    with open(a.out, "w") as f:
        for k in ("cpu_model", "gpu_model", "threads"):
            f.write(f"# {k}: {gmeta.get(k)}\n")
        f.write(f"# cpu binary: {cmeta.get('binary_sha256')} ({cmeta.get('proofs_source')})\n")
        f.write(f"# gpu binary: {gmeta.get('binary_sha256')} ({gmeta.get('proofs_source')})\n")
        f.write("# hits: device msm/ntt/coset/quotient/fallbacks, largest count of any repetition\n")
        for r, why in dropped:
            f.write(f"# excluded: {r['job']} (k={r['k']}, check {r['check']}): {why}\n")
        f.write("program\tjob\tk\tcpu_median_s\tgpu_median_s\tspeedup\tcheck\tgpu_reps_checked\thits\n")
        for r in out:
            f.write(f"{r['program']}\t{r['job']}\t{r['k']}\t{r['cpu_s']:.4f}\t{r['gpu_s']:.4f}\t"
                    f"{r['speedup']:.2f}\t{r['check']}\t{r['gpu_reps']}\t{r['hits']}\n")

    print("| k | proofs | CPU s (median) | GPU s (median) | speed-up (sum) | bytes-equal / verified / FAIL | proofs with device hits |")
    print("|---:|---:|---:|---:|---:|---|---:|")
    for k in sorted({r["k"] for r in out}):
        rs = [r for r in out if r["k"] == k]
        cs = [r["cpu_s"] for r in rs]
        gs = [r["gpu_s"] for r in rs]
        n = {c: sum(r["check"] == c for r in rs) for c in ("bytes-equal", "verified", "FAIL")}
        print(f"| {k} | {len(rs)} | {statistics.median(cs):.3f} | {statistics.median(gs):.3f} | "
              f"{sum(cs) / sum(gs):.2f} | {n['bytes-equal']} / {n['verified']} / {n['FAIL']} | "
              f"{sum(r['hit'] for r in rs)} |")
    cs = [r["cpu_s"] for r in out]
    gs = [r["gpu_s"] for r in out]
    n = {c: sum(r["check"] == c for r in out) for c in ("bytes-equal", "verified", "FAIL")}
    print(f"| all | {len(out)} | {statistics.median(cs):.3f} | {statistics.median(gs):.3f} | "
          f"{sum(cs) / sum(gs):.2f} | {n['bytes-equal']} / {n['verified']} / {n['FAIL']} | "
          f"{sum(r['hit'] for r in out)} |")
    print()
    print(f"total (sum of medians): CPU {sum(cs):.2f} s, GPU {sum(gs):.2f} s, "
          f"speed-up {sum(cs) / sum(gs):.2f}")
    print(f"median: CPU {statistics.median(cs):.4f} s, GPU {statistics.median(gs):.4f} s; "
          f"p95: CPU {p95(cs):.4f} s, GPU {p95(gs):.4f} s")
    if dropped:
        print(f"excluded: {len(dropped)} jobs (all checked: "
              f"{sum(r['check'] != 'FAIL' for r, _ in dropped)} pass)")
    if n["FAIL"] or any(r["check"] == "FAIL" for r, _ in dropped):
        sys.exit(1)


if __name__ == "__main__":
    main()
