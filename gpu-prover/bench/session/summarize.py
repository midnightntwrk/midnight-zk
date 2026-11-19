#!/usr/bin/env python3
"""Summarize one measurement session (see run.sh) into session.json and RESULTS.md.

Usage: summarize.py SESSION_OUT
Reads SESSION_OUT/raw and writes SESSION_OUT/session.json and SESSION_OUT/RESULTS.md.
"""
import csv
import json
import re
import statistics as st
import sys
from datetime import datetime
from pathlib import Path

out = Path(sys.argv[1])
raw = out / "raw"


def rows(path):
    if not path.exists():
        return []
    with open(path) as f:
        return list(csv.DictReader(f, delimiter="\t"))


def path_summary(rs):
    """The h2h fields of one path (cpu or gpu) at one k, as the site reads them."""
    cold = [float(r["prove_s"]) for r in rs if r["state"] == "cold"]
    warm = [float(r["prove_s"]) for r in rs if r["state"] == "warm"]
    peak = [int(r["peak_device_bytes"]) for r in rs if r["peak_device_bytes"] not in ("", "0", "NA")]
    one = lambda key: sorted({r[key] for r in rs})
    s = {
        "warm_runs": len(warm),
        "warm_median_s": st.median(warm),
        "warm_min_s": min(warm),
        "warm_max_s": max(warm),
        "cold_s": cold[0] if cold else None,
        "all_verified": all(r["verified"] == "true" for r in rs),
        "verified_values": one("verified"),
        "threads": rs[0]["threads"],
        "fallbacks": one("fallbacks"),
        "device_errors": one("device_errors"),
        "peak_device_bytes": max(peak) if peak else None,
        "msm_calls": rs[-1]["msm_calls"],
        "ntt_calls": rs[-1]["ntt_calls"],
        "quotient_calls": rs[-1]["quotient_calls"],
        "gpu_model": rs[0]["gpu_model"],
        "verify_median_s": st.median(float(r["verify_s"]) for r in rs),
    }
    reasons = set()
    for r in rs:
        for d in json.loads(r["hook_declines"] or "[]"):
            if isinstance(d, list) and len(d) >= 2:
                reasons.add(str(d[1]))
    if reasons:
        s["decline_reason"] = ",".join(sorted(reasons))
    return s


# Sensors: clocks and temperatures over the timed phases.
sensors = [r for r in rows(raw / "sensors.tsv") if r.get("phase") not in ("", "gate", "prepare", None)]


def num(rs, key):
    v = []
    for r in rs:
        try:
            v.append(float(r[key]))
        except (TypeError, ValueError, KeyError):
            pass
    return v


def span(v, unit, fmt="{:.0f}"):
    if not v:
        return "not readable"
    return f"{fmt.format(min(v))} to {fmt.format(max(v))} {unit} (median {fmt.format(st.median(v))})"


box = dict(
    line.split("=", 1) for line in (raw / "box.txt").read_text().splitlines() if "=" in line
) if (raw / "box.txt").exists() else {}
gpu_line = box.get("gpu", "")
first_temp = num(rows(raw / "sensors.tsv")[:5], "cpu_temp_c")
clocks = (
    f"CPU mean core clock {span(num(sensors, 'cpu_mhz'), 'MHz')}; "
    f"GPU SM clock {span(num(sensors, 'gpu_sm_mhz'), 'MHz')}, memory clock {span(num(sensors, 'gpu_mem_mhz'), 'MHz')}"
)
temps = (
    f"CPU package {span(num(sensors, 'cpu_temp_c'), 'C', '{:.0f}')}"
    + (f", {first_temp[0]:.0f} C at the start" if first_temp else "")
    + f"; GPU {span(num(sensors, 'gpu_temp_c'), 'C', '{:.0f}')}"
)
log = (raw / "session.log").read_text() if (raw / "session.log").exists() else ""
m = re.search(r"^(\S+) gate open", log, re.M)
date = m.group(1)[:10] if m else None

h2h_cpu, h2h_gpu = rows(raw / "h2h-cpu.tsv"), rows(raw / "h2h-gpu.tsv")
h2h = []
for k in sorted({int(r["k"]) for r in h2h_cpu} & {int(r["k"]) for r in h2h_gpu}):
    c = path_summary([r for r in h2h_cpu if int(r["k"]) == k])
    g = path_summary([r for r in h2h_gpu if int(r["k"]) == k])
    h2h.append({"k": k, "cpu": c, "gpu": g, "speedup": c["warm_median_s"] / g["warm_median_s"]})


def seq_path(rs):
    if not rs:
        return None
    warm = [float(r["prove_s"]) for r in rs if r["state"] == "warm"]
    s = path_summary(rs)
    prefix = {}
    n = 1
    while n <= len(warm):
        w = warm[:n]
        prefix[str(n)] = {
            "total_s": sum(w),
            "proofs_per_s": n / sum(w),
            "median_latency_s": st.median(w),
            "max_latency_s": max(w),
        }
        n *= 4
    if str(len(warm)) not in prefix:
        prefix[str(len(warm))] = {
            "total_s": sum(warm),
            "proofs_per_s": len(warm) / sum(warm),
            "median_latency_s": st.median(warm),
            "max_latency_s": max(warm),
        }
    return {
        "warm_proofs": len(warm),
        "all_verified": s["all_verified"],
        "verified_values": s["verified_values"],
        "peak_device_bytes": s["peak_device_bytes"],
        "fallbacks": s["fallbacks"],
        "prefix": prefix,
    }


sg, sc = rows(raw / "seq-gpu.tsv"), rows(raw / "seq-cpu.tsv")
seq = {"k": int(sg[0]["k"]), "gpu": seq_path(sg), "cpu": seq_path(sc)} if sg and sc else None


def duration(text):
    """Rust Debug of a Duration: 1.5s, 850.2ms, 12µs."""
    m = re.search(r"in ([0-9.]+)(s|ms|µs|us|ns) ", text)
    if not m:
        return None
    return float(m.group(1)) * {"s": 1, "ms": 1e-3, "µs": 1e-6, "us": 1e-6, "ns": 1e-9}[m.group(2)]


def busy(path, start, end):
    """Mean GPU utilization (0 to 1) over the samples taken between start and end (epoch seconds).

    nvidia-smi's utilization.gpu is the share of its sample period in which a kernel ran."""
    u = []
    for line in path.read_text().splitlines() if path.exists() else []:
        p = [x.strip() for x in line.split(",")]
        try:
            when = datetime.strptime(p[0], "%Y/%m/%d %H:%M:%S.%f").timestamp()
            if start <= when <= end:
                u.append(float(p[1]))
        except (IndexError, ValueError):
            pass
    return (st.mean(u) / 100, len(u)) if u else (None, 0)


batch = None
if (raw / "batch.txt").exists():
    sizes = {}
    bk = None
    for line in (raw / "batch.txt").read_text().splitlines():
        mode, n, k, rc, t0, t1, text = line.split("\t", 6)
        bk = int(k)
        e = duration(text)
        v = re.search(r"(\d+)/(\d+) proofs verified", text)
        b = sizes.setdefault(n, {})
        b[f"{mode}_proofs_per_s"] = int(n) / e if e else None
        b[f"{mode}_elapsed_s"] = e
        b[f"{mode}_wall_s"] = float(t1) - float(t0)
        b[f"{mode}_verified"] = f"{v.group(1)}/{v.group(2)}" if v else None
        # The batch's own timer ends just before the process prints and exits;
        # take the samples of that interval only (process start-up excluded).
        frac, samples = busy(raw / f"batch-util-{mode}-{n}.csv", float(t1) - (e or 0) - 0.2, float(t1))
        if mode == "gpu":
            b["gpu_busy_fraction"] = frac
            b["gpu_util_samples"] = samples
        b[f"{mode}_line"] = text
    batch = {"k": bk, "sizes": sizes}

ratios = []
plan = {}
for line in (raw / "abab-plan.tsv").read_text().splitlines() if (raw / "abab-plan.tsv").exists() else []:
    p = line.split("\t")
    if p and p[0] and not p[0].startswith("#"):
        plan[p[0]] = p
for change, p in plan.items():
    rs = []
    for line in (raw / f"abab-{change}.tsv").read_text().splitlines():
        arm, pair, state, s = line.split("\t")
        if state == "warm":
            rs.append((arm, int(pair), float(s)))
    per = []
    for pair in sorted({r[1] for r in rs}):
        a = [s for arm, q, s in rs if arm == "A" and q == pair]
        b = [s for arm, q, s in rs if arm == "B" and q == pair]
        if a and b:
            per.append({"pair": pair, "a_median_s": st.median(a), "b_median_s": st.median(b), "ratio": st.median(a) / st.median(b)})
    if per:
        r = [x["ratio"] for x in per]
        ratios.append({
            "change": change, "what": p[1], "kind": p[2], "k": int(p[3]),
            "ratio": st.median(r), "min": min(r), "max": max(r), "pairs": per,
        })

tline = box.get("tree", "")
tm = re.match(r"(\S+) base=(\S+) threads=(\d+)", tline)
session = {
    "meta": {
        "source": str(Path("gpu-prover/bench/session/results")),
        "tree": tm.group(1) if tm else None,
        "base": tm.group(2) if tm else None,
        "device": (gpu_line.split(",")[0].replace("NVIDIA GeForce ", "").replace(" GPU", "").strip() or None),
        "threads": int(tm.group(3)) if tm else None,
        "date": date,
        "clocks": clocks,
        "temperatures": temps,
        "cpu": box.get("cpu"),
        "gpu": gpu_line or None,
    },
    "h2h": h2h,
    "seq": seq,
    "batch": batch,
    "ratios": ratios or None,
}
(out / "session.json").write_text(json.dumps(session, indent=2) + "\n")

# RESULTS.md: the same numbers as text.
L = [f"# Measurement session {date}", ""]
L += [f"Tree `{session['meta']['tree']}` on base `{session['meta']['base']}`. {session['meta']['gpu']}. CPU: {box.get('cpu')}. "
      f"{session['meta']['threads']} prover threads. Every proof was checked by the stock CPU verifier.", ""]
L += [f"Clocks: {clocks}.", "", f"Temperatures: {temps}.", ""]
if h2h:
    L += ["## Single proofs by size (seconds)", "",
          "| k | CPU cold | GPU cold | CPU warm median (min-max) | GPU warm median (min-max) | Warm speed-up | GPU device peak | GPU declines |",
          "|---|---|---|---|---|---|---|---|"]
    for r in h2h:
        c, g = r["cpu"], r["gpu"]
        L.append(f"| {r['k']} | {c['cold_s']:.3f} | {g['cold_s']:.3f} | {c['warm_median_s']:.3f} ({c['warm_min_s']:.3f}-{c['warm_max_s']:.3f}) | "
                 f"{g['warm_median_s']:.3f} ({g['warm_min_s']:.3f}-{g['warm_max_s']:.3f}) | {r['speedup']:.2f}x | "
                 f"{(g['peak_device_bytes'] or 0) / 1e6:.1f} MB | {','.join(g['fallbacks'])} {g.get('decline_reason', '')} |")
    L.append("")
if seq:
    L += [f"## Sequential run at k = {seq['k']}", "", "| Warm proofs | GPU proofs/s | CPU proofs/s |", "|---|---|---|"]
    for n in seq["gpu"]["prefix"]:
        if n in seq["cpu"]["prefix"]:
            L.append(f"| {n} | {seq['gpu']['prefix'][n]['proofs_per_s']:.2f} | {seq['cpu']['prefix'][n]['proofs_per_s']:.2f} |")
    L.append("")
if batch:
    L += [f"## Batch proving at k = {batch['k']}", "", "| Batch size | GPU proofs/s | CPU proofs/s | GPU busy fraction |", "|---|---|---|---|"]
    for n, b in sorted(batch["sizes"].items(), key=lambda x: int(x[0])):
        f = b.get("gpu_busy_fraction")
        L.append(f"| {n} | {b.get('gpu_proofs_per_s') or 0:.2f} | {b.get('cpu_proofs_per_s') or 0:.2f} | {f:.2f} |" if f is not None else
                 f"| {n} | {b.get('gpu_proofs_per_s') or 0:.2f} | {b.get('cpu_proofs_per_s') or 0:.2f} | NA |")
    L.append("")
if ratios:
    L += ["## Alternating comparisons", "", "Ratio = warm median without the change / warm median with it, per pair; median over pairs.", "",
          "| Change | Bench | k | Pairs | Ratio (min-max) |", "|---|---|---|---|---|"]
    for r in ratios:
        L.append(f"| {r['change']} | {r['kind']} | {r['k']} | {len(r['pairs'])} | {r['ratio']:.3f} ({r['min']:.3f}-{r['max']:.3f}) |")
    L.append("")
(out / "RESULTS.md").write_text("\n".join(L))
print(f"wrote {out / 'session.json'} and {out / 'RESULTS.md'}")
