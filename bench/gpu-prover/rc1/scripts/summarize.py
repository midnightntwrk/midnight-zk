#!/usr/bin/env python3
"""Summarize the six complete rc.1 measurement sets."""

import argparse
import csv
import math
import sys
from collections import defaultdict
from pathlib import Path
from statistics import median

COUNTERS = (
    "msm_calls", "ntt_calls", "quotient_calls", "device_errors", "fallbacks",
    "h2d_copies", "h2d_bytes", "d2h_copies", "d2h_bytes", "msm_d2h_copies",
    "msm_d2h_bytes", "peak_device_bytes",
)


def summarize(cpu: Path, gpu: Path) -> None:
    samples: dict[tuple[str, str, str], list[float]] = defaultdict(list)
    sizes = set()
    threads = set()
    devices = set()
    for mode, path in (("cpu", cpu), ("gpu", gpu)):
        sets: dict[int, set[int]] = defaultdict(set)
        loads = {}
        with path.open(newline="", encoding="utf-8") as stream:
            for row in csv.DictReader(stream, delimiter="\t"):
                rep, proof = int(row["rep"]), int(row["proof"])
                group = sets[rep]
                state = "cold" if proof == 0 else "warm"
                if (row["mode"] != mode or row["state"] != state or row["k"] != "21"
                        or row["verified"] != "true" or proof < 0 or proof in group):
                    raise ValueError(f"{path}, repeat {rep}, proof {proof}: invalid row")
                load = float(row["start_load1"])
                if not 0 <= load < 2 or loads.setdefault(rep, load) != load:
                    raise ValueError(f"{path}, repeat {rep}: invalid start load")
                threads.add(int(row["threads"]))
                group.add(proof)
                for metric in ("prove_s", "verify_s", *COUNTERS):
                    value = float(row[metric]) if metric.endswith("_s") else int(row[metric])
                    if not math.isfinite(value) or value < 0:
                        raise ValueError(f"{path}: invalid {metric}")
                    samples[mode, state, metric].append(value)
                if mode == "gpu":
                    devices.add((row["gpu_model"], int(row["device_total_bytes"])))
                    calls = [int(row[key]) for key in ("msm_calls", "ntt_calls", "quotient_calls")]
                    if not any(calls):
                        raise ValueError(f"{path}, repeat {rep}, proof {proof}: no device work")
                    if not all(calls):
                        print(f"{path}, repeat {rep}, proof {proof}: missing device phase; "
                              "inspect the raw declines", file=sys.stderr)

        if set(sets) != {1, 2, 3}:
            raise ValueError(f"{path}: expected repeats 1 through 3")
        for rep, indices in sets.items():
            if len(indices) < 2 or indices != set(range(len(indices))):
                raise ValueError(f"{path}, repeat {rep}: incomplete cold/warm sequence")
            sizes.add(len(indices))

    if len(sizes) != 1 or len(threads) != 1 or min(threads) < 1:
        raise ValueError("all six sets must have the same warm count and thread count")
    if len(devices) != 1 or any(name in ("", "NA") or size <= 0 for name, size in devices):
        raise ValueError("expected one GPU model and capacity for all GPU rows")
    print("mode\tstate\tmetric\tn\tmedian\tmin\tmax")
    for (mode, state, metric), values in samples.items():
        if mode == "cpu" and metric in COUNTERS:
            continue
        digits = ".9f" if metric.endswith("_s") else ".1f"
        stats = (format(value, digits) for value in (median(values), min(values), max(values)))
        print(mode, state, metric, len(values), *stats, sep="\t")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cpu", type=Path)
    parser.add_argument("gpu", type=Path)
    args = parser.parse_args()
    try:
        summarize(args.cpu, args.gpu)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.exit(1, f"summary failed: {exc}\n")
