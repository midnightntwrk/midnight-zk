#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check acceptance artifacts for requirements whose inputs span builds or processes.

Each subcommand consumes measurements or files from the run under review.
See COVERAGE.md for producers, arguments and missing evidence.
"""
import argparse
import csv
import filecmp
import math
import os
import sys
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rows(path):
    with path.open() as stream:
        records = list(csv.DictReader((line for line in stream if not line.startswith("#")),
                                      delimiter="\t"))
    require(records, f"{path} has no measurement rows")
    return records


def number(row, key):
    value = float(row[key])
    require(math.isfinite(value) and value >= 0, f"invalid measurement in {key}")
    return value


def identical(args):
    for name in args.files:
        a, b = args.left / name, args.right / name
        require(a.is_file() and b.is_file() and a.stat().st_size > 0, f"missing or empty {name}")
        require(filecmp.cmp(a, b, shallow=False), f"{name} differs")


def workers(args):
    require(len(set(args.workers)) >= 2, "supply two distinct live daemon workers")
    used = set()
    seen = set()
    for item in args.workers:
        pid, threads = map(int, item.split(","))
        require(pid not in seen, "duplicate PID")
        seen.add(pid)
        tasks = list(Path(f"/proc/{pid}/task").iterdir())
        cpus = set().union(*(os.sched_getaffinity(int(t.name)) for t in tasks))
        require(0 < threads <= len(cpus), f"PID {pid} exceeds its CPU budget")
        require(cpus.isdisjoint(used), f"PID {pid} overlaps another worker")
        used.update(cpus)


def summary(args):
    for row in rows(args.file):
        require(int(row["n"]) >= 5, "fewer than five warm proofs")
        for key in ("median_s", "first_s", "ready_s", "device_peak_bytes", "host_hwm_bytes"):
            number(row, key)


def ratios(args):
    by_size = {}
    for row in rows(args.file):
        size = int(row["n"])
        group = by_size.setdefault(size, {})
        kind = row["distribution"]
        require(size > 0 and kind not in group, "invalid length or duplicate distribution")
        seconds = number(row, "device_s")
        require(seconds > 0, "no device time")
        group[kind] = (seconds, number(row, "ratio"))
    for size, group in by_size.items():
        uniform = group["uniform"][0]
        for kind in ("repeated", "90%-zero", "below-2^16"):
            seconds, ratio = group[kind]
            require(math.isclose(seconds / uniform, ratio, rel_tol=0.005),
                    f"wrong {kind}/uniform ratio at n={size}")


def kernel_order(args):
    required = set(args.kernels)
    seen = set()
    for row in rows(args.file):
        if row["event"] == "timed-set-start":
            require(required <= seen, f"missing before timing: {sorted(required - seen)}")
            return
        if row["event"] == "microbenchmark":
            require(row["cpu_equal"] == "true" and number(row, "device_s") > 0,
                    f'{row["kernel"]} lacks CPU equality or device timing')
            seen.add(row["kernel"])
    raise ValueError("no timed-set-start event")


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    checks = cli.add_subparsers(dest="check", required=True)
    cmp = checks.add_parser("identical", help="compare nonempty paired build artifacts")
    cmp.add_argument("left", type=Path)
    cmp.add_argument("right", type=Path)
    cmp.add_argument("files", nargs="+")
    cmp.set_defaults(run=identical)
    affinity = checks.add_parser("workers", help="PID,reported-Rayon-threads for each live daemon")
    affinity.add_argument("workers", nargs="+")
    affinity.set_defaults(run=workers)
    for name, run in (("summary", summary), ("msm-ratios", ratios), ("kernel-order", kernel_order)):
        cmd = checks.add_parser(name, help=f"check {name} TSV from one benchmark process")
        cmd.add_argument("file", type=Path)
        if name == "kernel-order":
            cmd.add_argument("kernels", nargs="+", help="complete required kernel inventory")
        cmd.set_defaults(run=run)
    args = cli.parse_args()
    try:
        args.run(args)
    except (OSError, KeyError, ValueError, TypeError, csv.Error) as error:
        print(f"{args.check}: {error}", file=sys.stderr)
        return 1
    print(f"{args.check}: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
