#!/usr/bin/env python3
"""Summarise a verify-package.sh run, and optionally diff it against another one.

Two things are reported:

* Per package, the wall and CPU time across all repeats: median, mean, standard
  deviation and range. Verification time varies a great deal between runs on
  identical input, so a single measurement is not evidence of anything; the
  standard deviation is what says whether a difference is real.
* Per member, the time Gobra spent on it, taken from the stats.json of the first
  repeat. This is what identifies *which* member is expensive, rather than just
  which package.

Usage:
    ./tooling/verify-report.py <runDir>              # summarise
    ./tooling/verify-report.py <runDir> <baseDir>    # summarise and compare
"""

import json
import math
import os
import statistics
import sys
from collections import defaultdict

# Members below this are noise; listing them all buries the interesting ones.
MEMBER_THRESHOLD_MS = 1000
TOP_N = 30


def read_run(run_dir):
    """Return (per-package samples, per-member times in ms)."""
    packages = defaultdict(lambda: {"wall": [], "cpu": [], "errors": set(), "timeouts": 0})
    timings = os.path.join(run_dir, "timings.tsv")
    if os.path.exists(timings):
        with open(timings) as f:
            header = next(f, "").rstrip("\n").split("\t")
            has_run_column = "run" in header
            for line in f:
                parts = line.rstrip("\n").split("\t")
                if has_run_column and len(parts) == 5:
                    pkg, _run, wall, cpu, errors = parts
                elif not has_run_column and len(parts) == 4:
                    pkg, wall, cpu, errors = parts
                else:
                    continue
                packages[pkg]["wall"].append(int(wall))
                packages[pkg]["cpu"].append(int(cpu))
                packages[pkg]["errors"].add(errors)
                if errors == "timeout":
                    packages[pkg]["timeouts"] = packages[pkg].get("timeouts", 0) + 1

    members = defaultdict(int)
    for stats_path in find_stats(run_dir):
        with open(stats_path) as f:
            stats = json.load(f)
        for member in stats:
            for viper_member in member.get("viperMembers", []):
                if viper_member.get("fromImport"):
                    continue
                members[member["id"]] += viper_member.get("time", 0)

    return packages, members


def find_stats(run_dir):
    """stats.json of the first repeat of each package.

    Later repeats would double-count members, and their per-member numbers are
    not more informative than the first.
    """
    for entry in sorted(os.scandir(run_dir), key=lambda e: e.name):
        if not entry.is_dir():
            continue
        direct = os.path.join(entry.path, "stats.json")
        if os.path.exists(direct):
            yield direct
            continue
        first_run = os.path.join(entry.path, "run1", "stats.json")
        if os.path.exists(first_run):
            yield first_run


def stats_of(samples):
    if not samples:
        return None
    return {
        "n": len(samples),
        "median": statistics.median(samples),
        "mean": statistics.fmean(samples),
        "sd": statistics.stdev(samples) if len(samples) > 1 else 0.0,
        "min": min(samples),
        "max": max(samples),
    }


def fmt_delta(new, old):
    if old is None:
        return "new"
    if old == 0:
        return "+inf" if new else "0"
    return f"{100.0 * (new - old) / old:+.0f}%"


def significance(new, base):
    """Flag differences that the observed spread can explain on its own."""
    if new is None or base is None:
        return ""
    diff = abs(new["median"] - base["median"])
    # Standard error of the difference of two means.
    pooled = math.sqrt(new["sd"] ** 2 / max(new["n"], 1) + base["sd"] ** 2 / max(base["n"], 1))
    if pooled == 0:
        return "" if diff == 0 else " *"
    return " *" if diff > 2 * pooled else " (noise)"


def print_packages(packages, base_packages, compare):
    print(
        f"{'package':<10} {'n':>3} {'wall med':>9} {'sd':>7} {'range':>13} "
        f"{'cpu med':>9} {'sd':>7} {'errors':>7}"
        + (f" {'d wall':>8}" if compare else "")
    )
    width = 78 + (9 if compare else 0)
    print("-" * width)

    for pkg, samples in packages.items():
        wall = stats_of(samples["wall"])
        cpu = stats_of(samples["cpu"])
        timeouts = samples.get("timeouts", 0)
        errors = ",".join(sorted(samples["errors"]))
        if timeouts:
            errors = f"{timeouts}/{wall['n']} to"
        row = (
            f"{pkg:<10} {wall['n']:>3} {wall['median']:>8.0f}s {wall['sd']:>6.1f}s "
            f"{wall['min']:>5.0f}-{wall['max']:<6.0f}s {cpu['median']:>8.0f}s "
            f"{cpu['sd']:>6.1f}s {errors:>7}"
        )
        if compare:
            base = base_packages.get(pkg)
            base_wall = stats_of(base["wall"]) if base else None
            row += f" {fmt_delta(wall['median'], base_wall['median'] if base_wall else None):>8}"
            row += significance(wall, base_wall)
        print(row)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 1

    run_dir = sys.argv[1]
    base_dir = sys.argv[2] if len(sys.argv) > 2 else None

    packages, members = read_run(run_dir)
    base_packages, base_members = read_run(base_dir) if base_dir else ({}, {})

    print(f"run: {run_dir}")
    if base_dir:
        print(f"baseline: {base_dir}")
    extra = os.path.join(run_dir, "extra-args.txt")
    if os.path.exists(extra):
        print(open(extra).read().strip())
    print()

    print_packages(packages, base_packages, bool(base_dir))

    totals = [sum(s["wall"]) for s in packages.values()]
    print()
    print(f"sum of package medians: {sum(stats_of(s['wall'])['median'] for s in packages.values()):.0f}s wall")

    print()
    print(f"slowest members (>{MEMBER_THRESHOLD_MS} ms, top {TOP_N}, first repeat only):")
    print()
    ranked = sorted(members.items(), key=lambda kv: kv[1], reverse=True)
    shown = 0
    for member_id, ms in ranked:
        if ms < MEMBER_THRESHOLD_MS or shown >= TOP_N:
            break
        line = f"  {ms / 1000:>8.1f}s  {member_id}"
        if base_dir:
            line += f"   ({fmt_delta(ms, base_members.get(member_id))})"
        print(line)
        shown += 1

    if base_dir:
        gone = [m for m in base_members if m not in members]
        if gone:
            print()
            print(f"members in the baseline but not in this run: {len(gone)}")
            for member_id in sorted(gone)[:10]:
                print(f"  {member_id}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
