#!/usr/bin/env python3
"""Summarise Gobra verification statistics as GitHub-flavored markdown.

Usage:
    summarize-verification-stats.py INPUT [INPUT...] [-o OUT.md]
        [--title TITLE] [--missing PHASES] [--baseline DIR]

    INPUT       a stats.json file, or a directory searched recursively for
                files named exactly "stats.json" (and "timings.tsv", see
                below). Duplicates (same resolved absolute path) are counted
                once. Each distinct stats.json is ONE iteration/measurement of
                the package task(s) it contains.
    -o          write the markdown report here (default: stdout). The report
                starts with the marker comment <!-- verification-times --> on
                its own first line; CI finds and updates the sticky PR comment
                by searching for that marker.
    --title     report title (default "Gobra verification times").
    --missing   comma-separated phases whose statistics are absent; rendered
                as a warning banner above everything else.
    --baseline  a second run directory; the report then also diffs this run
                against it (per-package and per-phase deltas with a
                significance marker).

Markdown is the only output format: the report is read in a PR comment and in
the Actions job summary, and it is capped at MD_CHAR_BUDGET characters so it
always fits GitHub's 65536-character comment limit (tables are truncated
progressively, with a hard cut as the last resort).

Input 1 -- Gobra stats.json: a JSON array of Gobra-member entries
    {id, pkgId, pkg, name, args, nodeType, trusted, abstract,
     viperMembers: [{name, taskName, time, nodeType, success, cached,
                     fromImport, hasBody, verified}, ...], ...}
viperMember.time is in MILLISECONDS. taskName identifies the package
verification task (e.g. "pkg/trees/prefix - prefix"); one file may contain
several tasks (e.g. a CI phase verifying multiple packages).

Aggregation rules:
  * Group viperMembers by taskName; a "member" is one (taskName, entry id).
  * Within one file, a member's time is the SUM of its viperMembers' times
    under that task (a Gobra member can compile to several Viper members,
    e.g. a function plus its termination proofs).
  * Across files, a member's per-file sums form its iteration sample:
    n, median, min, max.
  * Package total per file = sum of the task's NON-imported member times in
    that file; those per-file totals form the package's sample (n, median,
    min, max, sd). n can differ between packages when different files cover
    different tasks.
  * FAILED (per member, per file): any viperMember with success == false, or
    any NON-imported viperMember with hasBody == true and verified == false.
    The fromImport restriction was validated against real runs: imported
    members routinely carry hasBody=true/verified=false because their bodies
    are verified in their home task, not in the importing task - applying
    the verified/hasBody test to them would flag ~40 false failures per
    healthy file, while restricting it to fromImport=false flags exactly the
    members of runs that did not terminate (observed: success=true,
    verified=false, hasBody=true, fromImport=false, time=0).
  * cached=true members are included and flagged "cached".
  * fromImport=true members are included and flagged "imported" but EXCLUDED
    from the package total. Rationale, checked against real files: in a task
    T's stats, imported members appear under taskName T with small times
    (import processing, not verification); their real verification cost is
    accounted for in their home task where they appear with fromImport=false.
    Excluding them keeps a package's total the cost of its own members and
    avoids double counting across the tasks of one CI run. A member whose
    viperMembers mix fromImport values within one task (never observed) is
    treated as not imported (counted in the total) but still flagged.

Input 2 -- timings.tsv (optional), written by tooling/verify.py. stats.json
records neither wall-clock nor CPU time, so process-level cost comes from a
tab-separated file with a HEADER LINE, one row per (iteration, phase):

    iteration<TAB>phase<TAB>selection<TAB>status<TAB>wall_s<TAB>cpu_s<TAB>exit_code
    1<TAB>unary<TAB>include:proofs,utils<TAB>ok<TAB>41.2<TAB>150.6<TAB>0
    1<TAB>hyper<TAB>exclude:main,proofs,utils<TAB>timeout<TAB>3000.0<TAB>16800.5<TAB>124

    iteration  1-based repeat index
    phase      "unary" / "hyper", or any label the runner measured
    selection  which packages the invocation verified; recorded for the reader,
               not used here
    status     ok | failed | timeout
    wall_s     wall-clock seconds (float), REQUIRED
    cpu_s      user+sys CPU seconds (float); "" or absent if not measured
    exit_code  the process exit status (124 = killed on timeout)

Columns are located BY NAME, extra columns are ignored, and common synonyms
are accepted (iter/run/rep, package/pkg for phase, wall/cpu, rc/exit), so a
timings file from a different producer still parses. A row whose wall_s is
unparseable is skipped. status is derived from exit_code when absent.

Baseline diffing (--baseline): package medians of this run are compared with
the baseline's. Verification times vary a great deal between runs on identical
input, so a percentage on its own is not evidence: a delta is marked "*" only
when |median(new) - median(base)| exceeds twice the pooled standard error
sqrt(sd_new^2/n_new + sd_base^2/n_base), "noise" when it does not, and "?" when
neither side was repeated and there is no spread to judge it against. Run both
sides with -n >= 3 for that marker to mean anything.

Robustness: a missing/null time counts as 0; an entry with an empty or
absent viperMembers list is skipped but counted (reported in the header);
duplicate (taskName, id) pairs inside one file are merged (times summed).
An unparseable stats.json is an ERROR (exit 2): skipping it would silently
drop a phase or an iteration and understate every total that follows. Exit 2
likewise when no stats.json was found at all.
"""

import argparse
import json
import math
import re
import sys
from pathlib import Path
from statistics import median, stdev

class StatsError(Exception):
    """An input file could not be used; the report would be wrong without it."""


MD_MARKER = "<!-- verification-times -->"
MD_CHAR_BUDGET = 59000  # stay safely under the 65536 PR-comment limit
TIMINGS_NAME = "timings.tsv"

# Per-field header synonyms, first match wins. Lower-cased, whitespace-stripped.
TIMING_COLUMNS = {
    "iteration": ("iteration", "iter", "run", "rep", "repeat"),
    "phase": ("phase", "package", "pkg", "target", "side", "step"),
    "wall_s": ("wall_s", "wall", "wall_seconds", "walltime_s", "seconds"),
    "cpu_s": ("cpu_s", "cpu", "cpu_seconds", "cputime_s"),
    "status": ("status", "result", "outcome", "errors"),
    "exit_code": ("exit_code", "exit", "exitcode", "rc", "returncode"),
}
# Status/exit-code cell values that mean "nothing went wrong".
OK_TOKENS = {"", "0", "ok", "pass", "passed", "success", "succeeded", "yes",
             "none", "true", "-"}
TIMEOUT_TOKENS = {"timeout", "timedout", "timed out", "to", "killed"}


# ---------------------------------------------------------------------------
# Input discovery and parsing

def find_stats_files(inputs):
    """Resolve CLI inputs to a deduplicated, sorted list of stats.json paths."""
    seen = set()
    files = []
    for raw in inputs:
        p = Path(raw)
        if p.is_dir():
            candidates = sorted(p.rglob("stats.json"))
        elif p.is_file():
            candidates = [p]  # an explicitly named file is accepted as-is
        else:
            print("warning: input not found, skipping: %s" % raw, file=sys.stderr)
            continue
        for c in candidates:
            r = c.resolve()
            if r not in seen:
                seen.add(r)
                files.append(r)
    # Natural sort so iter2 orders before iter10; measurement columns then
    # follow chronological iteration order.
    def natkey(p):
        return [int(t) if t.isdigit() else t
                for t in re.split(r"(\d+)", str(p))]
    return sorted(files, key=natkey)


def find_timings_files(inputs):
    """Locate timings.tsv files for the same inputs.

    A directory is searched recursively (the runner writes one timings.tsv per
    run directory, next to the per-phase stats directories). When the input is
    an explicitly named stats.json, its directory and the directory above it
    are searched shallowly, so `report.py run/hyper/stats.json` still picks up
    `run/timings.tsv`.
    """
    seen = set()
    files = []
    for raw in inputs:
        p = Path(raw)
        candidates = []
        if p.is_dir():
            candidates = sorted(p.rglob(TIMINGS_NAME))
        elif p.is_file():
            if p.name == TIMINGS_NAME:
                candidates = [p]
            else:
                for d in (p.parent, p.parent.parent):
                    cand = d / TIMINGS_NAME
                    if cand.is_file():
                        candidates.append(cand)
        for c in candidates:
            r = c.resolve()
            if r not in seen:
                seen.add(r)
                files.append(r)
    return files


def parse_stats_file(path):
    """Parse one stats.json.

    Returns {"members": {(task, id): obs}, "skipped": int}.

    Raises StatsError if the file cannot be read or is not a Gobra stats
    array. Skipping it would silently drop a phase or an iteration and
    understate every total that follows, so a damaged input is fatal.
    """
    try:
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        if not isinstance(data, list):
            raise ValueError("top-level JSON value is not an array")
    except Exception as exc:  # noqa: BLE001 - re-raised as StatsError
        raise StatsError("cannot parse %s: %s" % (path, exc))

    members = {}
    skipped = 0
    for entry in data:
        if not isinstance(entry, dict):
            skipped += 1
            continue
        vms = entry.get("viperMembers")
        if not vms:
            skipped += 1  # counted, not aggregated
            continue
        ident = str(entry.get("id") or entry.get("name") or "?")
        display = (str(entry.get("name") or "") + str(entry.get("args") or "")) or ident

        by_task = {}
        for vm in vms:
            if not isinstance(vm, dict):
                continue
            by_task.setdefault(str(vm.get("taskName") or "(unknown task)"), []).append(vm)

        for task, group in by_task.items():
            time_ms = sum(vm.get("time") or 0 for vm in group)
            cached = any(vm.get("cached") for vm in group)
            imported = all(vm.get("fromImport") for vm in group)
            failed = any(vm.get("success") is False for vm in group) or any(
                (not vm.get("fromImport")) and vm.get("hasBody") and not vm.get("verified")
                for vm in group
            )
            key = (task, ident)
            if key in members:  # duplicate ids tolerated: merge
                prev = members[key]
                prev["time"] += time_ms
                prev["cached"] = prev["cached"] or cached
                prev["imported"] = prev["imported"] and imported
                prev["failed"] = prev["failed"] or failed
            else:
                members[key] = {
                    "name": display,
                    "time": time_ms,
                    "cached": cached,
                    "imported": imported,
                    "failed": failed,
                }
    return {"members": members, "skipped": skipped}


def _num(text):
    try:
        return float(text)
    except (TypeError, ValueError):
        return None


def _status_of(status_cell, exit_cell):
    """Normalise a status/exit-code pair to ok | failed | timeout."""
    s = status_cell.strip().lower()
    if s in TIMEOUT_TOKENS:
        return "timeout"
    if s and s not in OK_TOKENS:
        return "failed"
    e = exit_cell.strip()
    if e and e not in OK_TOKENS:
        # 124 is what `timeout(1)` and our runner report for a killed process.
        return "timeout" if e == "124" else "failed"
    return "ok"


def parse_timings_file(path):
    """Parse one timings.tsv into a list of row dicts (see module docstring)."""
    try:
        with open(path, "r", encoding="utf-8") as fh:
            lines = [ln.rstrip("\n") for ln in fh if ln.strip()]
    except Exception as exc:  # noqa: BLE001 - warn and continue per contract
        print("warning: cannot read %s: %s" % (path, exc), file=sys.stderr)
        return []
    if not lines:
        return []

    header = [h.strip().lower() for h in lines[0].split("\t")]
    idx = {}
    for field, aliases in TIMING_COLUMNS.items():
        for alias in aliases:
            if alias in header:
                idx[field] = header.index(alias)
                break
    if "wall_s" not in idx:
        print("warning: %s has no recognised wall-time column (header: %s)"
              % (path, ", ".join(header)), file=sys.stderr)
        return []

    rows = []
    for line in lines[1:]:
        parts = line.split("\t")

        def cell(field):
            i = idx.get(field)
            return parts[i].strip() if i is not None and i < len(parts) else ""

        wall = _num(cell("wall_s"))
        if wall is None:
            continue  # not a data row (or an unusable one)
        rows.append({
            "phase": cell("phase") or "(run)",
            "iteration": cell("iteration"),
            "wall": wall,
            "cpu": _num(cell("cpu_s")),
            "status": _status_of(cell("status"), cell("exit_code")),
        })
    return rows


# ---------------------------------------------------------------------------
# Aggregation across files

def aggregate(parsed_files):
    """Merge per-file member observations into the report model.

    parsed_files: list of (path, {"members": ..., "skipped": ...}).
    """
    members = {}   # (task, id) -> {name, times[], fails, cached, imported}
    packages = {}  # task -> {totals[], fail_files, failed_keys:set, iters:[(path,total)]}
    skipped = 0

    for path, parsed in parsed_files:
        skipped += parsed["skipped"]
        per_task_total = {}
        per_task_failed = {}
        for (task, ident), obs in parsed["members"].items():
            m = members.setdefault(
                (task, ident),
                {"name": obs["name"], "times": [], "fails": 0,
                 "cached": False, "imported": False},
            )
            m["times"].append(obs["time"])
            m["cached"] = m["cached"] or obs["cached"]
            m["imported"] = m["imported"] or obs["imported"]
            if obs["failed"]:
                m["fails"] += 1
            if not obs["imported"]:  # imported members are excluded from totals
                per_task_total[task] = per_task_total.get(task, 0) + obs["time"]
            else:
                per_task_total.setdefault(task, 0)
            if obs["failed"]:
                per_task_failed.setdefault(task, set()).add((task, ident))

        for task, total in per_task_total.items():
            pkg = packages.setdefault(
                task, {"totals": [], "fail_files": 0, "failed_keys": set(), "iters": []})
            pkg["totals"].append(total)
            pkg["iters"].append((str(path), total))
            if task in per_task_failed:
                pkg["fail_files"] += 1
                pkg["failed_keys"].update(per_task_failed[task])

    return {"members": members, "packages": packages, "skipped": skipped}


def aggregate_timings(rows):
    """Group timings rows by phase, slowest first."""
    phases = {}
    for row in rows:
        ph = phases.setdefault(
            row["phase"], {"phase": row["phase"], "wall": [], "cpu": [], "status": {}})
        ph["wall"].append(row["wall"])
        if row["cpu"] is not None:
            ph["cpu"].append(row["cpu"])
        ph["status"][row["status"]] = ph["status"].get(row["status"], 0) + 1
    for ph in phases.values():
        ph["wall_st"] = stats(ph["wall"])
        ph["cpu_st"] = stats(ph["cpu"])
    return sorted(phases.values(), key=lambda p: (-p["wall_st"]["med"], p["phase"]))


def stats(values):
    return {"n": len(values), "med": median(values) if values else 0,
            "min": min(values) if values else 0, "max": max(values) if values else 0,
            "sd": stdev(values) if len(values) > 1 else 0.0}


# ---------------------------------------------------------------------------
# Formatting helpers

def fmt_ms(ms):
    """Auto-format a millisecond value as ms / s / m."""
    ms = max(0, ms)
    if ms < 1000:
        return "%d ms" % round(ms)
    s = ms / 1000.0
    # Guards sit at the rounding granularity of each format: anything that
    # would *display* as 60.0 s (or 10.00 s) falls into the next branch.
    if s < 59.95:
        return ("%.2f s" if s < 9.995 else "%.1f s") % s
    total = int(round(s))  # whole seconds, so 659.6s -> 11m 00s, never 10m 60s
    return "%dm %02ds" % (total // 60, total % 60)


def fmt_s(seconds):
    """Same formatting for a value already expressed in seconds."""
    return fmt_ms(seconds * 1000.0)


def fmt_range(st, unit="ms"):
    f = fmt_ms if unit == "ms" else fmt_s
    return "%s – %s" % (f(st["min"]), f(st["max"]))


def short_task(task):
    """'pkg/trees/prefix - prefix' -> 'pkg/trees/prefix'."""
    return task.split(" - ")[0] if " - " in task else task


def block_bar(value, scale, cells=20):
    """Unicode block bar of at most `cells` cells, scaled to `scale`."""
    if scale <= 0 or value <= 0:
        return ""
    eighths = "▏▎▍▌▋▊▉█"  # 1/8 .. 8/8
    frac = min(value / scale, 1.0) * cells
    full = int(frac)
    bar = "█" * full
    rem = int(round((frac - full) * 8))
    if rem > 0 and full < cells:
        bar += eighths[rem - 1]
    return bar or eighths[0]


def md_code(text):
    """Render a member/package name as an inline code span (protects *, _, <)."""
    return "`%s`" % str(text).replace("`", "'").replace("|", "\\|")


def fmt_delta(new, old):
    """Percentage change of `new` against `old` (both same unit)."""
    if old is None or new is None:
        return "new" if old is None else "gone"
    if old == 0:
        return "+inf" if new else "0%"
    return "%+.0f%%" % (100.0 * (new - old) / old)


def significance(new, base):
    """Flag differences that the observed spread can explain on its own.

    Returns "*" for a difference larger than twice the pooled standard error of
    the two medians, "noise" otherwise, "?" when neither side was repeated (a
    single run per side has no spread to judge a difference against, and
    verification times move by tens of percent on identical input), and "" when
    either side is missing.
    """
    if new is None or base is None:
        return ""
    diff = abs(new["med"] - base["med"])
    pooled = math.sqrt(new["sd"] ** 2 / max(new["n"], 1)
                       + base["sd"] ** 2 / max(base["n"], 1))
    if pooled == 0:
        if new["n"] < 2 and base["n"] < 2:
            return "?"  # one measurement per side: nothing to compare against
        # Repeated and perfectly reproducible: the difference is as real as
        # this data can say.
        return "" if diff == 0 else "*"
    return "*" if diff > 2 * pooled else "noise"


# ---------------------------------------------------------------------------
# Report model

def build_report(model):
    pkg_rows = []
    for task, pkg in model["packages"].items():
        st = stats(pkg["totals"])
        pkg_rows.append({
            "task": task, "label": short_task(task), "st": st,
            "fail_files": pkg["fail_files"],
            "failed_members": len(pkg["failed_keys"]),
            "iters": pkg["iters"],
        })
    pkg_rows.sort(key=lambda r: (-r["st"]["med"], r["label"]))

    mem_rows = []
    for (task, ident), m in model["members"].items():
        st = stats(m["times"])
        mem_rows.append({
            "task": task, "pkg_label": short_task(task), "id": ident,
            "name": m["name"], "st": st, "fails": m["fails"],
            "cached": m["cached"], "imported": m["imported"],
        })

    by_pkg = {}
    for r in mem_rows:
        by_pkg.setdefault(r["task"], []).append(r)
    for rows in by_pkg.values():
        rows.sort(key=lambda r: (0 if r["fails"] else 1, -r["st"]["med"], r["name"]))

    slowest = sorted(mem_rows, key=lambda r: (-r["st"]["med"], r["name"]))
    failed = sorted((r for r in mem_rows if r["fails"]),
                    key=lambda r: (-r["fails"], r["pkg_label"], r["name"]))
    return {
        "pkg_rows": pkg_rows, "by_pkg": by_pkg, "slowest": slowest,
        "failed": failed, "n_members": len(mem_rows),
        "max_n": max((r["st"]["n"] for r in pkg_rows), default=0),
        "skipped": model["skipped"],
    }


def load_run(inputs, label):
    """Read one run: stats.json files plus an optional timings.tsv.

    Returns {"label", "report" (or None), "n_files", "timings"}.
    """
    parsed = [(f, parse_stats_file(f)) for f in find_stats_files(inputs)]
    rows = []
    for f in find_timings_files(inputs):
        rows.extend(parse_timings_file(f))
    return {
        "label": label,
        "report": build_report(aggregate(parsed)) if parsed else None,
        "n_files": len(parsed),
        "timings": aggregate_timings(rows),
    }


# ---------------------------------------------------------------------------
# Markdown output

def render_markdown(report, title, n_files, missing="", timings=None,
                    baseline=None):
    r = report
    timings = timings or []

    def assemble(failed_limit, slowest_limit, pkg_limit):
        lines = [MD_MARKER, "", "# %s" % title, ""]
        if missing:
            # Placed before everything else: a report missing a phase lists
            # only the packages of the phases that ran, which otherwise looks
            # like a fast, healthy verification.
            lines.append("> [!WARNING]")
            lines.append("> Statistics for the **%s** phase are missing, so "
                         "this report covers the remaining phase only. The "
                         "packages verified by the missing phase are absent "
                         "below, not fast." % missing)
            lines.append("")
        lines.append("_%d stats.json file%s · %d package%s · %d members "
                     "· up to %d iteration%s per package%s_"
                     % (n_files, "s" if n_files != 1 else "", len(r["pkg_rows"]),
                        "s" if len(r["pkg_rows"]) != 1 else "", r["n_members"],
                        r["max_n"], "s" if r["max_n"] != 1 else "",
                        (" · %d entries without viperMembers skipped"
                         % r["skipped"]) if r["skipped"] else ""))
        lines.append("")

        # With a single measurement per member there is nothing to take a
        # median of and no spread to report, so the Range column would be "–"
        # in every row. Drop it and call the remaining column what it is.
        multi = r["max_n"] > 1
        time_hdr = "Median" if multi else "Time"

        if r["failed"]:
            lines.append("## ✕ Failed members")
            lines.append("")
            lines.append("| Member | Package | Failures | %s |" % time_hdr)
            lines.append("| --- | --- | ---: | ---: |")
            for m in r["failed"][:failed_limit]:
                lines.append("| %s | %s | %d/%d | %s |"
                             % (md_code(m["name"]), md_code(m["pkg_label"]),
                                m["fails"], m["st"]["n"], fmt_ms(m["st"]["med"])))
            if len(r["failed"]) > failed_limit:
                lines.append("| … and %d more | | | |"
                             % (len(r["failed"]) - failed_limit))
            lines.append("")

        lines.extend(timings_section(timings))

        pkg_scale = max((row["st"]["med"] for row in r["pkg_rows"]), default=0)
        lines.append("## Package totals")
        lines.append("")
        if multi:
            lines.append("| Package | n | %s | Range | Failures | Bar |" % time_hdr)
            lines.append("| --- | ---: | ---: | ---: | ---: | :-- |")
        else:
            lines.append("| Package | %s | Failures | Bar |" % time_hdr)
            lines.append("| --- | ---: | ---: | :-- |")
        for row in r["pkg_rows"][:pkg_limit]:
            fails = ("%d/%d" % (row["fail_files"], row["st"]["n"])
                     if row["fail_files"] else "–")
            bar = block_bar(row["st"]["med"], pkg_scale)
            if multi:
                rng = fmt_range(row["st"]) if row["st"]["n"] > 1 else "–"
                lines.append("| %s | %d | %s | %s | %s | %s |"
                             % (md_code(row["label"]), row["st"]["n"],
                                fmt_ms(row["st"]["med"]), rng, fails, bar))
            else:
                lines.append("| %s | %s | %s | %s |"
                             % (md_code(row["label"]),
                                fmt_ms(row["st"]["med"]), fails, bar))
        if len(r["pkg_rows"]) > pkg_limit:
            lines.append("| … and %d more |%s"
                         % (len(r["pkg_rows"]) - pkg_limit,
                            " | | | | |" if multi else " | | |"))
        lines.append("")

        lines.extend(baseline_section(r, timings, baseline, pkg_limit))

        lines.append("## Slowest members")
        lines.append("")
        if multi:
            lines.append("| Member | Package | %s | Range |" % time_hdr)
            lines.append("| --- | --- | ---: | ---: |")
        else:
            lines.append("| Member | Package | %s |" % time_hdr)
            lines.append("| --- | --- | ---: |")
        shown = r["slowest"][:slowest_limit]
        for m in shown:
            if multi:
                rng = fmt_range(m["st"]) if m["st"]["n"] > 1 else "–"
                lines.append("| %s | %s | %s | %s |"
                             % (md_code(m["name"]), md_code(m["pkg_label"]),
                                fmt_ms(m["st"]["med"]), rng))
            else:
                lines.append("| %s | %s | %s |"
                             % (md_code(m["name"]), md_code(m["pkg_label"]),
                                fmt_ms(m["st"]["med"])))
        rest = r["slowest"][len(shown):]
        if rest:
            # Summarise the truncated tail rather than just counting it: the
            # combined time answers "is anything meaningful hiding down here?".
            total = sum(m["st"]["med"] for m in rest)
            lo = sum(m["st"]["min"] for m in rest)
            hi = sum(m["st"]["max"] for m in rest)
            if multi:
                rng = "–" if lo == hi else "%s – %s" % (fmt_ms(lo), fmt_ms(hi))
                lines.append("| … and %d more | – | %s combined | %s |"
                             % (len(rest), fmt_ms(total), rng))
            else:
                lines.append("| … and %d more | – | %s combined |"
                             % (len(rest), fmt_ms(total)))
        lines.append("")
        return "\n".join(lines)

    failed_limit, slowest_limit = len(r["failed"]), 15
    pkg_limit = len(r["pkg_rows"])
    md = assemble(failed_limit, slowest_limit, pkg_limit)
    while len(md) > MD_CHAR_BUDGET and (
            failed_limit > 5 or pkg_limit > 10 or slowest_limit > 5):
        if failed_limit > 5:
            failed_limit = max(5, failed_limit // 2)
        elif pkg_limit > 10:
            pkg_limit = max(10, pkg_limit // 2)
        else:
            slowest_limit = max(5, slowest_limit - 5)
        md = assemble(failed_limit, slowest_limit, pkg_limit)
    if len(md) > MD_CHAR_BUDGET:
        # Hard cap: cut at a line boundary so the tables stay well-formed
        # enough to render, and say so.
        cut = md.rfind("\n", 0, MD_CHAR_BUDGET - 80)
        md = md[:cut] + "\n\n_… output truncated to fit the comment size limit._\n"
    return md


def status_cell(counts, n):
    """'ok', or the non-ok outcomes with their share of the runs."""
    bad = sorted(((k, v) for k, v in counts.items() if k != "ok"),
                 key=lambda kv: -kv[1])
    if not bad:
        return "ok"
    return ", ".join("%d/%d %s" % (v, n, k) for k, v in bad)


def timings_section(timings):
    """Process-level wall/CPU time per phase; empty when no timings.tsv."""
    if not timings:
        return []
    has_cpu = any(ph["cpu_st"]["n"] for ph in timings)
    lines = ["## Phase timings", "",
             "| Phase | n | Wall median | Wall range | CPU median | Parallelism | Status |",
             "| --- | ---: | ---: | ---: | ---: | ---: | :-- |"]
    for ph in timings:
        w, c = ph["wall_st"], ph["cpu_st"]
        par = ("%.1f×" % (c["med"] / w["med"])) if c["n"] and w["med"] else "–"
        lines.append("| %s | %d | %s | %s | %s | %s | %s |"
                     % (md_code(ph["phase"]), w["n"], fmt_s(w["med"]),
                        fmt_range(w, "s") if w["n"] > 1 else "–",
                        fmt_s(c["med"]) if c["n"] else "–", par,
                        status_cell(ph["status"], w["n"])))
    total = sum(ph["wall_st"]["med"] for ph in timings)
    note = ("_Wall-clock and CPU time of the Gobra process itself, from "
            "timings.tsv; the package times below are Viper verification times "
            "and exclude parsing, type-checking and encoding. Sum of phase "
            "wall medians: %s._" % fmt_s(total))
    if not has_cpu:
        note = note.replace("Wall-clock and CPU time", "Wall-clock time")
    lines.extend(["", note, ""])
    return lines


def baseline_section(r, timings, baseline, pkg_limit):
    """Per-package (and per-phase) deltas against a baseline run."""
    if not baseline:
        return []
    base_report = baseline.get("report")
    base_timings = baseline.get("timings") or []
    if base_report is None and not base_timings:
        return []

    lines = ["## Baseline comparison", "",
             "_Baseline: %s%s._" % (md_code(baseline["label"]),
                                    (" · %d stats.json file%s"
                                     % (baseline["n_files"],
                                        "s" if baseline["n_files"] != 1 else ""))
                                    if baseline["n_files"] else "")]
    lines.append("")
    lines.append("_Δ compares medians. `*` marks a change larger than twice the "
                 "pooled standard error of the two medians, `noise` one that "
                 "run-to-run spread explains on its own, and `?` a comparison "
                 "of single runs, which has no spread to judge it by (re-run "
                 "both sides with -n 3 or more)._")
    lines.append("")

    if timings and base_timings:
        base_ph = {ph["phase"]: ph for ph in base_timings}
        lines.append("**Wall clock, per phase**")
        lines.append("")
        lines.append("| Phase | Baseline | This run | Δ | Signif. |")
        lines.append("| --- | ---: | ---: | ---: | :-- |")
        for ph in timings:
            base = base_ph.get(ph["phase"])
            base_st = base["wall_st"] if base else None
            lines.append(
                "| %s | %s | %s | %s | %s |"
                % (md_code(ph["phase"]),
                   ("%s (n=%d)" % (fmt_s(base_st["med"]), base_st["n"]))
                   if base_st else "–",
                   "%s (n=%d)" % (fmt_s(ph["wall_st"]["med"]), ph["wall_st"]["n"]),
                   fmt_delta(ph["wall_st"]["med"],
                             base_st["med"] if base_st else None),
                   significance(ph["wall_st"], base_st) or "–"))
        lines.append("")

    if base_report is not None:
        base_pkgs = {row["task"]: row for row in base_report["pkg_rows"]}
        lines.append("**Viper verification time, per package**")
        lines.append("")
        lines.append("| Package | Baseline | This run | Δ | Signif. |")
        lines.append("| --- | ---: | ---: | ---: | :-- |")
        for row in r["pkg_rows"][:pkg_limit]:
            base = base_pkgs.get(row["task"])
            base_st = base["st"] if base else None
            lines.append(
                "| %s | %s | %s | %s | %s |"
                % (md_code(row["label"]),
                   ("%s (n=%d)" % (fmt_ms(base_st["med"]), base_st["n"]))
                   if base_st else "–",
                   "%s (n=%d)" % (fmt_ms(row["st"]["med"]), row["st"]["n"]),
                   fmt_delta(row["st"]["med"], base_st["med"] if base_st else None),
                   significance(row["st"], base_st) or "–"))
        if len(r["pkg_rows"]) > pkg_limit:
            lines.append("| … and %d more | | | | |"
                         % (len(r["pkg_rows"]) - pkg_limit))
        lines.append("")

        now_total = sum(row["st"]["med"] for row in r["pkg_rows"])
        base_total = sum(row["st"]["med"] for row in base_report["pkg_rows"])
        lines.append("_Sum of package medians: %s → %s (%s)._"
                     % (fmt_ms(base_total), fmt_ms(now_total),
                        fmt_delta(now_total, base_total)))
        lines.append("")

        gone = [row for row in base_report["pkg_rows"]
                if row["task"] not in {x["task"] for x in r["pkg_rows"]}]
        if gone:
            lines.append("_In the baseline but not in this run: %s._"
                         % ", ".join(md_code(g["label"]) for g in gone[:10]))
            lines.append("")

        lines.extend(member_movers(r, base_report))
    return lines


def member_movers(r, base_report, limit=10, floor_ms=500):
    """The members whose median moved most, largest absolute change first."""
    base_members = {(m["task"], m["id"]): m for m in base_report["slowest"]}
    moved = []
    for m in r["slowest"]:
        base = base_members.get((m["task"], m["id"]))
        if base is None or m["imported"]:
            continue
        diff = m["st"]["med"] - base["st"]["med"]
        if abs(diff) >= floor_ms:
            moved.append((abs(diff), diff, m, base))
    if not moved:
        return []
    moved.sort(key=lambda t: -t[0])
    lines = ["<details><summary>Largest per-member changes</summary>", "",
             "| Member | Package | Baseline | This run | Δ | Signif. |",
             "| --- | --- | ---: | ---: | ---: | :-- |"]
    for _, diff, m, base in moved[:limit]:
        lines.append("| %s | %s | %s | %s | %s | %s |"
                     % (md_code(m["name"]), md_code(m["pkg_label"]),
                        fmt_ms(base["st"]["med"]), fmt_ms(m["st"]["med"]),
                        fmt_delta(m["st"]["med"], base["st"]["med"]),
                        significance(m["st"], base["st"]) or "–"))
    if len(moved) > limit:
        lines.append("| … and %d more | | | | | |" % (len(moved) - limit))
    lines.extend(["", "</details>", ""])
    return lines


# ---------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(
        prog="summarize-verification-stats.py",
        description="Summarise Gobra verification statistics as markdown.")
    ap.add_argument("inputs", nargs="+", metavar="INPUT",
                    help="stats.json file or directory searched recursively "
                         "(timings.tsv is picked up alongside it)")
    ap.add_argument("-o", "--out", "--summary", metavar="OUT.md", default=None,
                    help="write the markdown report here (default: stdout)")
    ap.add_argument("--title", default="Gobra verification times",
                    help="report title")
    ap.add_argument("--missing", metavar="PHASES", default="",
                    help="comma-separated phases whose statistics are absent "
                         "(e.g. \"hyper\"); rendered as a prominent warning so "
                         "a partial report is not mistaken for a complete one")
    ap.add_argument("--baseline", metavar="DIR", default=None,
                    help="a previous run directory to diff against; adds "
                         "per-package and per-phase deltas with a "
                         "significance marker")
    args = ap.parse_args(argv)

    try:
        run = load_run(args.inputs, ", ".join(args.inputs))
        baseline = (load_run([args.baseline], args.baseline)
                    if args.baseline else None)
    except StatsError as exc:
        print("error: %s" % exc, file=sys.stderr)
        return 2
    if run["report"] is None:
        print("error: no parsable stats.json found under: %s"
              % ", ".join(args.inputs), file=sys.stderr)
        return 2

    if baseline is not None and baseline["report"] is None \
            and not baseline["timings"]:
        print("warning: baseline %s has no stats.json and no timings.tsv; "
              "no comparison is shown" % args.baseline, file=sys.stderr)
        baseline = None

    md = render_markdown(run["report"], args.title, run["n_files"],
                         args.missing, run["timings"], baseline)

    if args.out:
        out = Path(args.out)
        if out.is_dir():  # tolerate being handed a run directory
            out = out / "summary.md"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(md, encoding="utf-8")
        print("wrote %s (%d characters)" % (out, len(md)))
    else:
        sys.stdout.write(md if md.endswith("\n") else md + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
