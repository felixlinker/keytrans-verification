#!/usr/bin/env python3
"""Visualize Gobra verification times from stats.json files.

Usage:
    visualize-verification.py INPUT [INPUT...] -o OUT.html [--summary OUT.md] [--title TITLE]

    INPUT       a stats.json file, or a directory searched recursively for
                files named exactly "stats.json". Duplicates (same resolved
                absolute path) are counted once. Each distinct file is ONE
                iteration/measurement of the package task(s) it contains.
    -o          write a single self-contained HTML report (inline CSS, no
                external requests; works from file:// and under a strict CSP).
    --summary   write a GitHub-flavored markdown summary (for the Actions job
                summary / a sticky PR comment). Starts with the marker
                comment <!-- verification-times --> on its own first line.
    --title     report title (default "Gobra verification times").

At least one of -o / --summary is required.

Input schema (Gobra stats.json): a JSON array of Gobra-member entries
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
    min, max). n can differ between packages when different files cover
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

Robustness: a missing/null time counts as 0; an entry with an empty or
absent viperMembers list is skipped but counted (reported in the header);
an unparseable file is a warning on stderr, not an error; duplicate
(taskName, id) pairs inside one file are merged (times summed). Exit 2 only
when no stats.json was found at all or none could be parsed.
"""

import argparse
import html as html_mod
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from statistics import median

# ---------------------------------------------------------------------------
# Palette (validated; light / dark via prefers-color-scheme). Do not add hues.
BAR_LIGHT, BAR_DARK = "#2a78d6", "#3987e5"
FAIL = "#d03b3b"
INK_LIGHT, INK_DARK = "#0b0b0b", "#ffffff"
SEC_LIGHT, SEC_DARK = "#52514e", "#c3c2b7"
MUTED = "#898781"
GRID_LIGHT, GRID_DARK = "#e1e0d9", "#2c2c2a"
SURFACE_LIGHT, SURFACE_DARK = "#fcfcfb", "#1a1a19"
PAGE_LIGHT, PAGE_DARK = "#f9f9f7", "#0d0d0d"

MD_MARKER = "<!-- verification-times -->"
MD_CHAR_BUDGET = 59000  # stay safely under the 65536 PR-comment limit


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


def parse_stats_file(path):
    """Parse one stats.json.

    Returns {"members": {(task, id): obs}, "skipped": int} or None on error.
    obs = {"name", "time", "cached", "imported", "failed"}.
    """
    try:
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        if not isinstance(data, list):
            raise ValueError("top-level JSON value is not an array")
    except Exception as exc:  # noqa: BLE001 - warn and continue per contract
        print("warning: cannot parse %s: %s" % (path, exc), file=sys.stderr)
        return None

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


def stats(values):
    return {"n": len(values), "med": median(values) if values else 0,
            "min": min(values) if values else 0, "max": max(values) if values else 0}


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


def fmt_range(st):
    return "%s – %s" % (fmt_ms(st["min"]), fmt_ms(st["max"]))


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


def esc(text):
    return html_mod.escape(str(text), quote=True)


def md_code(text):
    """Render a member/package name as an inline code span (protects *, _, <)."""
    return "`%s`" % str(text).replace("`", "'").replace("|", "\\|")


# ---------------------------------------------------------------------------
# Report model (shared by HTML and markdown renderers)

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


# ---------------------------------------------------------------------------
# HTML output

HTML_CSS = """
:root {{ color-scheme: light dark;
  --bar:{bar_l}; --fail:{fail}; --ink:{ink_l}; --sec:{sec_l}; --muted:{muted};
  --grid:{grid_l}; --surface:{surface_l}; --page:{page_l}; }}
@media (prefers-color-scheme: dark) {{
  :root {{ --bar:{bar_d}; --ink:{ink_d}; --sec:{sec_d};
    --grid:{grid_d}; --surface:{surface_d}; --page:{page_d}; }} }}
* {{ box-sizing: border-box; }}
body {{ margin:0; padding:24px; background:var(--page); color:var(--ink);
  font:14px/1.5 system-ui, -apple-system, "Segoe UI", sans-serif; }}
main {{ max-width:1000px; margin:0 auto; }}
h1 {{ font-size:20px; margin:0 0 4px; }}
h2 {{ font-size:15px; margin:0 0 12px; color:var(--ink); }}
.meta {{ color:var(--sec); font-size:12.5px; margin:0 0 20px; }}
section {{ background:var(--surface); border:1px solid var(--grid);
  border-radius:8px; padding:16px 18px; margin:0 0 18px; }}
.row {{ display:grid; grid-template-columns:minmax(200px,32%) 1fr max-content;
  gap:12px; align-items:center; padding:3px 0; }}
.row.dim {{ opacity:.55; }}
.lbl {{ font-size:12.5px; color:var(--ink); overflow:hidden;
  text-overflow:ellipsis; white-space:nowrap; }}
.lbl .in {{ color:var(--muted); }}
.track {{ position:relative; height:14px; border-left:1px solid var(--grid);
  overflow:hidden; }}
.bar {{ position:absolute; top:2px; height:10px; background:var(--bar);
  border-radius:0 4px 4px 0; }}
.bar.failed {{ background:var(--fail); }}
.whisk {{ position:absolute; top:3px; height:8px;
  border-left:1px solid var(--sec); border-right:1px solid var(--sec); }}
.whisk::after {{ content:""; position:absolute; left:0; right:0; top:50%;
  border-top:1px solid var(--sec); }}
.val {{ font-variant-numeric:tabular-nums; font-size:12.5px; color:var(--ink);
  text-align:right; min-width:64px; }}
.val .rng {{ display:block; color:var(--muted); font-size:10.5px; }}
.chip {{ display:inline-block; font-size:10px; line-height:1.6; padding:0 6px;
  margin-left:6px; border:1px solid var(--grid); border-radius:999px;
  color:var(--sec); vertical-align:1px; white-space:nowrap; }}
.chip.fail {{ border-color:var(--fail); color:var(--fail); font-weight:600; }}
.warnbanner {{ border:1px solid var(--fail); border-left-width:4px;
  border-radius:4px; padding:.6rem .8rem; margin:.9rem 0; color:var(--ink);
  background:var(--surface); }}
.chip.lead {{ margin-left:0; margin-right:6px; }}
.chip.nn {{ color:var(--muted); }}
details {{ border-top:1px solid var(--grid); padding:8px 0; }}
details:first-of-type {{ border-top:none; }}
summary {{ cursor:pointer; display:grid;
  grid-template-columns:minmax(200px,32%) 1fr max-content; gap:12px;
  align-items:center; list-style-position:outside; }}
summary .lbl {{ font-weight:600; }}
summary .lbl::before {{ content:"▸ "; color:var(--muted); }}
details[open] summary .lbl::before {{ content:"▾ "; }}
.members {{ margin-top:8px; }}
table {{ border-collapse:collapse; font-size:12px; margin-top:8px; }}
th, td {{ border:1px solid var(--grid); padding:3px 8px; text-align:right;
  font-variant-numeric:tabular-nums; }}
th {{ color:var(--sec); font-weight:600; }}
td:first-child, th:first-child {{ text-align:left;
  font-variant-numeric:normal; }}
.tblwrap {{ overflow-x:auto; }}
footer {{ color:var(--muted); font-size:11.5px; margin-top:8px; }}
""".format(
    bar_l=BAR_LIGHT, bar_d=BAR_DARK, fail=FAIL, ink_l=INK_LIGHT, ink_d=INK_DARK,
    sec_l=SEC_LIGHT, sec_d=SEC_DARK, muted=MUTED, grid_l=GRID_LIGHT,
    grid_d=GRID_DARK, surface_l=SURFACE_LIGHT, surface_d=SURFACE_DARK,
    page_l=PAGE_LIGHT, page_d=PAGE_DARK,
)


def pct(value, scale):
    if scale <= 0:
        return 0.0
    return max(0.0, min(100.0, 100.0 * value / scale))


def html_bar_row(label_html, st, scale, failed=False, chips="", dim=False,
                 tooltip=""):
    """One label + bar + whisker + value row. Bars are scaled to `scale`;
    whisker positions are clamped to the track (the tooltip and the value
    column carry the exact numbers)."""
    w = pct(st["med"], scale)
    parts = ['<div class="row%s"%s>' % (" dim" if dim else "",
             ' title="%s"' % esc(tooltip) if tooltip else "")]
    parts.append('<div class="lbl">%s%s</div>' % (label_html, chips))
    parts.append('<div class="track"><div class="bar%s" style="width:%.2f%%"></div>'
                 % (" failed" if failed else "", w))
    if st["n"] > 1 and st["max"] > st["min"]:
        lo, hi = pct(st["min"], scale), pct(st["max"], scale)
        parts.append('<div class="whisk" style="left:%.2f%%;width:%.2f%%"></div>'
                     % (lo, max(0.0, hi - lo)))
    parts.append("</div>")
    rng = ('<span class="rng">%s</span>' % esc(fmt_range(st))) if st["n"] > 1 else ""
    parts.append('<div class="val">%s%s</div></div>' % (esc(fmt_ms(st["med"])), rng))
    return "".join(parts)


def member_chips(r):
    """(lead, trail) chips. FAILED leads the label so the truncating name can
    never ellipsize it away - the critical flag must not be color-alone."""
    lead = ""
    if r["fails"]:
        label = "FAILED" if r["st"]["n"] == 1 else "FAILED %d/%d" % (r["fails"], r["st"]["n"])
        lead = '<span class="chip fail lead">✕ %s</span>' % label
    trail = ""
    if r["cached"]:
        trail += '<span class="chip">cached</span>'
    if r["imported"]:
        trail += '<span class="chip">imported</span>'
    return lead, trail


def member_tooltip(r):
    st = r["st"]
    tip = "%s · median %s" % (r["name"], fmt_ms(st["med"]))
    if st["n"] > 1:
        tip += " · min %s · max %s · n=%d" % (
            fmt_ms(st["min"]), fmt_ms(st["max"]), st["n"])
    return tip


def render_html(report, title, n_files, missing=""):
    r = report
    out = ["<!doctype html>", '<html lang="en"><head><meta charset="utf-8">',
           '<meta name="viewport" content="width=device-width, initial-scale=1">',
           "<title>%s</title>" % esc(title),
           "<style>%s</style></head><body><main>" % HTML_CSS]

    # -- Header ------------------------------------------------------------
    out.append("<h1>%s</h1>" % esc(title))
    meta = ("Generated from %d stats.json file%s · %d package%s · "
            "%d members · up to %d iteration%s per package"
            % (n_files, "s" if n_files != 1 else "", len(r["pkg_rows"]),
               "s" if len(r["pkg_rows"]) != 1 else "", r["n_members"],
               r["max_n"], "s" if r["max_n"] != 1 else ""))
    if r["skipped"]:
        meta += " · %d entries without viperMembers skipped" % r["skipped"]
    if r["failed"]:
        meta += " · %d member%s failed" % (len(r["failed"]),
                                                "s" if len(r["failed"]) != 1 else "")
    out.append('<p class="meta">%s</p>' % esc(meta))

    if missing:
        out.append(
            '<p class="warnbanner"><strong>Statistics for the %s phase are '
            'missing.</strong> This report covers the remaining phase only; '
            'the packages verified by the missing phase are absent below, '
            'not fast.</p>' % esc(missing))

    if r["max_n"] > 1:  # per-iteration package totals
        out.append('<section><h2>Per-run package totals</h2><div class="tblwrap">')
        out.append("<table><tr><th>Package</th>")
        # Columns are per-package measurement indexes ("run k" = the k-th file,
        # in natural file order, that measured this package) — not global
        # iteration ids, since a package may be absent from some files.
        for i in range(r["max_n"]):
            out.append("<th>run %d</th>" % (i + 1))
        out.append("</tr>")
        for row in r["pkg_rows"]:
            out.append("<tr><td>%s</td>" % esc(row["label"]))
            for i in range(r["max_n"]):
                cell = fmt_ms(row["iters"][i][1]) if i < len(row["iters"]) else "–"
                out.append("<td>%s</td>" % esc(cell))
            out.append("</tr>")
        out.append("</table></div></section>")

    # -- View 1: overview --------------------------------------------------
    pkg_scale = max((row["st"]["med"] for row in r["pkg_rows"]), default=0)
    out.append("<section><h2>Overview — package totals, slowest first</h2>")
    for row in r["pkg_rows"]:
        chips = '<span class="chip nn">n=%d</span>' % row["st"]["n"]
        if row["failed_members"]:
            chips += ('<span class="chip fail">✕ %d failed</span>'
                      % row["failed_members"])
        tip = "%s · median %s" % (row["label"], fmt_ms(row["st"]["med"]))
        if row["st"]["n"] > 1:
            tip += " · min %s · max %s" % (fmt_ms(row["st"]["min"]),
                                                     fmt_ms(row["st"]["max"]))
        out.append(html_bar_row(esc(row["label"]), row["st"], pkg_scale,
                                failed=bool(row["failed_members"]), chips=chips,
                                tooltip=tip))
    out.append("</section>")

    # -- View 2: per-package member details --------------------------------
    out.append("<section><h2>Members by package</h2>")
    for idx, row in enumerate(r["pkg_rows"]):
        rows = r["by_pkg"].get(row["task"], [])
        mem_scale = max((m["st"]["med"] for m in rows), default=0)
        out.append("<details%s>" % (" open" if idx == 0 else ""))
        chips = '<span class="chip nn">%d members</span>' % len(rows)
        if row["failed_members"]:
            chips += ('<span class="chip fail">✕ %d failed</span>'
                      % row["failed_members"])
        out.append('<summary><span class="lbl">%s%s</span>'
                   '<span></span><span class="val">%s</span></summary>'
                   % (esc(row["label"]), chips, esc(fmt_ms(row["st"]["med"]))))
        out.append('<div class="members">')
        for m in rows:
            lead, trail = member_chips(m)
            out.append(html_bar_row(lead + esc(m["name"]), m["st"], mem_scale,
                                    failed=bool(m["fails"]), chips=trail,
                                    dim=m["imported"], tooltip=member_tooltip(m)))
        out.append("</div></details>")
    out.append("</section>")

    # -- View 3: slowest members -------------------------------------------
    top = r["slowest"][:20]
    slow_scale = max((m["st"]["med"] for m in top), default=0)
    out.append("<section><h2>Slowest members — top %d</h2>" % len(top))
    for m in top:
        lead, trail = member_chips(m)
        label = '%s%s <span class="in">· %s</span>' % (lead, esc(m["name"]),
                                                            esc(m["pkg_label"]))
        out.append(html_bar_row(label, m["st"], slow_scale,
                                failed=bool(m["fails"]), chips=trail,
                                dim=m["imported"], tooltip=member_tooltip(m)))
    rest = r["slowest"][len(top):]
    if rest:
        meds = [m["st"]["med"] for m in rest]
        out.append('<p class="meta">… and %d more members, %s combined '
                   '(%s – %s per member).</p>'
                   % (len(rest), esc(fmt_ms(sum(meds))),
                      esc(fmt_ms(min(meds))), esc(fmt_ms(max(meds)))))
    out.append("</section>")

    out.append("<footer>Generated %s by visualize-verification.py · times "
               "are Viper verification times per Gobra member; imported members "
               "are shown dimmed and excluded from package totals.</footer>"
               % datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"))
    out.append("</main></body></html>")
    return "\n".join(out)


# ---------------------------------------------------------------------------
# Markdown output

def render_markdown(report, title, n_files, missing=""):
    r = report

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

        # With one measurement per member there is no median to take and no
        # spread to show, so the Range column would be "–" in every row.
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


# ---------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(
        prog="visualize-verification.py",
        description="Visualize Gobra verification times from stats.json files.")
    ap.add_argument("inputs", nargs="+", metavar="INPUT",
                    help="stats.json file or directory searched recursively")
    ap.add_argument("-o", "--html", metavar="OUT.html",
                    help="write self-contained HTML report")
    ap.add_argument("--summary", metavar="OUT.md",
                    help="write GitHub-flavored markdown summary")
    ap.add_argument("--title", default="Gobra verification times",
                    help="report title")
    ap.add_argument("--missing", metavar="PHASES", default="",
                    help="comma-separated phases whose statistics are absent "
                         "(e.g. \"hyper\"); rendered as a prominent warning so "
                         "a partial report is not mistaken for a complete one")
    args = ap.parse_args(argv)

    if not args.html and not args.summary:
        ap.error("at least one of -o/--html or --summary is required")

    files = find_stats_files(args.inputs)
    if not files:
        print("error: no stats.json files found under: %s"
              % ", ".join(args.inputs), file=sys.stderr)
        return 2

    parsed = []
    for f in files:
        p = parse_stats_file(f)
        if p is not None:
            parsed.append((f, p))
    if not parsed:
        print("error: none of the %d stats.json file(s) could be parsed"
              % len(files), file=sys.stderr)
        return 2

    report = build_report(aggregate(parsed))

    if args.html:
        Path(args.html).write_text(
            render_html(report, args.title, len(parsed), args.missing),
            encoding="utf-8")
        print("wrote %s" % args.html)
    if args.summary:
        Path(args.summary).write_text(
            render_markdown(report, args.title, len(parsed), args.missing),
            encoding="utf-8")
        print("wrote %s" % args.summary)
    return 0


if __name__ == "__main__":
    sys.exit(main())
