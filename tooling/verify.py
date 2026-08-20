#!/usr/bin/env python3
"""Run Gobra over this repository and record how long each phase took.

This script is the single source of truth for *how* Gobra is invoked: CI
(.github/workflows/verify.yml) calls it too, so the flags in PHASES/COMMON
below are exactly the flags that run in CI. Never duplicate them elsewhere.

Verification happens in two phases, as in CI:

    unary   --hyperMode off       over proofs and utils
    hyper   --hyperMode extended  over everything except main, proofs, utils

Usage:
    tooling/verify.py                         # both phases, once
    tooling/verify.py --phase hyper -n 3      # hyper only, three iterations
    tooling/verify.py --packages log client   # just these packages
    tooling/verify.py --timeout 3000          # cap each phase at 50 minutes
    tooling/verify.py --dry-run               # print the commands, run nothing

Output layout (all under --out, which defaults OUTSIDE the repository):

    iter<i>/<phase>/stats.json   Gobra's own statistics, written by Gobra
    iter<i>/<phase>.log          combined stdout+stderr of that invocation
    timings.tsv                  one row per (iteration, phase), see below
    summary.md                   markdown report, unless --no-summary

Gobra only writes stats.json when --gobraDirectory is passed, and it rewrites
it after every package, so even a killed run leaves the statistics of the
packages that did finish.

timings.tsv schema (tab-separated, one header line, appended across runs):

    iteration   1-based iteration number
    phase       unary | hyper
    selection   include:<pkg>,<pkg> or exclude:<pkg>,<pkg> -- the packages this
                invocation was asked to verify
    status      ok | failed | timeout
    wall_s      wall-clock seconds, one decimal
    cpu_s       child CPU seconds (user+sys) of the phase, one decimal
    exit_code   Gobra's exit code, or 124 when the phase was killed on timeout

Environment:
    GOBRA_JAR   path to gobra.jar (default /gobra/gobra.jar)
    FORCE=1     skip the pre-flight check for already-running gobra.jar JVMs

Safety: this machine froze once because a harness killed a wrapper process and
orphaned the JVM grandchild. Each phase therefore runs in its own session
(start_new_session=True), a timeout kills the whole process *group*, and the
kill is verified with pgrep before we move on -- escalating to SIGKILL if the
JVM is still there. Ctrl-C and SIGTERM (a cancelled CI job) take the group
down the same way, so no exit path leaves a JVM behind.
"""

import argparse
import os
import resource
import shlex
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# --- the Gobra invocation; CI runs exactly this ----------------------------
MODULE = "github.com/felixlinker/keytrans-verification"
JVM_ARGS = ["-Xss128m"]
COMMON = ["--recursive", "--include", ".", ".verification",
          "--checkConsistency", "--parallelizeBranches"]
# phase -> (--hyperMode value, package selector flag, packages)
PHASES = {
    "unary": ("off", "--includePackages", ["proofs", "utils"]),
    "hyper": ("extended", "--excludePackages", ["main", "proofs", "utils"]),
}
# ---------------------------------------------------------------------------

TIMEOUT_RC = 124          # conventional timeout exit code, as used by timeout(1)
KILL_GRACE_S = 10         # wait after SIGTERM before escalating to SIGKILL
SUMMARIZER = Path(__file__).resolve().parent / "summarize-verification-stats.py"


def warn(msg):
    print("warning: %s" % msg, file=sys.stderr)


def gobra_jvms():
    """Running gobra.jar processes as (pid, command), excluding this script.

    Our own command line may well contain "gobra.jar" (--jar ...), so filtering
    out our pid is not optional.
    """
    try:
        out = subprocess.run(["pgrep", "-fl", "gobra.jar"],
                             capture_output=True, text=True).stdout
    except OSError:
        return []
    found = []
    for line in out.splitlines():
        pid, _, cmd = line.strip().partition(" ")
        if pid.isdigit() and int(pid) != os.getpid():
            found.append((int(pid), cmd))
    return found


def check_no_orphans(force):
    """Refuse to measure next to another Gobra run; leaked JVMs eat this box."""
    if force:
        return
    running = gobra_jvms()
    if running:
        print("error: gobra.jar JVMs are already running:", file=sys.stderr)
        for pid, cmd in running:
            print("  %d %s" % (pid, cmd), file=sys.stderr)
        print("Two JVMs corrupt each other's timings and exhaust this machine.\n"
              "Clean them up ('pkill -f gobra.jar', verify with 'pgrep -fl "
              "gobra.jar'),\nor set FORCE=1 to skip this check.", file=sys.stderr)
        sys.exit(3)


def signal_group(proc, sig):
    try:
        os.killpg(proc.pid, sig)      # start_new_session => pgid == pid
    except (ProcessLookupError, PermissionError):
        pass


def reaped(proc, timeout):
    try:
        proc.wait(timeout=timeout)
        return True
    except subprocess.TimeoutExpired:
        return False


def kill_group(proc):
    """Take down the phase's process group and check the JVM actually died."""
    print("==> killing process group %d" % proc.pid, file=sys.stderr)
    signal_group(proc, signal.SIGTERM)
    if reaped(proc, KILL_GRACE_S) and not gobra_jvms():
        return
    warn("JVM survived SIGTERM; escalating to SIGKILL")
    signal_group(proc, signal.SIGKILL)
    reaped(proc, KILL_GRACE_S)
    left = gobra_jvms()
    if left:
        warn("gobra.jar is STILL alive after SIGKILL -- clean up manually:")
        for pid, cmd in left:
            print("  %d %s" % (pid, cmd), file=sys.stderr)


def on_terminate(_signum, _frame):
    """Handle SIGTERM like Ctrl-C.

    Without this, a `kill` (a cancelled CI job, a harness timeout) would end
    this process outright while the JVM -- deliberately in its own session --
    kept running with no parent. That is exactly how leaked Gobra JVMs once
    froze this machine.
    """
    raise KeyboardInterrupt


def selection(phase, packages):
    """(selector flag, packages) for a phase; --packages overrides the phase."""
    _, flag, pkgs = PHASES[phase]
    if packages:
        return "--includePackages", list(packages)
    return flag, pkgs


def command(jar, phase, gobra_dir, packages):
    mode = PHASES[phase][0]
    flag, pkgs = selection(phase, packages)
    return ["java", *JVM_ARGS, "-jar", str(jar),
            "--gobraDirectory", str(gobra_dir),
            "--module", MODULE,
            "--hyperMode", mode,
            *COMMON, flag, *pkgs]


def label(phase, packages):
    flag, pkgs = selection(phase, packages)
    kind = "include" if flag == "--includePackages" else "exclude"
    return "%s:%s" % (kind, ",".join(pkgs))


def run_phase(cmd, log_path, timeout):
    """Run one Gobra invocation. Returns (status, wall_s, cpu_s, exit_code)."""
    cpu0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    timed_out = False
    with open(log_path, "wb") as log:
        # Own session, so a timeout can kill java *and* everything it spawns.
        proc = subprocess.Popen(cmd, cwd=str(REPO), stdout=log,
                                stderr=subprocess.STDOUT, start_new_session=True)
        try:
            rc = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            kill_group(proc)
            rc = TIMEOUT_RC
        except BaseException:          # Ctrl-C must never orphan a JVM
            kill_group(proc)
            raise
    wall = time.monotonic() - start
    cpu1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (cpu1.ru_utime - cpu0.ru_utime) + (cpu1.ru_stime - cpu0.ru_stime)
    status = "timeout" if timed_out else ("ok" if rc == 0 else "failed")
    return status, wall, cpu, rc


def summarize(out, missing, iterations):
    """Render the markdown report. A broken summary must not fail the run."""
    if not SUMMARIZER.exists():
        warn("%s not found; skipping the summary" % SUMMARIZER)
        return
    md = out / "summary.md"
    title = "Verification times (%s, n=%d)" % (out.name, iterations)
    help_text = subprocess.run([sys.executable, str(SUMMARIZER), "--help"],
                               capture_output=True, text=True).stdout
    cmd = [sys.executable, str(SUMMARIZER), str(out)]
    if "--title" in help_text:
        cmd += ["--title", title]
    if missing and "--missing" in help_text:
        cmd += ["--missing", ",".join(missing)]
    print("\n==> %s" % shlex.join(cmd))
    if "-o" in help_text or "--out" in help_text:
        done = subprocess.run(cmd + ["-o", str(md)])
    else:                              # summarizer prints markdown to stdout
        with open(md, "w") as f:
            done = subprocess.run(cmd, stdout=f)
    if done.returncode != 0:
        warn("the summarizer failed (exit %d); the raw data is still in %s"
             % (done.returncode, out))


def parse_args(argv):
    ap = argparse.ArgumentParser(
        prog="tooling/verify.py",
        description="Run Gobra over this repository and time it.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="The Gobra flags live in this file only; CI calls this script.")
    ap.add_argument("--phase", choices=["unary", "hyper", "both"], default="both",
                    help="which verification phase to run (default: both)")
    ap.add_argument("--packages", nargs="+", metavar="P",
                    help="verify only these packages, overriding the phase's "
                         "own package selection")
    ap.add_argument("-n", "--iterations", type=int, default=1, metavar="N",
                    help="repeat the whole run N times (default: 1). "
                         "Verification times vary a lot on identical input, so "
                         "one measurement is not evidence")
    ap.add_argument("--timeout", type=float, metavar="SECONDS",
                    help="kill a phase that runs longer than this and record "
                         "it as timed out; the run continues")
    ap.add_argument("-o", "--out", metavar="DIR", type=Path,
                    help="output directory (default: a UTC-stamped directory "
                         "under $TMPDIR/keytrans-verify, outside the repo)")
    ap.add_argument("--jar", metavar="PATH", type=Path,
                    default=Path(os.environ.get("GOBRA_JAR", "/gobra/gobra.jar")),
                    help="path to gobra.jar (default: $GOBRA_JAR or "
                         "/gobra/gobra.jar)")
    ap.add_argument("--summary", action=argparse.BooleanOptionalAction,
                    default=True, help="render summary.md at the end "
                                       "(default: --summary)")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the Gobra commands and exit without running "
                         "anything")
    args = ap.parse_args(argv)

    if args.iterations < 1:
        ap.error("-n/--iterations must be at least 1")
    if args.timeout is not None and args.timeout <= 0:
        ap.error("--timeout must be positive")
    if args.out is None:
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        args.out = Path(os.environ.get("TMPDIR", "/tmp")) / "keytrans-verify" / stamp
    return args


def main(argv=None):
    args = parse_args(argv)
    # --packages selects the packages explicitly, so running both phases would
    # verify each of them twice, once per hyperMode. That is not just wasteful:
    # a file carrying its own `##(--hyperMode extended)` option fails under
    # `--hyperMode off`. Default such a run to the hyper phase, which is what CI
    # uses for every package except proofs/utils; --phase still overrides.
    if args.packages and args.phase == "both":
        phases = ["hyper"]
        print("note: --packages given without --phase; verifying in the hyper "
              "phase only (pass --phase unary to override)")
    else:
        phases = ["unary", "hyper"] if args.phase == "both" else [args.phase]
    out = args.out.expanduser().resolve()

    # Measurement data must never land in the repository.
    if out == REPO or REPO in out.parents:
        print("error: --out %s is inside the repository (%s).\n"
              "Measurement data must never be written there; pick a path "
              "outside it." % (out, REPO), file=sys.stderr)
        return 2

    if args.dry_run:
        print("out:  %s" % out)
        print("jar:  %s%s" % (args.jar,
                              "" if args.jar.is_file() else "   (does not exist)"))
        for i in range(1, args.iterations + 1):
            for phase in phases:
                cmd = command(args.jar, phase, out / ("iter%d" % i) / phase,
                              args.packages)
                print("\niter %d, %s  [%s]\n  %s"
                      % (i, phase, label(phase, args.packages), shlex.join(cmd)))
        return 0

    if not args.jar.is_file():
        print("error: gobra jar not found at %s; pass --jar or set GOBRA_JAR"
              % args.jar, file=sys.stderr)
        return 2
    out.mkdir(parents=True, exist_ok=True)

    timings = out / "timings.tsv"
    new = not timings.exists()
    force = os.environ.get("FORCE") == "1"
    print("repo: %s\njar:  %s\nout:  %s\nrun:  %s x %d, packages %s"
          % (REPO, args.jar, out, "+".join(phases), args.iterations,
             " ".join(args.packages) if args.packages else "per phase"))

    failed = False
    with open(timings, "a", buffering=1) as tsv:
        if new:
            tsv.write("iteration\tphase\tselection\tstatus\twall_s\tcpu_s\t"
                      "exit_code\n")
        for i in range(1, args.iterations + 1):
            check_no_orphans(force)
            for phase in phases:
                gobra_dir = out / ("iter%d" % i) / phase
                gobra_dir.mkdir(parents=True, exist_ok=True)
                log = out / ("iter%d" % i) / ("%s.log" % phase)
                cmd = command(args.jar, phase, gobra_dir, args.packages)
                print("\n==> iter %d/%d, phase %s (log: %s)"
                      % (i, args.iterations, phase, log))
                status, wall, cpu, rc = run_phase(cmd, log, args.timeout)
                tsv.write("%d\t%s\t%s\t%s\t%.1f\t%.1f\t%d\n"
                          % (i, phase, label(phase, args.packages), status,
                             wall, cpu, rc))
                print("==> iter %d, phase %s %s (%.0fs wall, %.0fs cpu, exit %d)"
                      % (i, phase, status.upper(), wall, cpu, rc))
                failed |= status != "ok"

    # A phase that produced no statistics at all is reported as missing, so a
    # partial report is not mistaken for a healthy one: those packages are
    # absent from it, not fast.
    if args.summary:
        missing = [p for p in PHASES
                   if not list(out.glob("iter*/%s/stats.json" % p))]
        summarize(out, missing, args.iterations)

    print("\n  timings: %s\n  summary: %s" % (timings, out / "summary.md"))
    if failed:
        print("error: at least one phase failed or timed out (see %s)" % timings,
              file=sys.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    signal.signal(signal.SIGTERM, on_terminate)
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("interrupted; the Gobra process group was killed", file=sys.stderr)
        sys.exit(130)
