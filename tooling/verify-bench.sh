#!/usr/bin/env bash
# verify-bench.sh -- run the CI Gobra verification locally N times and time it.
#
# Mirrors the two verification invocations of the verify-packages job in
# .github/workflows/verify.yml: an "unary" phase (--hyperMode off) and a
# "hyper" phase (--hyperMode extended). Keep the flags below in sync with
# that file.
#
# Usage: tooling/verify-bench.sh [-n N] [-o OUTDIR] [-t TAG] [-T SECONDS]
#   -n N        number of iterations (default 1)
#   -o OUTDIR   output directory; the default is deliberately OUTSIDE the
#               repository: ${TMPDIR:-/tmp}/keytrans-verify-bench/<TAG or UTC
#               timestamp>. Benchmark data must never be committed; if you
#               point -o inside the repo you get a warning but are obeyed.
#   -t TAG      label for this run (used in the default outdir and the report
#               title; defaults to a UTC timestamp)
#   -T SECONDS  per-phase timeout; on expiry the whole Gobra process tree is
#               killed (see "Safety" below)
#
# Environment:
#   GOBRA_JAR   path to gobra.jar (default: /gobra/gobra.jar)
#   FORCE=1     skip the pre-flight check for already-running gobra.jar JVMs
#
# Outputs (all under OUTDIR):
#   iter<i>/<phase>.log        combined stdout+stderr of each phase
#   iter<i>/<phase>/stats.json Gobra statistics (written by Gobra itself)
#   timings.tsv                iter, phase, wall seconds, exit code
#   report.html, summary.md    rendered by tooling/visualize-verification.py
#
# Safety: this machine froze on 2026-08-13 because a benchmark harness leaked
# orphaned JVMs (it pkill'ed a wrapper and orphaned the JVM grandchild).
# Therefore:
#   (a) before each iteration we abort if pgrep -f gobra.jar finds anything
#       (FORCE=1 overrides);
#   (b) the phase runs as its own process group (set -m), a timeout kills the
#       group with `kill -- -PGID`, then VERIFIES via pgrep -f gobra.jar that
#       the JVM actually died, escalating to `kill -9 -- -PGID` if not;
#   (c) INT/TERM/EXIT traps kill any still-running phase group, so Ctrl-C
#       never orphans a JVM.
#
# Requires only bash 3.2 (macOS default): no associative arrays, no ${var,,},
# no mapfile.

set -u

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd -P)
REPO_ROOT=$(cd "$SCRIPT_DIR/.." && pwd -P)

usage() {
  echo "Usage: tooling/verify-bench.sh [-n N] [-o OUTDIR] [-t TAG] [-T SECONDS]" >&2
  echo "  -n N        iterations (default 1)" >&2
  echo "  -o OUTDIR   output dir (default: \${TMPDIR:-/tmp}/keytrans-verify-bench/<TAG or UTC timestamp>)" >&2
  echo "  -t TAG      run label (default: UTC timestamp)" >&2
  echo "  -T SECONDS  per-phase timeout; kills the whole Gobra process tree" >&2
  echo "  env: GOBRA_JAR (default /gobra/gobra.jar), FORCE=1 skips orphan check" >&2
  exit 2
}

is_pos_int() {
  case "$1" in
    ''|*[!0-9]*) return 1 ;;
    0) return 1 ;;
    *) return 0 ;;
  esac
}

N=1
OUTDIR=""
TAG=""
TIMEOUT_S=""

while getopts "n:o:t:T:h" opt; do
  case "$opt" in
    n) N=$OPTARG ;;
    o) OUTDIR=$OPTARG ;;
    t) TAG=$OPTARG ;;
    T) TIMEOUT_S=$OPTARG ;;
    h|*) usage ;;
  esac
done
shift $((OPTIND - 1))
if [ $# -ne 0 ]; then
  echo "error: unexpected extra arguments: $*" >&2
  usage
fi

if ! is_pos_int "$N"; then
  echo "error: -n must be a positive integer (got '$N')" >&2
  exit 2
fi
if [ -n "$TIMEOUT_S" ] && ! is_pos_int "$TIMEOUT_S"; then
  echo "error: -T must be a positive integer (got '$TIMEOUT_S')" >&2
  exit 2
fi

GOBRA_JAR=${GOBRA_JAR:-/gobra/gobra.jar}
if [ ! -f "$GOBRA_JAR" ]; then
  echo "error: GOBRA_JAR '$GOBRA_JAR' does not exist." >&2
  echo "Set GOBRA_JAR to the path of your gobra.jar, e.g.:" >&2
  echo "  GOBRA_JAR=~/gobra/gobra.jar tooling/verify-bench.sh" >&2
  exit 2
fi

if [ -z "$TAG" ]; then
  TAG=$(date -u +%Y%m%dT%H%M%SZ)
fi

# Default outdir is OUTSIDE the repository on purpose: measurement data must
# never end up inside (let alone committed to) the repo.
if [ -z "$OUTDIR" ]; then
  tmp_base=${TMPDIR:-/tmp}
  tmp_base=${tmp_base%/}
  OUTDIR="$tmp_base/keytrans-verify-bench/$TAG"
fi

if ! mkdir -p "$OUTDIR"; then
  echo "error: cannot create output directory '$OUTDIR'" >&2
  exit 2
fi
OUTDIR=$(cd "$OUTDIR" && pwd -P)

case "$OUTDIR/" in
  "$REPO_ROOT"/*)
    echo "WARNING: output directory $OUTDIR is INSIDE the repository ($REPO_ROOT)." >&2
    echo "WARNING: benchmark data must never be committed. Proceeding as requested." >&2
    ;;
esac

TIMINGS="$OUTDIR/timings.tsv"
if [ ! -f "$TIMINGS" ]; then
  printf 'iter\tphase\twall_s\texit_code\n' > "$TIMINGS"
fi

# --- keep in sync with .github/workflows/verify.yml (job verify-packages) ---
MOD_NAME="github.com/felixlinker/keytrans-verification"
EXCLUDE_PKGS="main"
UNARY_MODE_PKGS="proofs utils"
# ---------------------------------------------------------------------------

KILL_GRACE_S=10   # seconds to wait after SIGTERM before escalating to SIGKILL
ANY_FAILED=0
CURRENT_PGID=""

# Kill whatever phase group is still running. Called from traps, so it must
# be safe to call at any time (no-op when no phase is in flight).
cleanup() {
  if [ -n "$CURRENT_PGID" ]; then
    kill -- "-$CURRENT_PGID" 2>/dev/null || true
    sleep 1
    if pgrep -f gobra.jar >/dev/null 2>&1; then
      kill -9 -- "-$CURRENT_PGID" 2>/dev/null || true
    fi
    CURRENT_PGID=""
  fi
}
trap cleanup EXIT
trap 'echo "interrupted; killing running phase" >&2; cleanup; trap - EXIT; exit 130' INT TERM

# Abort when gobra.jar JVMs are already running: a benchmark next to another
# verification run measures garbage, and leaked JVMs froze this machine once
# already. FORCE=1 skips the check.
check_orphans() {
  if [ "${FORCE:-0}" = "1" ]; then
    return 0
  fi
  local procs
  procs=$(pgrep -fl gobra.jar 2>/dev/null || true)
  if [ -n "$procs" ]; then
    echo "error: gobra.jar JVMs are already running:" >&2
    echo "$procs" >&2
    echo "Clean them up first (e.g. 'pkill -f gobra.jar', then check again" >&2
    echo "with 'pgrep -fl gobra.jar'), or re-run with FORCE=1 to skip this check." >&2
    exit 3
  fi
}

# kill_tree PGID: take down the whole phase process tree. The phase was
# started as its own process group (set -m), so `kill -- -PGID` reaches the
# JVM and all its children directly -- never kill only a wrapper by parent
# pid; that is exactly how a previous harness orphaned the JVM grandchild.
kill_tree() {
  local pgid="$1"
  local grace=0
  echo "==> timeout: killing process group $pgid (kill -- -$pgid)" >&2
  kill -- "-$pgid" 2>/dev/null || true
  while [ "$grace" -lt "$KILL_GRACE_S" ]; do
    if ! pgrep -f gobra.jar >/dev/null 2>&1; then
      return 0
    fi
    sleep 1
    grace=$((grace + 1))
  done
  echo "==> JVM survived SIGTERM for ${KILL_GRACE_S}s; escalating: kill -9 -- -$pgid" >&2
  kill -9 -- "-$pgid" 2>/dev/null || true
  sleep 1
  if pgrep -f gobra.jar >/dev/null 2>&1; then
    echo "WARNING: gobra.jar processes are STILL alive after SIGKILL:" >&2
    pgrep -fl gobra.jar >&2 || true
    echo "WARNING: clean these up manually before doing anything else." >&2
  fi
}

# run_phase ITER PHASE GOBRA_ARGS...
run_phase() {
  local iter="$1" phase="$2"
  shift 2
  local iter_dir="$OUTDIR/iter$iter"
  local log="$iter_dir/$phase.log"
  local start end wall rc timed_out pid waited
  timed_out=0

  echo ""
  echo "==> iter $iter/$N, phase $phase (log: $log)"
  start=$(date +%s)

  # set -m gives the background pipeline its own process group whose PGID is
  # $!, so a later `kill -- -$pid` reliably reaches java AND tee AND anything
  # java spawns. Turned off again right after: the group assignment sticks.
  set -m
  (
    cd "$REPO_ROOT" || exit 127
    set -o pipefail
    java -Xss128m -jar "$GOBRA_JAR" "$@" 2>&1 | tee "$log"
  ) &
  pid=$!
  set +m
  CURRENT_PGID=$pid

  if [ -n "$TIMEOUT_S" ]; then
    waited=0
    # bash reaps the background job as it exits, so kill -0 turns false then.
    while kill -0 "$pid" 2>/dev/null; do
      if [ "$waited" -ge "$TIMEOUT_S" ]; then
        timed_out=1
        kill_tree "$pid"
        break
      fi
      sleep 1
      waited=$((waited + 1))
    done
  fi

  wait "$pid"
  rc=$?
  CURRENT_PGID=""
  end=$(date +%s)
  wall=$((end - start))

  if [ "$timed_out" -eq 1 ]; then
    rc=124   # conventional timeout exit code, as used by timeout(1)
    echo "==> iter $iter, phase $phase TIMED OUT after ${wall}s" >&2
  fi

  printf '%s\t%s\t%s\t%s\n' "$iter" "$phase" "$wall" "$rc" >> "$TIMINGS"

  if [ "$rc" -ne 0 ]; then
    ANY_FAILED=1
    echo "==> iter $iter, phase $phase FAILED (exit $rc, ${wall}s)"
  else
    echo "==> iter $iter, phase $phase ok (${wall}s)"
  fi
}

echo "keytrans verify-bench"
echo "  repo:    $REPO_ROOT"
echo "  jar:     $GOBRA_JAR"
echo "  outdir:  $OUTDIR"
echo "  tag:     $TAG"
echo "  n:       $N"
if [ -n "$TIMEOUT_S" ]; then
  echo "  timeout: ${TIMEOUT_S}s per phase"
fi

i=1
while [ "$i" -le "$N" ]; do
  check_orphans
  iter_dir="$OUTDIR/iter$i"
  mkdir -p "$iter_dir/unary" "$iter_dir/hyper"

  # $UNARY_MODE_PKGS / $EXCLUDE_PKGS are intentionally unquoted below: they
  # are space-separated lists, exactly like the CI's env interpolation.
  run_phase "$i" unary \
    --gobraDirectory "$iter_dir/unary" \
    --module "$MOD_NAME" \
    --hyperMode off \
    --recursive \
    --include . .verification \
    --checkConsistency \
    --parallelizeBranches \
    --includePackages $UNARY_MODE_PKGS

  run_phase "$i" hyper \
    --gobraDirectory "$iter_dir/hyper" \
    --module "$MOD_NAME" \
    --hyperMode extended \
    --recursive \
    --include . .verification \
    --checkConsistency \
    --parallelizeBranches \
    --excludePackages $EXCLUDE_PKGS $UNARY_MODE_PKGS

  i=$((i + 1))
done

# Generate the report even when phases failed: partial timing data is still
# worth looking at, and stats.json of the failed phase shows what failed.
echo ""
echo "==> generating report"
VIZ="$SCRIPT_DIR/visualize-verification.py"
viz_rc=0
if [ -f "$VIZ" ]; then
  python3 "$VIZ" "$OUTDIR" \
    -o "$OUTDIR/report.html" \
    --summary "$OUTDIR/summary.md" \
    --title "keytrans verification times ($TAG, n=$N)" || viz_rc=$?
else
  echo "WARNING: $VIZ not found; skipping report generation." >&2
  viz_rc=1
fi

echo ""
echo "============================================================"
echo "  Report:  $OUTDIR/report.html"
echo "  Summary: $OUTDIR/summary.md"
echo "  Timings: $OUTDIR/timings.tsv"
echo "============================================================"

if [ "$ANY_FAILED" -ne 0 ]; then
  echo "error: at least one verification phase failed (see $TIMINGS)" >&2
  exit 1
fi
exit "$viz_rc"
