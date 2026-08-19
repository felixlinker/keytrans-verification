#!/bin/bash

# Verifies one or more packages and records how long each one took, so that
# changes to the specifications can be compared against a known baseline.
#
# Usage: ./tooling/verify-package.sh [-t <tag>] [-n <repeats>] [<package>...] [-- <extra gobra args>...]
#
#   <package>  package names (not directory names) to verify. Defaults to all.
#   -t <tag>   name of this run; results are written to .verify-runs/<tag>
#              (default: "run")
#   -n <k>     verify each package k times (default: 1). Verification time
#              varies a lot between runs on identical input, so a single
#              measurement is not evidence; the report gives the median and the
#              observed spread.
#   -T <secs>  kill a run that exceeds this many seconds and record it as a
#              timeout (default: no limit). Occasionally a run takes orders of
#              magnitude longer than the median; a cap keeps a repeated
#              measurement bounded and turns those runs into a countable
#              outcome rather than an unbounded wait.
#   --         everything after this is appended to the Gobra invocation. This
#              is for *diagnostics only* (e.g. --chop, --assertTimeout); the
#              committed configuration must stay identical to the one CI uses,
#              otherwise the numbers are not comparable.
#
# The Gobra jar defaults to the location used by the CI container. Set
# GOBRA_JAR to point at a local build.
#
# Examples:
#   ./tooling/verify-package.sh -t baseline -n 3
#   ./tooling/verify-package.sh log
#   ./tooling/verify-package.sh -t chop4 log -- --chop 4

set -uo pipefail

repoRoot=$(cd "$(dirname "$0")/.." && pwd)

gobraJar="${GOBRA_JAR:-/gobra/gobra.jar}"

# Parallel branch verification is on by default, as in local-verify-package.sh.
# Set PARALLELIZE_BRANCHES=0 to leave the flag out, which is how CI runs Gobra
# and which is worth comparing against when run-to-run times vary a lot.
parallelFlag=(--parallelizeBranches)
if [ "${PARALLELIZE_BRANCHES:-1}" = "0" ]; then
    parallelFlag=()
fi

# Package names, not directory names. Ordered cheapest-first so that a broken
# build fails fast.
allPackages=(utils proofs crypto misc utilsrel search prefix log client)

tag="run"
repeats=1
runTimeout=0
packages=()
while [ $# -gt 0 ]; do
    case "$1" in
        -t|--tag) tag="$2"; shift 2 ;;
        -n|--repeats) repeats="$2"; shift 2 ;;
        -T|--timeout) runTimeout="$2"; shift 2 ;;
        --) shift; break ;;
        -*) echo "unknown option: $1" >&2; exit 1 ;;
        *) packages+=("$1"); shift ;;
    esac
done
extraArgs=("$@")

if [ ${#packages[@]} -eq 0 ]; then
    packages=("${allPackages[@]}")
fi

if [ ! -f "$gobraJar" ]; then
    echo "Gobra jar not found at $gobraJar; set GOBRA_JAR to override" >&2
    exit 1
fi

outDir="$repoRoot/.verify-runs/$tag"
rm -rf "$outDir"
mkdir -p "$outDir"

timings="$outDir/timings.tsv"
printf 'package\trun\twall_s\tcpu_s\terrors\n' > "$timings"

if [ ${#extraArgs[@]} -gt 0 ]; then
    echo "extra gobra args: ${extraArgs[*]}" | tee "$outDir/extra-args.txt"
fi

failed=0

for pkg in "${packages[@]}"; do
    echo "=== $pkg"
    for run in $(seq 1 "$repeats"); do
        # Only the first run's stats.json is kept for per-member numbers; the
        # remaining runs exist to measure the spread of the wall/CPU time.
        if [ "$repeats" -eq 1 ]; then
            pkgOut="$outDir/$pkg"
        else
            pkgOut="$outDir/$pkg/run$run"
        fi
        mkdir -p "$pkgOut"
        log="$pkgOut/gobra.log"

        start=$(date +%s)
        # `time` reports to stderr; run it in a group so its output ends up in
        # the log next to Gobra's, and parse it back out afterwards.
        { /usr/bin/time -p java -Xss128m -jar "$gobraJar" \
            --recursive -I "$repoRoot" \
            --module github.com/felixlinker/keytrans-verification \
            --include "$repoRoot/.verification" \
            "${parallelFlag[@]+"${parallelFlag[@]}"}" \
            --includePackages "$pkg" \
            --gobraDirectory "$pkgOut" \
            "${extraArgs[@]+"${extraArgs[@]}"}" ; } > "$log" 2>&1 &
        gobraPid=$!

        timedOut=0
        if [ "$runTimeout" -gt 0 ]; then
            ( sleep "$runTimeout"; kill -0 "$gobraPid" 2>/dev/null && \
              pkill -P "$gobraPid" 2>/dev/null; kill "$gobraPid" 2>/dev/null ) &
            watchdog=$!
            wait "$gobraPid" 2>/dev/null
            kill "$watchdog" 2>/dev/null
            wait "$watchdog" 2>/dev/null
        else
            wait "$gobraPid" 2>/dev/null
        fi
        wall=$(( $(date +%s) - start ))
        if [ "$runTimeout" -gt 0 ] && [ "$wall" -ge "$runTimeout" ]; then
            timedOut=1
        fi

        user=$(awk '/^user /{print $2}' "$log" | tail -1)
        sys=$(awk '/^sys /{print $2}' "$log" | tail -1)
        cpu=$(awk -v u="${user:-0}" -v s="${sys:-0}" 'BEGIN{printf "%.0f", u+s}')

        errors=$(grep -oE 'Gobra found [0-9]+ error' "$log" | grep -oE '[0-9]+' | tail -1)
        if [ "$timedOut" -eq 1 ]; then
            errors="timeout"
            failed=1
        elif [ -z "$errors" ]; then
            errors="?"
            failed=1
        elif [ "$errors" != "0" ]; then
            failed=1
        fi

        printf '%s\t%s\t%s\t%s\t%s\n' "$pkg" "$run" "$wall" "$cpu" "$errors" >> "$timings"
        echo "    run $run: wall ${wall}s  cpu ${cpu}s  errors ${errors}"
    done
done

echo
python3 "$repoRoot/tooling/verify-report.py" "$outDir" | tee "$outDir/report.txt"

exit $failed
