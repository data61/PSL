#!/bin/bash
# Capability evaluation that decides "proved" from the prover's own verdict.
#
# This replaces the ad-hoc scripts that decided it by grepping the build log for Isabelle's
# "Finished <session>" line. That line says the THEORY COMPILED. "prove_by_abduction" is an
# Outer_Syntax.local_theory command - it runs the search, discards the result, and returns its
# context unchanged whether or not a proof was found - so the theory compiles either way, and
# every target that did not crash was recorded as proved. Two evaluations were read that way and
# their headline numbers are counts of compiled theories: see OVERNIGHT_EVAL_2026-08-04.html and
# PARTIAL_PROOF_EVAL_2026-08-04.html, both corrected in place.
#
# It lives in the repository, under version control, because the scripts that got this wrong did
# not. That is a large part of why the error survived two evaluations.
#
# Usage:  Eval/run_verdict_eval.sh <targets-dir> <out-dir> [prove_timeout] [wall_clock] [threads]
#
#   <targets-dir>  a directory of generated .thy targets, one goal each
#   <out-dir>      created fresh; receives proofs/, work/, verdicts.csv and summary.csv
#
# Read summary.csv. Its "verdict" column is the prover's own answer, taken from verdicts.csv:
#
#   proved          the search proved the goal and emitted a script
#   proved-applied  solve proved it and applied it to the caller's state (no file expected)
#   unproved        the search finished without a proof - BUT check guard_stops first: a
#                   memory-guard stop is handled by returning what has been proved, which reports
#                   as unproved. A row with guard_stops > 0 is a truncated search, not a verdict
#                   on the goal.
#   none            no verdict was reached - the run died first (memory guard, wall clock, crash)
#
# "none" is not "unproved". An absent verdict is not a claim, and counting it as a failure is the
# same class of mistake as counting a compiled theory as a success.
#
# Two things that look like evidence and are not, both measured:
#   * "Finished <session>" - see above.
#   * the presence of a .proof file - a FAILED search writes one too, holding the auxiliary
#     lemmas it did prove. A goal reported unproved after 217s left a .proof file behind.
set -u

SRC=${1:?usage: run_verdict_eval.sh <targets-dir> <out-dir> [prove_timeout] [wall_clock]}
OUT=${2:?usage: run_verdict_eval.sh <targets-dir> <out-dir> [prove_timeout] [wall_clock]}
PROVE_TIMEOUT=${3:-900}
# Deliberately not equal to PROVE_TIMEOUT. prove_timeout bounds when new work may START, not how
# long a run takes: measured, prove_timeout = 300 produced a 1171-second run, because attempts
# already in flight run to their own budgets. See AGENTS.md. Leave real headroom here or the wall
# clock, not the prover, decides the result.
WALL=${4:-$((PROVE_TIMEOUT * 2))}
# Fewer worker threads is the memory lever that does NOT cost search time. Each worker that
# reaches a hammer launches Sledgehammer, which starts every prover in sledgehammer_provers
# concurrently as external processes - time-bounded but not memory-bounded. So peak memory scales
# with the number of workers in a hammer at once, and halving the workers halves the concurrent
# prover footprint while every hammer keeps its full budget.
#
# Shortening the hammer budget instead is the obvious alternative and is the wrong trade here.
# TIP15_HARD_FAILURE_ANALYSIS.md section 6 compared 5/10 against 10/30 on four targets that were
# already known provable, and says plainly that the sample "cannot contain the case that matters
# most - a conjecture whose usefulness Sledgehammer only establishes after more than five
# seconds". Cutting the budget turns capability results into budget results.
#
# Not zero, and not left to Isabelle's own guess: threads = 0 under-counts cores badly on these
# VMs and has repeatedly been mistaken for slow proof search. See README.md.
THREADS=${5:-$(nproc)}

if [ -z "${ML_OPTIONS:-}" ] && ! isabelle getenv -b ML_OPTIONS | grep -q maxheap; then
  echo "WARNING: Poly/ML has no heap ceiling (ML_OPTIONS has no --maxheap)." >&2
  echo "  Without one the ML process grows until the run dies; TIP15_HARD_FAILURE_ANALYSIS.md" >&2
  echo "  section 2 blames that for 149 of 176 abduction failures. Set it in" >&2
  echo "  \$ISABELLE_HOME_USER/etc/settings, e.g. --minheap 500 --maxheap 3500 on an 11GB box." >&2
fi

rm -rf "$OUT"; mkdir -p "$OUT/proofs" "$OUT/work"
export PSL_PROOF_OUTPUT_DIR="$OUT/proofs"
echo "target,verdict,elapsed_sec,proof_files,guard_stops,build,note" > "$OUT/summary.csv"

for thy in "$SRC"/*.thy; do
  g=$(basename "$thy" .thy)
  w="$OUT/work/$g"; mkdir -p "$w"
  # The target states its own prove_timeout, and imports Abduction directly.
  sed -e "s/^begin\$/begin\ndeclare [[prove_timeout = $PROVE_TIMEOUT]]/" \
      -e "s/^ *imports .*/  imports Main \"Abduction.Abduction\"/" "$thy" > "$w/$g.thy"
  printf 'session %s (psl) in "." = "Abduction" +\n  options [timeout = %d]\n  theories [document = false]\n    "%s"\n' \
    "$g" "$((WALL * 2))" "$g" > "$w/ROOT"

  # Tested rather than redirected: "wc -l < missing 2>/dev/null" still reports the failed
  # redirect, because the shell opens the file before wc runs.
  if [ -f "$OUT/proofs/verdicts.csv" ]; then before=$(wc -l < "$OUT/proofs/verdicts.csv"); else before=0; fi
  st=$(date +%s)
  # The memory guard is set unconditionally, not as an option to remember. A guard stop is
  # HANDLED cleanly - the search returns what it has proved, so "solved" is false and the verdict
  # says "unproved" - which is indistinguishable from a genuine failure to prove unless this log
  # exists. Measured on this box: a run with 3.0GB available had the guard fire twice and report
  # unproved, while the same goal proved when memory was free. Reading a truncated search as a
  # capability result is the same class of error as reading a compiled theory as a proof.
  out=$(PSL_MEMORY_MONITOR_LOG="$w/guard.log" \
        timeout "$WALL" isabelle build -c -d "$PWD" -d "$w" -o threads="$THREADS" "$g" 2>&1)
  el=$(( $(date +%s) - st ))
  printf "%s\n" "$out" > "$w/build.log"

  # The prover's own answer: the row it appended for this run, if it reached one at all.
  row=$(tail -n +$((before + 1)) "$OUT/proofs/verdicts.csv" 2>/dev/null | tail -1)
  verdict=$(printf "%s" "$row" | cut -d, -f2); [ -z "$verdict" ] && verdict=none
  files=$(printf "%s" "$row" | cut -d, -f4);   [ -z "$files" ] && files=0
  if printf "%s" "$out" | grep -q "^Finished $g"; then build=ok; else build=FAILED; fi
  note=$(printf "%s" "$out" | grep -oE '\*\*\* [^*]{0,60}' | head -1 | tr ',' ';')

  guard=$( [ -f "$w/guard.log" ] && wc -l < "$w/guard.log" || echo 0 )
  echo "$g,$verdict,$el,$files,$guard,$build,$note" >> "$OUT/summary.csv"
  echo "$g: verdict=$verdict guard_stops=$guard build=$build ${el}s"
done

echo "ALLDONE" >> "$OUT/summary.csv"
echo
echo "=== counts by verdict ==="
tail -n +2 "$OUT/summary.csv" | grep -v ALLDONE | cut -d, -f2 | sort | uniq -c
echo
echo "=== how many were truncated by the memory guard ==="
echo "  these are NOT capability results; their searches were cut short:"
tail -n +2 "$OUT/summary.csv" | grep -v ALLDONE | awk -F, '$5 > 0 {print "  " $1 " (" $2 ", " $5 " guard stops)"}'
n=$(tail -n +2 "$OUT/summary.csv" | grep -v ALLDONE | awk -F, '$5 > 0' | wc -l)
echo "  total: $n"
