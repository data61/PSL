#!/bin/bash
set -euo pipefail

BENCHMARK="${1:?Usage: $0 BENCHMARK full|sample TIMEOUT [SAMPLE_SIZE] [SAMPLE_SEED]}"
MODE="${2:?Usage: $0 BENCHMARK full|sample TIMEOUT [SAMPLE_SIZE] [SAMPLE_SEED]}"
TIMEOUT="${3:?Usage: $0 BENCHMARK full|sample TIMEOUT [SAMPLE_SIZE] [SAMPLE_SEED]}"

SAMPLE_SIZE="${4:-50}"
SAMPLE_SEED="${5:-2027}"

GENERATED_ROOT="${GENERATED_ROOT:-Eval/generated}"
RESULTS_ROOT="${RESULTS_ROOT:-Eval/results}"
ROOT="${ROOT:-.}"
ISABELLE="${ISABELLE:-isabelle}"
THREADS="${THREADS:-0}"

# Use PSL_EVAL_* names to avoid accidental interference from generic
# environment variables such as METHODS.
PSL_EVAL_METHODS="${PSL_EVAL_METHODS:-sledgehammer psl tbc abduction preprocessed_abduction}"
PSL_EVAL_SLEDGEHAMMER_GRACE_SEC="${PSL_EVAL_SLEDGEHAMMER_GRACE_SEC:-30}"
PSL_EVAL_TBC_PREPROCESS_ROUNDS="${PSL_EVAL_TBC_PREPROCESS_ROUNDS:-2}"
export PSL_EVAL_TBC_PREPROCESS_ROUNDS

# Per-call Sledgehammer budget (see TBC_Utils.Short_Hammer/Long_Hammer).  The
# defaults baked into the ML suit Isaplanner and Prod; TIP15 wants the shorter
# 5.0/10.0, both to fit more targets into a run and because this budget is the
# only ceiling on how far a diverging external prover can grow (they are given
# --max-time but no memory limit).
if [ -n "${PSL_SHORT_HAMMER:-}" ]; then export PSL_SHORT_HAMMER; fi
if [ -n "${PSL_LONG_HAMMER:-}" ];  then export PSL_LONG_HAMMER;  fi

# Poly/ML grows its heap to fill available RAM unless told otherwise, and
# Isabelle ships no maxheap by default (ML_OPTIONS32="--minheap 500").  In the
# recorded TIP15 run that let the ML process reach 8-11GB, and 148 of the 176
# abduction/preprocessed_abduction failures were memory exhaustion rather than
# anything the prover reported: 106 SIGKILLed by the OS OOM killer and 42 dying
# inside Poly/ML's own "Run out of store".
#
# ML_OPTIONS cannot be exported from here: Isabelle rebuilds its settings
# environment from $ISABELLE_HOME/etc/settings plus $ISABELLE_HOME_USER/etc/
# settings, and the latter's location is itself overwritten by the former, so a
# shell variable set here never reaches the ML process.  It has to be set in the
# user settings file, which is machine-level configuration rather than something
# this script can do safely.  Warn rather than silently repeating the run that
# lost 148 targets.
if [ -z "$($ISABELLE getenv -b ML_OPTIONS 2>/dev/null)" ]; then
  cat >&2 <<'WARN'
WARNING: ML_OPTIONS is unset, so Poly/ML has no maxheap and will grow until the
         machine runs out of memory.  Consider adding a line such as

             ML_OPTIONS="--minheap 500 --maxheap 3500"

         to $ISABELLE_HOME_USER/etc/settings (run "isabelle getenv
         ISABELLE_HOME_USER" to locate it), sized so that the ML heap, the
         ~1.5GB Isabelle JVM and the concurrently-running external provers all
         fit in RAM.
WARN
fi

# Important: define as empty array for "full" mode.
EXTRA_ARGS=()

case "$BENCHMARK" in
  Isaplanner|Prod|TIP15)
    ;;
  *)
    echo "Unknown benchmark: $BENCHMARK" >&2
    exit 1
    ;;
esac

case "$MODE" in
  full)
    OUT="${RESULTS_ROOT}/${BENCHMARK}"
    ;;
  sample)
    OUT="${RESULTS_ROOT}/${BENCHMARK}_sample_${SAMPLE_SIZE}_seed_${SAMPLE_SEED}"
    EXTRA_ARGS=(
      --sample-size "$SAMPLE_SIZE"
      --sample-seed "$SAMPLE_SEED"
      --selected-targets-out "$OUT/selected_targets.txt"
    )
    ;;
  *)
    echo "Unknown mode: $MODE" >&2
    exit 1
    ;;
esac

echo "Benchmark : $BENCHMARK"
echo "Mode      : $MODE"
echo "Timeout   : ${TIMEOUT}s"
echo "Threads   : $THREADS"
echo "Methods   : $PSL_EVAL_METHODS"
echo "SH grace  : ${PSL_EVAL_SLEDGEHAMMER_GRACE_SEC}s"
echo "TBC pre   : ${PSL_EVAL_TBC_PREPROCESS_ROUNDS} round(s)"
echo "Isabelle  : $ISABELLE"
echo "Results   : $RESULTS_ROOT"
echo "Output    : $OUT"

# shellcheck disable=SC2086
python3 Eval/eval_methods_round_robin.py \
  --generated-root "$GENERATED_ROOT" \
  --benchmark "$BENCHMARK" \
  --methods $PSL_EVAL_METHODS \
  --isabelle "$ISABELLE" \
  --root "$ROOT" \
  --threads "$THREADS" \
  --timeout "$TIMEOUT" \
  --sledgehammer-grace-sec "$PSL_EVAL_SLEDGEHAMMER_GRACE_SEC" \
  --out "$OUT" \
  ${EXTRA_ARGS[@]+"${EXTRA_ARGS[@]}"} \
  --kill-all-isabelle-on-abort
