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
PSL_EVAL_METHODS="${PSL_EVAL_METHODS:-sledgehammer psl tbc abduction}"
PSL_EVAL_SLEDGEHAMMER_GRACE_SEC="${PSL_EVAL_SLEDGEHAMMER_GRACE_SEC:-30}"

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
