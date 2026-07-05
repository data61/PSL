#!/bin/bash
set -euo pipefail

# Two-stage evaluation:
#
# 1. Screening run:
#      all five methods, including direct Sledgehammer, on Isaplanner only,
#      with a shorter timeout.  This establishes whether Sledgehammer is
#      competitive on the easiest benchmark.
#
# 2. Main run:
#      PSL, TBC, AbductionProver, and preprocessed AbductionProver, with the full timeout, on the main
#      benchmark suite.
#
# Override examples:
#   PSL_EVAL_SCREEN_TIMEOUT=300 ./Eval/run_all_evals.sh
#   PSL_EVAL_MAIN_TIMEOUT=3000 ./Eval/run_all_evals.sh
#   PSL_EVAL_MAIN_METHODS="psl tbc abduction preprocessed_abduction" ./Eval/run_all_evals.sh

PSL_EVAL_SCREEN_RESULTS_ROOT="${PSL_EVAL_SCREEN_RESULTS_ROOT:-Eval/results_screening}"
PSL_EVAL_MAIN_RESULTS_ROOT="${PSL_EVAL_MAIN_RESULTS_ROOT:-Eval/results}"

PSL_EVAL_SCREEN_METHODS="${PSL_EVAL_SCREEN_METHODS:-sledgehammer psl tbc abduction preprocessed_abduction}"
PSL_EVAL_MAIN_METHODS="${PSL_EVAL_MAIN_METHODS:-psl tbc abduction preprocessed_abduction}"

PSL_EVAL_SCREEN_TIMEOUT="${PSL_EVAL_SCREEN_TIMEOUT:-100}"
PSL_EVAL_MAIN_TIMEOUT="${PSL_EVAL_MAIN_TIMEOUT:-3000}"
PSL_EVAL_TIP15_FULL_TIMEOUT="${PSL_EVAL_TIP15_FULL_TIMEOUT:-600}"

PSL_EVAL_TIP15_SAMPLE_SIZE="${PSL_EVAL_TIP15_SAMPLE_SIZE:-50}"
PSL_EVAL_TIP15_SAMPLE_SEED="${PSL_EVAL_TIP15_SAMPLE_SEED:-2027}"

PSL_EVAL_SLEDGEHAMMER_GRACE_SEC="${PSL_EVAL_SLEDGEHAMMER_GRACE_SEC:-30}"
PSL_EVAL_TBC_PREPROCESS_ROUNDS="${PSL_EVAL_TBC_PREPROCESS_ROUNDS:-2}"
export PSL_EVAL_SLEDGEHAMMER_GRACE_SEC
export PSL_EVAL_TBC_PREPROCESS_ROUNDS

echo "=== Cleaning old evaluation artefacts ==="
rm -rf "${PSL_EVAL_SCREEN_RESULTS_ROOT:?}"/*/sessions
rm -rf "${PSL_EVAL_SCREEN_RESULTS_ROOT:?}"/*/logs
rm -rf "${PSL_EVAL_SCREEN_RESULTS_ROOT:?}"/*/proofs

rm -rf "${PSL_EVAL_MAIN_RESULTS_ROOT:?}"/*/sessions
rm -rf "${PSL_EVAL_MAIN_RESULTS_ROOT:?}"/*/logs
rm -rf "${PSL_EVAL_MAIN_RESULTS_ROOT:?}"/*/proofs

echo
echo "=== Stage 1: Sledgehammer screening on Isaplanner ==="
echo "Results root : $PSL_EVAL_SCREEN_RESULTS_ROOT"
echo "Methods      : $PSL_EVAL_SCREEN_METHODS"
echo "Timeout      : ${PSL_EVAL_SCREEN_TIMEOUT}s"

RESULTS_ROOT="$PSL_EVAL_SCREEN_RESULTS_ROOT" \
PSL_EVAL_METHODS="$PSL_EVAL_SCREEN_METHODS" \
./Eval/run_eval.sh Isaplanner full "$PSL_EVAL_SCREEN_TIMEOUT"

echo
echo "=== Stage 2: main evaluation without Sledgehammer ==="
echo "Results root : $PSL_EVAL_MAIN_RESULTS_ROOT"
echo "Methods      : $PSL_EVAL_MAIN_METHODS"
echo "Timeout      : ${PSL_EVAL_MAIN_TIMEOUT}s"
echo "TBC pre      : ${PSL_EVAL_TBC_PREPROCESS_ROUNDS} round(s)"

RESULTS_ROOT="$PSL_EVAL_MAIN_RESULTS_ROOT" \
PSL_EVAL_METHODS="$PSL_EVAL_MAIN_METHODS" \
./Eval/run_eval.sh Isaplanner full "$PSL_EVAL_MAIN_TIMEOUT"

RESULTS_ROOT="$PSL_EVAL_MAIN_RESULTS_ROOT" \
PSL_EVAL_METHODS="$PSL_EVAL_MAIN_METHODS" \
./Eval/run_eval.sh Prod full "$PSL_EVAL_MAIN_TIMEOUT"

RESULTS_ROOT="$PSL_EVAL_MAIN_RESULTS_ROOT" \
PSL_EVAL_METHODS="$PSL_EVAL_MAIN_METHODS" \
./Eval/run_eval.sh TIP15 sample "$PSL_EVAL_MAIN_TIMEOUT" \
  "$PSL_EVAL_TIP15_SAMPLE_SIZE" "$PSL_EVAL_TIP15_SAMPLE_SEED"

# Optional full TIP15 run with a shorter timeout, kept from the previous script.
RESULTS_ROOT="$PSL_EVAL_MAIN_RESULTS_ROOT" \
PSL_EVAL_METHODS="$PSL_EVAL_MAIN_METHODS" \
./Eval/run_eval.sh TIP15 full "$PSL_EVAL_TIP15_FULL_TIMEOUT"
