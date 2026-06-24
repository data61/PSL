#!/bin/bash
set -euo pipefail

rm -rf Eval/results/*/sessions
rm -rf Eval/results/*/logs
rm -rf Eval/results/*/proofs

# Default method set now includes an independent Sledgehammer baseline.
# Override at invocation time if needed, e.g.:
#   PSL_EVAL_METHODS="psl tbc abduction" ./Eval/run_all_evals.sh
#   PSL_EVAL_METHODS="sledgehammer" ./Eval/run_eval.sh Isaplanner sample 2000 3 2027
PSL_EVAL_METHODS="${PSL_EVAL_METHODS:-sledgehammer psl tbc abduction}"
PSL_EVAL_SLEDGEHAMMER_GRACE_SEC="${PSL_EVAL_SLEDGEHAMMER_GRACE_SEC:-30}"

export PSL_EVAL_METHODS
export PSL_EVAL_SLEDGEHAMMER_GRACE_SEC

echo "Methods   : $PSL_EVAL_METHODS"
echo "SH grace  : ${PSL_EVAL_SLEDGEHAMMER_GRACE_SEC}s"

./Eval/run_eval.sh Isaplanner full 2000

./Eval/run_eval.sh Prod full 2000

./Eval/run_eval.sh TIP15 sample 2000 50 2027

./Eval/run_eval.sh TIP15 full 600
