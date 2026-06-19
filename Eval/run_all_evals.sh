#!/bin/bash
set -euo pipefail

./Eval/run_eval.sh Isaplanner full 2000

./Eval/run_eval.sh Prod full 2000

./Eval/run_eval.sh TIP15 sample 2000 50 2027

./Eval/run_eval.sh TIP15 full 600