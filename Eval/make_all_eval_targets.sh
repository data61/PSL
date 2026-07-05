#!/bin/bash
set -euo pipefail

rm -rf Eval/generated

METHODS=(
  sledgehammer
  psl
  tbc
  abduction
  preprocessed_abduction
)

BENCHMARKS=(
  "Prod:UR/TIP/Prod/Prod"
  "Isaplanner:UR/TIP/Isaplanner/Isaplanner"
  "TIP15:UR/TIP/TIP15/TIP15"
)

for method in "${METHODS[@]}"; do
  for item in "${BENCHMARKS[@]}"; do
    name="${item%%:*}"
    source="${item#*:}"

    python3 Eval/make_eval_targets.py \
      --method "$method" \
      "$source" \
      "Eval/generated/$method/$name"
  done
done