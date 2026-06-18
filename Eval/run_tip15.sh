#!/bin/bash

python3 Eval/eval_methods_round_robin.py \
  --generated-root Eval/generated \
  --benchmark TIP15 \
  --methods psl tbc abduction \
  --root . \
  --threads 0 \
  --timeout 600 \
  --out Eval/results/TIP15