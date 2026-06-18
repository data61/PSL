#!/bin/bash

python3 Eval/eval_methods_round_robin.py \
  --generated-root Eval/generated \
  --benchmark Prod \
  --methods psl tbc abduction \
  --root . \
  --threads 0 \
  --timeout 2000 \
  --out Eval/results/Prod