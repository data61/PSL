#!/bin/bash

python3 Eval/eval_abduction_dir.py \
    UR/TIP/TIP15/TIP15 \
    --root . \
    --logic Smart_Isabelle \
    --threads 0 \
    --timeout 600 \
    --out Eval/TIP15