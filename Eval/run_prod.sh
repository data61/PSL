#!/bin/bash

python3 Eval/eval_abduction_dir.py \
    UR/TIP/Prod/Prod \
    --root . \
    --logic Smart_Isabelle \
    --threads 0 \
    --timeout 2000 \
    --out Eval/Prod