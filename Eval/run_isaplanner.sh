#!/bin/bash

python3 Eval/eval_abduction_dir.py \
    Eval/generated/Isaplanner/ \
    --root . \
    --logic Smart_Isabelle \
    --threads 0 \
    --timeout 2000 \
    --out Eval/Isaplanner