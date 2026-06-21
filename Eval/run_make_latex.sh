#!/bin/bash
set -euo pipefail

cd "$(dirname "$0")"

python3 summary_to_latex.py \
  --results-root results \
  --out latex