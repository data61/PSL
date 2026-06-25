#!/bin/bash
set -euo pipefail

cd "$(dirname "$0")"

mkdir -p latex/main
mkdir -p latex/screening

python3 summary_to_latex.py \
  --results-root results \
  --out latex/main

python3 abduction_statistics_to_latex.py \
  --results-root results \
  --benchmark Prod \
  --out latex/main

#python3 summary_to_latex.py \
#  --results-root results_screening \
#  --out latex/screening

echo "Generated:"
echo "  latex/main"
echo "  latex/screening"
echo "  Abduction figures (Prod only) under latex/main"
