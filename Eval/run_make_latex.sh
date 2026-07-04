#!/bin/bash
set -euo pipefail

cd "$(dirname "$0")"

mkdir -p latex/main

if [[ -d results ]]; then
  python3 summary_to_latex.py \
    --results-root results \
    --out latex/main

  if find results -name abduction_statistics.csv -print -quit | grep -q .; then
    python3 abduction_statistics_to_latex.py \
      --results-root results \
      --out latex/main

    python3 abduction_graph_to_latex.py \
      --results-root results \
      --out latex/main

    python3 abduction_filter_funnel_to_latex.py \
      --results-root results \
      --out latex/main
  else
    echo "No abduction_statistics.csv found under results; skipping Abduction statistics, AbductionGraph, and filter-attrition figures."
  fi

  if find results -name abduction_decremental_statistics.csv -print -quit | grep -q .; then
    python3 abduction_decremental_to_latex.py \
      --results-root results \
      --out latex/main
  else
    echo "No abduction_decremental_statistics.csv found under results; skipping decremental conjecturing figures."
  fi

  if find results -name tbc_seed_preprocessing_statistics.csv -print -quit | grep -q .; then
    python3 tbc_seed_preprocessing_to_latex.py \
      --results-root results \
      --out latex/main
  else
    echo "No tbc_seed_preprocessing_statistics.csv found under results; skipping TBC-seeded pipeline summaries."
  fi
else
  echo "No results directory found; skipping main LaTeX generation."
fi

if [[ -d results_screening ]]; then
  mkdir -p latex/screening
  python3 summary_to_latex.py \
    --results-root results_screening \
    --out latex/screening
else
  echo "No results_screening directory found; skipping screening LaTeX generation."
fi

echo "Generated files under latex/ where applicable."
echo "Main output:       latex/main"
if [[ -d latex/screening ]]; then
  echo "Screening output:  latex/screening"
fi
