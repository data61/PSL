#!/usr/bin/env python3
r"""Generate a stacked runtime-profile figure for TBC-seeded AbductionProver.

Input:
  Eval/results/<benchmark>/tbc_seed_preprocessing_statistics.csv

Output:
  One PGFPlots/TikZ figure per benchmark that shows, for solved problems only,
  a stacked runtime decomposition over solved-problem rank:

    * PSL/direct goal attack time,
    * remaining TBC preprocessing time, and
    * Pure AbductionProver time.

The solved problems are sorted by total runtime, so the x-axis acts like a
cactus-style solved-problem rank.  The result is a stacked area plot with three
planes, one for each stage.  The generated figure uses black-and-white TikZ
patterns; add \usetikzlibrary{patterns} to the LaTeX preamble.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Optional


def truthy(x: object) -> bool:
    return str(x).strip().lower() in {"1", "true", "yes", "y"}


def to_float(x: object) -> Optional[float]:
    if x is None:
        return None
    s = str(x).strip()
    if not s:
        return None
    try:
        y = float(s)
    except ValueError:
        return None
    return y if math.isfinite(y) else None


def tex_escape(s: object) -> str:
    text = str(s)
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(ch, ch) for ch in text)


def fmt_num(x: Optional[float], digits: int = 1) -> str:
    if x is None:
        return "--"
    if abs(x - round(x)) < 10 ** (-(digits + 1)):
        return str(int(round(x)))
    return f"{x:.{digits}f}"


def distinct_benchmarks(rows: list[dict]) -> list[str]:
    return sorted({str(r.get("benchmark", "")).strip() for r in rows if str(r.get("benchmark", "")).strip()})


def discover_csvs(results_root: Optional[Path], explicit_csvs: list[Path]) -> list[Path]:
    csvs: list[Path] = []
    for p in explicit_csvs:
        if not p.exists():
            raise FileNotFoundError(f"No such TBC-seed preprocessing statistics CSV: {p}")
        csvs.append(p)
    if results_root:
        if not results_root.exists():
            raise FileNotFoundError(f"No such results root: {results_root}")
        csvs.extend(sorted(results_root.rglob("tbc_seed_preprocessing_statistics.csv")))
    seen = set()
    out: list[Path] = []
    for p in csvs:
        q = p.resolve()
        if q not in seen:
            seen.add(q)
            out.append(p)
    return out


def read_rows(csvs: list[Path]) -> list[dict]:
    rows: list[dict] = []
    for path in csvs:
        with path.open(encoding="utf-8", newline="") as f:
            for raw in csv.DictReader(f):
                row = dict(raw)
                row["benchmark"] = (row.get("benchmark") or path.parent.name).strip() or path.parent.name
                rows.append(row)
    return rows


def filter_rows(rows: list[dict], method: str, benchmark: Optional[str]) -> list[dict]:
    out = rows
    wanted_method = str(method or "").strip()
    if wanted_method not in {"", "all"}:
        out = [r for r in out if str(r.get("method", "")).strip() == wanted_method]
    if benchmark:
        out = [r for r in out if str(r.get("benchmark", "")).strip() == benchmark]
    return out


def is_clean_proof(row: dict) -> bool:
    proof_text = str(row.get("proof_found", "")).strip()
    if proof_text:
        return truthy(proof_text)
    status = str(row.get("status", "")).strip().lower()
    return status in {"ok", "proved", "success"}

def method_output_dir(base: Path, method: str) -> Path:
    wanted = str(method or "").strip()
    if wanted in {"", "preprocessed_abduction", "all"}:
        return base
    safe = "".join(ch if ch.isalnum() or ch in {"-", "_"} else "_" for ch in wanted)
    return base / safe


def solved_profiles(rows: list[dict]) -> list[dict]:
    solved = [r for r in rows if is_clean_proof(r)]
    profiles: list[dict] = []
    for row in solved:
        direct = to_float(row.get("direct_goal_elapsed_sec")) or 0.0
        tbc_total = to_float(row.get("tbc_preprocessing_elapsed_sec")) or 0.0
        abduction = to_float(row.get("abduction_elapsed_sec")) or 0.0
        total = to_float(row.get("total_elapsed_sec")) or to_float(row.get("elapsed_sec")) or (tbc_total + abduction)
        tbc_only = max(0.0, tbc_total - direct)
        profiles.append(
            {
                "target_id": str(row.get("target_id", "")).strip(),
                "direct": max(0.0, direct),
                "tbc_only": tbc_only,
                "abduction": max(0.0, abduction),
                "total": max(total, direct + tbc_only + abduction),
                "generated": to_float(row.get("generated_conjectures")),
                "proved_lemmas": to_float(row.get("proved_template_lemmas")),
            }
        )
    profiles.sort(key=lambda p: (p["total"], p["target_id"]))
    return profiles


def mean(xs: list[Optional[float]]) -> Optional[float]:
    ys = [x for x in xs if x is not None and math.isfinite(x)]
    if not ys:
        return None
    return sum(ys) / len(ys)


def coordinates(values: list[float]) -> str:
    """Return step-area coordinates with rank i centered at x=i.

    With PGFPlots' const plot convention, a value at coordinate x_i is
    drawn over the interval from x_i to x_{i+1}.  Therefore, if we used
    points (0,0), (1,y_1), (2,y_2), the first non-zero value would occupy
    the interval [1,2], leaving [0,1] empty.  Here each solved-problem rank
    is treated as a unit-width bin centered at the integer rank: y_i is drawn
    over [i-0.5, i+0.5].
    """
    if not values:
        return "{}"
    points = []
    for i, v in enumerate(values, start=1):
        points.append(f"({i - 0.5:.6f},{v:.6f})")
    points.append(f"({len(values) + 0.5:.6f},{values[-1]:.6f})")
    return "{" + " ".join(points) + "}"


def runtime_stage_style(stage: str) -> str:
    if stage == "psl":
        return "draw=black,fill=black"
    if stage == "tbc":
        return "draw=black,fill=white,pattern=grid,pattern color=black"
    if stage == "abduction":
        return "draw=black,fill=white,pattern=crosshatch,pattern color=black"
    raise ValueError(f"unknown runtime stage: {stage}")


def summary_box_lines(rows: list[dict], profiles: list[dict]) -> list[str]:
    solved_count = len(profiles)
    total_count = len(rows)
    direct_solved = sum(1 for r in rows if truthy(r.get("direct_goal_proved")) and is_clean_proof(r))
    tbc_round_solved = sum(
        1 for r in rows
        if truthy(r.get("original_goal_proved_by_tbc")) and not truthy(r.get("direct_goal_proved")) and is_clean_proof(r)
    )
    abduction_solved = sum(1 for r in rows if truthy(r.get("abduction_solved")) and is_clean_proof(r))
    handed_to_abduction = sum(1 for r in rows if truthy(r.get("abduction_invoked")))

    lines = [
        rf"Solved problems shown: {solved_count}/{total_count}",
        rf"Solved directly: {direct_solved}; solved in TBC rounds: {tbc_round_solved}",
        rf"Handed to Abduction: {handed_to_abduction}; solved by Abduction: {abduction_solved}",
        rf"Avg. initial direct time: {fmt_num(mean([p['direct'] for p in profiles]))}\,s",
        rf"Avg. TBC-only time: {fmt_num(mean([p['tbc_only'] for p in profiles]))}\,s",
        rf"Avg. Abduction time: {fmt_num(mean([p['abduction'] for p in profiles]))}\,s",
        rf"Avg. total time: {fmt_num(mean([p['total'] for p in profiles]))}\,s",
        rf"Avg. generated conjectures: {fmt_num(mean([p['generated'] for p in profiles]))}",
        rf"Avg. proved template lemmas: {fmt_num(mean([p['proved_lemmas'] for p in profiles]))}",
    ]
    return lines


def write_runtime_profile(path: Path, benchmark: str, rows: list[dict], profiles: list[dict]) -> None:
    n = len(profiles)
    if n == 0:
        path.write_text(
            "% No solved problems for this benchmark/method combination.\n",
            encoding="utf-8",
        )
        return

    direct = [p["direct"] for p in profiles]
    tbc_only = [p["tbc_only"] for p in profiles]
    abduction = [p["abduction"] for p in profiles]
    total = [p["total"] for p in profiles]
    ymax = max(total)
    ymax = max(1.0, ymax * 1.10)
    lines: list[str] = []
    lines.append(r"% Requires: \usetikzlibrary{patterns}")
    lines.append(r"\begin{tikzpicture}")
    lines.append(r"\begin{axis}[")
    lines.append(r"width=0.96\linewidth,")
    lines.append(r"height=0.56\linewidth,")
    lines.append(rf"title={{Runtime decomposition of Combo Prover ({tex_escape(benchmark)})}},")
    lines.append(r"xlabel={Solved-problem rank (sorted by total runtime)},")
    lines.append(r"ylabel={Runtime (s)},")
    lines.append(r"xmin=0.5,")
    lines.append(rf"xmax={n + 0.5},")
    lines.append(r"ymin=0,")
    lines.append(rf"ymax={ymax:.6f},")
    lines.append(r"grid=both,")
    lines.append(r"xtick distance=1,")
    lines.append(r"minor x tick num=1,")
    lines.append(r"minor y tick num=1,")
    lines.append(r"major grid style={draw=black!18,line width=0.25pt},")
    lines.append(r"minor grid style={draw=black!8,line width=0.15pt},")
    lines.append(r"tick align=outside,")
    lines.append(r"axis line style={black},")
    lines.append(r"stack plots=y,")
    lines.append(r"area style,")
    lines.append(r"const plot,")
    lines.append(r"clip=false,")
    lines.append(r"legend style={at={(0.02,0.98)},anchor=north west,draw=black,fill=white,fill opacity=0.92,text opacity=1,rounded corners=1pt,font=\scriptsize},")
    lines.append(r"legend cell align=left,")
    lines.append(r"]")

    lines.append(rf"\addplot+[{runtime_stage_style('psl')}] coordinates {coordinates(direct)} \closedcycle;")
    lines.append(r"\addlegendentry{PSL/direct}")
    lines.append(rf"\addplot+[{runtime_stage_style('tbc')}] coordinates {coordinates(tbc_only)} \closedcycle;")
    lines.append(r"\addlegendentry{TBC}")
    lines.append(rf"\addplot+[{runtime_stage_style('abduction')}] coordinates {coordinates(abduction)} \closedcycle;")
    lines.append(r"\addlegendentry{Abduction}")
    lines.append(r"\end{axis}")
    lines.append(r"\end{tikzpicture}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("csvs", nargs="*", type=Path, help="Explicit tbc_seed_preprocessing_statistics.csv files.")
    parser.add_argument("--results-root", type=Path, default=None, help="Root directory under which benchmark result directories live.")
    parser.add_argument("--out", type=Path, required=True, help="Output directory for generated .tex files.")
    parser.add_argument("--benchmark", action="append", default=[], help="Benchmark name to generate. Repeatable. Defaults to all benchmarks found.")
    parser.add_argument("--method", default="preprocessed_abduction", help="Method to visualize. Default: preprocessed_abduction.")
    args = parser.parse_args()

    csvs = discover_csvs(args.results_root, args.csvs)
    if not csvs:
        raise RuntimeError("No tbc_seed_preprocessing_statistics.csv files found.")

    rows = read_rows(csvs)
    rows = filter_rows(rows, args.method, None)
    if not rows:
        raise RuntimeError(f"No rows found for method {args.method!r}.")

    out_dir = method_output_dir(args.out.resolve(), args.method)
    out_dir.mkdir(parents=True, exist_ok=True)

    benchmarks = args.benchmark or distinct_benchmarks(rows)
    for benchmark in benchmarks:
        bench_rows = filter_rows(rows, args.method, benchmark)
        if not bench_rows:
            print(f"warning: no TBC-seed preprocessing rows for benchmark {benchmark}; skipping")
            continue
        profiles = solved_profiles(bench_rows)
        out_file = out_dir / f"tbc_seed_runtime_profile_{benchmark}.tex"
        write_runtime_profile(out_file, benchmark, bench_rows, profiles)
        print(f"wrote {out_file}")


if __name__ == "__main__":
    main()
