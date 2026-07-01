#!/usr/bin/env python3
"""
Generate paper-facing figures for decremental conjecturing statistics.

Input: one or more abduction_decremental_statistics.csv files produced by the
evaluation scripts.  The expected CSV is the round-level v12 format: one row per
decremental round per parent OR-node, with columns such as actual_proof_attempts
and attempted_depth_max.

This script is intentionally limited to decremental-conjecturing metrics.  It
generates one family of figures per benchmark found, unless one or more
--benchmark options are passed.  Generic contributive-node-loop metrics belong
in abduction_statistics_to_latex.py.  AbductionGraph sharing metrics belong in
abduction_graph_to_latex.py.
"""

from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path
from typing import DefaultDict, Dict, Iterable, List, Tuple


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



def title_with_benchmark(title: str, benchmark: str) -> str:
    return f"{title} ({benchmark})" if benchmark else title

def to_int(value: object, default: int = 0) -> int:
    if value is None:
        return default
    text = str(value).strip()
    if text == "":
        return default
    try:
        return int(float(text))
    except ValueError:
        return default


def truthy(value: object) -> bool:
    return str(value).strip().lower() in {"1", "true", "yes", "ok", "proved"}


def discover_csvs(results_root: Path | None, explicit_csvs: Iterable[Path]) -> list[Path]:
    csvs: list[Path] = []
    for p in explicit_csvs:
        csvs.append(p)
    if results_root:
        if results_root.is_file():
            csvs.append(results_root)
        elif results_root.is_dir():
            csvs.extend(sorted(results_root.rglob("abduction_decremental_statistics.csv")))
    unique: list[Path] = []
    seen = set()
    for p in csvs:
        q = p.resolve()
        if q in seen:
            continue
        if not p.exists():
            raise FileNotFoundError(p)
        seen.add(q)
        unique.append(p)
    return unique


def read_rows(csvs: Iterable[Path]) -> list[dict]:
    rows: list[dict] = []
    for path in csvs:
        with path.open(newline="", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                row = dict(row)
                row.setdefault("source_csv", str(path))
                row["benchmark"] = (row.get("benchmark") or path.parent.name).strip() or path.parent.name
                rows.append(row)
    return rows


def distinct_benchmarks(rows: Iterable[dict]) -> list[str]:
    return sorted({str(row.get("benchmark", "")).strip() for row in rows if str(row.get("benchmark", "")).strip()})


def target_id(row: dict) -> str:
    return (
        str(row.get("target_id") or "").strip()
        or str(row.get("target_index") or "").strip()
        or Path(str(row.get("source_csv", "unknown"))).stem
    )


def is_proved(row: dict) -> bool:
    """Return True only for cleanly solved rows.

    Older CSV files can contain status=timeout together with proof_found=True
    when a .proof file was written just before the evaluator killed Isabelle.
    Those rows must remain unproved in paper-facing plots.
    """
    status = str(row.get("status", "")).strip().lower()
    proof_text = str(row.get("proof_found", "")).strip()

    if proof_text:
        return truthy(proof_text) and status in {"ok", "proved", "success"}

    return status in {"proved", "success"}


def filter_rows(rows: list[dict], benchmark: str) -> list[dict]:
    if not benchmark:
        return rows
    return [row for row in rows if str(row.get("benchmark", "")) == benchmark]


SeriesMap = Dict[str, Dict[int, float]]
StatusMap = Dict[str, bool]


def total_attempts_by_loop(rows: list[dict]) -> tuple[SeriesMap, StatusMap]:
    series: DefaultDict[str, DefaultDict[int, float]] = defaultdict(lambda: defaultdict(float))
    statuses: StatusMap = {}
    for row in rows:
        tid = target_id(row)
        loop = to_int(row.get("top_loop_index"))
        if loop <= 0:
            continue
        series[tid][loop] += to_int(row.get("actual_proof_attempts"))
        statuses[tid] = statuses.get(tid, False) or is_proved(row)
    return {k: dict(v) for k, v in series.items()}, statuses


def max_attempts_per_parent_by_loop(rows: list[dict]) -> tuple[SeriesMap, StatusMap]:
    per_parent: DefaultDict[tuple[str, int], DefaultDict[str, int]] = defaultdict(lambda: defaultdict(int))
    statuses: StatusMap = {}
    for row in rows:
        tid = target_id(row)
        loop = to_int(row.get("top_loop_index"))
        if loop <= 0:
            continue
        parent = str(row.get("parent_or_name", "")) or "<unknown parent>"
        per_parent[(tid, loop)][parent] += to_int(row.get("actual_proof_attempts"))
        statuses[tid] = statuses.get(tid, False) or is_proved(row)

    series: DefaultDict[str, Dict[int, float]] = defaultdict(dict)
    for (tid, loop), parent_counts in per_parent.items():
        vals = list(parent_counts.values())
        if vals:
            series[tid][loop] = float(max(vals))
    return {k: dict(v) for k, v in series.items()}, statuses


def max_depth_by_loop(rows: list[dict]) -> tuple[SeriesMap, StatusMap]:
    series: DefaultDict[str, DefaultDict[int, float]] = defaultdict(lambda: defaultdict(float))
    statuses: StatusMap = {}
    for row in rows:
        tid = target_id(row)
        loop = to_int(row.get("top_loop_index"))
        if loop <= 0:
            continue
        attempts = to_int(row.get("actual_proof_attempts"))
        depth = to_int(row.get("attempted_depth_max"))
        # If no candidate set was actually tried, attempted_depth_max is just 0
        # by convention.  Keeping 0 is useful for showing that this top-level
        # round did not go deeper than the initial layer.
        if attempts > 0:
            series[tid][loop] = max(series[tid][loop], float(depth))
        else:
            series[tid][loop] = max(series[tid][loop], 0.0)
        statuses[tid] = statuses.get(tid, False) or is_proved(row)
    return {k: dict(v) for k, v in series.items()}, statuses




def row_int_with_fallback(row: dict, primary: str, fallback: str) -> int:
    if primary in row and str(row.get(primary, "")).strip() != "":
        return to_int(row.get(primary))
    return to_int(row.get(fallback))


def decremental_exact_duplicate_hit_rate_by_loop(rows: list[dict]) -> tuple[SeriesMap, StatusMap]:
    """
    For each target and top-level loop, compute:
      exact duplicate hits / (exact duplicate hits + actual proof attempts).

    This mirrors a strict cache-hit rate: only exact already-checked conjecture
    sets count as hits.  Failed-subsumption skips are not counted here.
    """
    hits: DefaultDict[tuple[str, int], int] = defaultdict(int)
    misses: DefaultDict[tuple[str, int], int] = defaultdict(int)
    statuses: StatusMap = {}
    for row in rows:
        tid = target_id(row)
        loop = to_int(row.get("top_loop_index"))
        if loop <= 0:
            continue
        key = (tid, loop)
        hits[key] += row_int_with_fallback(row, "decremental_exact_duplicate_hits", "skipped_duplicate_sets")
        misses[key] += row_int_with_fallback(row, "decremental_cache_misses", "actual_proof_attempts")
        statuses[tid] = statuses.get(tid, False) or is_proved(row)

    series: DefaultDict[str, Dict[int, float]] = defaultdict(dict)
    for (tid, loop), h in hits.items():
        denom = h + misses[(tid, loop)]
        series[tid][loop] = (float(h) / float(denom)) if denom > 0 else 0.0
    return {k: dict(v) for k, v in series.items()}, statuses


def decremental_avoidance_rate_by_loop(rows: list[dict]) -> tuple[SeriesMap, StatusMap]:
    """
    For each target and top-level loop, compute:
      avoided attempts / selected conjecture sets,
    where avoided attempts include both exact duplicate hits and failed-set
    subsumption hits.
    """
    avoided: DefaultDict[tuple[str, int], int] = defaultdict(int)
    selected: DefaultDict[tuple[str, int], int] = defaultdict(int)
    statuses: StatusMap = {}
    for row in rows:
        tid = target_id(row)
        loop = to_int(row.get("top_loop_index"))
        if loop <= 0:
            continue
        key = (tid, loop)
        exact_hits = row_int_with_fallback(row, "decremental_exact_duplicate_hits", "skipped_duplicate_sets")
        subsumption_hits = row_int_with_fallback(row, "decremental_failed_subsumption_hits", "skipped_subsumed_sets")
        avoided[key] += exact_hits + subsumption_hits
        selected[key] += to_int(row.get("selected_sets"))
        statuses[tid] = statuses.get(tid, False) or is_proved(row)

    series: DefaultDict[str, Dict[int, float]] = defaultdict(dict)
    for (tid, loop), h in avoided.items():
        denom = selected[(tid, loop)]
        series[tid][loop] = (float(h) / float(denom)) if denom > 0 else 0.0
    return {k: dict(v) for k, v in series.items()}, statuses



def avoided_attempts_by_loop(rows: list[dict]) -> tuple[SeriesMap, StatusMap]:
    """
    For each target and top-level loop, count candidate sets whose expensive
    proof attempt was avoided either by exact duplicate detection or by failed
    set subsumption.
    """
    series: DefaultDict[str, DefaultDict[int, float]] = defaultdict(lambda: defaultdict(float))
    statuses: StatusMap = {}
    for row in rows:
        tid = target_id(row)
        loop = to_int(row.get("top_loop_index"))
        if loop <= 0:
            continue
        exact_hits = row_int_with_fallback(row, "decremental_exact_duplicate_hits", "skipped_duplicate_sets")
        subsumption_hits = row_int_with_fallback(row, "decremental_failed_subsumption_hits", "skipped_subsumed_sets")
        series[tid][loop] += exact_hits + subsumption_hits
        statuses[tid] = statuses.get(tid, False) or is_proved(row)
    return {k: dict(v) for k, v in series.items()}, statuses


def max_xy(series: SeriesMap) -> tuple[int, float]:
    max_x = 1
    max_y = 0.0
    for points in series.values():
        if points:
            max_x = max(max_x, max(points))
            max_y = max(max_y, max(points.values()))
    return max_x, max_y


def data_tight_upper(max_y: float, *, padding: float = 1.03, cap: float | None = None) -> float:
    """Return a deliberately tight data-dependent upper axis bound.

    For these diagnostic plots, rounding to human-friendly values can still
    waste too much space, especially when the maximum is small.  Therefore the
    default is just a small multiplicative margin over the actual CSV maximum.
    """
    if max_y <= 0:
        result = 1.0
    else:
        result = max_y * padding
        # Avoid placing a non-zero maximum exactly at the frame boundary for
        # tiny integer-valued plots such as refinement depth.
        if result == max_y:
            result = max_y + 0.05
    if cap is not None:
        result = min(result, cap)
    return result


def y_max_for_axis(max_y: float, *, cap: float | None = None) -> float:
    return data_tight_upper(max_y, padding=1.03, cap=cap)


def y_max_for_log_axis(max_y: float, *, cap: float | None = None) -> float:
    # ymax must be strictly larger than ymin=1 on a log plot.
    result = data_tight_upper(max_y, padding=1.03, cap=cap)
    if cap is not None:
        result = min(result, cap)
    return max(result, 1.15)


def coordinates(points: Dict[int, float], *, positive_only: bool = False) -> str:
    pairs = []
    for x, y in sorted(points.items()):
        if positive_only and y <= 0:
            continue
        pairs.append(f"({x},{y:g})")
    return " ".join(pairs)


def write_line_figure(
    out_path: Path,
    *,
    series: SeriesMap,
    statuses: StatusMap,
    title: str,
    y_label: str,
    x_label: str = "Top-level loop round",
    fixed_ymax: float | None = None,
    ytick: str | None = None,
    log_y: bool = False,
    y_cap: float | None = None,
) -> None:
    if not series:
        out_path.write_text("% No decremental conjecturing data found.\n", encoding="utf-8")
        return

    max_x, max_y = max_xy(series)
    ymax = fixed_ymax if fixed_ymax is not None else (
        y_max_for_log_axis(max_y, cap=y_cap) if log_y else y_max_for_axis(max_y, cap=y_cap)
    )
    ymin = 1.0 if log_y else 0.0
    xtick = "{" + ",".join(str(i) for i in range(1, max_x + 1)) + "}" if max_x <= 30 else "\\empty"
    ytick_line = rf"  ytick={ytick}," if ytick is not None else None
    log_lines = [r"  ymode=log,", r"  log basis y=10,"] if log_y else []

    lines: list[str] = [
        r"\begin{tikzpicture}",
        r"\begin{axis}[%",
        r"  width=\linewidth,",
        r"  height=0.46\linewidth,",
        rf"  title={{{tex_escape(title)}}},",
        rf"  xlabel={{{tex_escape(x_label)}}},",
        rf"  ylabel={{{tex_escape(y_label)}}},",
        r"  xmin=1,",
        rf"  xmax={max_x},",
        rf"  ymin={ymin:g},",
        rf"  ymax={ymax:g},",
        *log_lines,
        *( [ytick_line] if ytick_line is not None else [] ),
        rf"  xtick={xtick},",
        r"  grid=both,",
        r"  minor grid style={draw=black!8,line width=0.15pt},",
        r"  major grid style={draw=black!18,line width=0.25pt},",
        r"  minor x tick num=1,",
        r"  minor y tick num=9," if log_y else r"  minor y tick num=3,",
        r"  legend style={at={(0.02,0.98)},anchor=north west,draw=black,fill=white,fill opacity=0.85,text opacity=1,rounded corners=1pt},",
        r"  legend cell align=left,",
        r"  tick align=outside,",
        r"  scaled y ticks=false,",
        r"]",
        r"\addlegendimage{blue,solid,line width=1.0pt}",
        r"\addlegendentry{proved}",
        r"\addlegendimage{red,dashed,line width=1.0pt}",
        r"\addlegendentry{unproved}",
    ]

    for tid in sorted(series):
        pts = series[tid]
        if not pts:
            continue
        proved = statuses.get(tid, False)
        style = "solid" if proved else "dashed"
        colour = "blue" if proved else "red"
        coords = coordinates(pts, positive_only=log_y)
        if coords == "":
            continue
        lines.append(
            rf"\addplot+[mark=none,forget plot,{style},{colour},line width=1.0pt,opacity=0.78] coordinates {{{coords}}};"
        )

    lines.extend([r"\end{axis}", r"\end{tikzpicture}", ""])
    out_path.write_text("\n".join(lines), encoding="utf-8")


def write_notes(out_path: Path, benchmark: str) -> None:
    text = f"""Decremental conjecturing figures for {benchmark or 'all benchmarks'}.

The CSV is round-level: one row corresponds to one decremental round for one parent OR-node.

actual_proof_attempts counts candidate conjecture sets that were actually submitted to
prove_ornode_assuming_andnode.  It does not include skipped duplicate sets or sets skipped
because they were already subsumed by a failed conjecture set.

Depth convention: the initial full conjecture set has depth 0.  When a new candidate set is
created by deleting one conjecture from an existing set, its depth is parent depth + 1.  If
the same conjecture set is reached through multiple paths in the refinement DAG, the ML code
keeps the maximum depth observed for that set.

The exact-duplicate hit rate is skipped_duplicate_sets / (skipped_duplicate_sets + actual_proof_attempts),
aggregated by target and top-level loop.  The broader avoidance rate is
(skipped_duplicate_sets + skipped_subsumed_sets) / selected_sets.  Count-like effort plots with very wide ranges use a
logarithmic y-axis; zero-valued points are omitted in those plots because PGFPlots cannot place
zero on a logarithmic axis.
"""
    out_path.write_text(text, encoding="utf-8")


def write_figures_for_benchmark(rows: list[dict], out_dir: Path, benchmark: str) -> bool:
    rows = filter_rows(rows, benchmark)
    if not rows:
        print(f"No decremental rows found for benchmark {benchmark}; skipping decremental figures.")
        return False

    total_series, total_statuses = total_attempts_by_loop(rows)
    max_parent_series, max_parent_statuses = max_attempts_per_parent_by_loop(rows)
    depth_series, depth_statuses = max_depth_by_loop(rows)
    exact_hit_rate_series, exact_hit_rate_statuses = decremental_exact_duplicate_hit_rate_by_loop(rows)
    avoidance_rate_series, avoidance_rate_statuses = decremental_avoidance_rate_by_loop(rows)
    avoided_attempts_series, avoided_attempts_statuses = avoided_attempts_by_loop(rows)

    suffix = f"_{benchmark}" if benchmark else ""
    write_line_figure(
        out_dir / f"abduction_decremental_total_attempts_by_top_loop{suffix}.tex",
        series=total_series,
        statuses=total_statuses,
        title=title_with_benchmark("Decremental conjecturing effort by top-level loop", benchmark),
        y_label="Total conjecture-set proof attempts",
        log_y=True,
    )
    write_line_figure(
        out_dir / f"abduction_decremental_max_attempts_per_parent_by_top_loop{suffix}.tex",
        series=max_parent_series,
        statuses=max_parent_statuses,
        title=title_with_benchmark("Maximum decremental effort per parent OR-node", benchmark),
        y_label="Maximum attempts per parent OR-node",
        log_y=True,
    )
    write_line_figure(
        out_dir / f"abduction_decremental_max_refinement_depth_by_top_loop{suffix}.tex",
        series=depth_series,
        statuses=depth_statuses,
        title=title_with_benchmark("Maximum refinement depth by top-level loop", benchmark),
        y_label="Maximum candidate-set depth",
    )
    write_line_figure(
        out_dir / f"abduction_decremental_avoided_attempts_by_top_loop{suffix}.tex",
        series=avoided_attempts_series,
        statuses=avoided_attempts_statuses,
        title=title_with_benchmark("Avoided decremental proof attempts by top-level loop", benchmark),
        y_label="Avoided proof attempts",
        log_y=True,
    )
    write_line_figure(
        out_dir / f"abduction_decremental_exact_duplicate_hit_rate_by_top_loop{suffix}.tex",
        series=exact_hit_rate_series,
        statuses=exact_hit_rate_statuses,
        title=title_with_benchmark("Exact duplicate avoidance in decremental conjecturing", benchmark),
        y_label="Exact duplicate hit rate",
        y_cap=1.0,
    )
    write_line_figure(
        out_dir / f"abduction_decremental_avoidance_rate_by_top_loop{suffix}.tex",
        series=avoidance_rate_series,
        statuses=avoidance_rate_statuses,
        title=title_with_benchmark("Avoidance rate in decremental conjecturing", benchmark),
        y_label="Avoided / selected candidate sets",
        y_cap=1.0,
    )
    write_notes(out_dir / f"abduction_decremental_figures{suffix}_notes.txt", benchmark)
    return True


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", nargs="*", type=Path)
    parser.add_argument("--results-root", type=Path, default=None)
    parser.add_argument("--out", type=Path, default=Path("latex/main"))
    parser.add_argument(
        "--benchmark",
        action="append",
        default=[],
        help="Generate figures for this benchmark. Can be passed multiple times. If omitted, figures are generated separately for every benchmark found.",
    )
    # Accepted for compatibility with the previous heatmap-oriented script.
    parser.add_argument("--phase", default=None)
    parser.add_argument("--style", default=None)
    parser.add_argument("--legacy-gray-name", action="store_true")
    parser.add_argument("--annotate", action="store_true")
    args = parser.parse_args()

    csvs = discover_csvs(args.results_root, args.csv)
    if not csvs:
        print("No abduction_decremental_statistics.csv found; skipping decremental figures.")
        return

    rows = read_rows(csvs)
    benchmarks = list(args.benchmark) if args.benchmark else distinct_benchmarks(rows)
    if not benchmarks:
        print("No benchmark names found in decremental statistics; skipping decremental figures.")
        return

    args.out.mkdir(parents=True, exist_ok=True)
    generated = 0
    for benchmark in benchmarks:
        if write_figures_for_benchmark(rows, args.out, benchmark):
            generated += 1

    if generated == 0:
        print("No decremental rows found for the selected benchmarks; skipping decremental figures.")
    else:
        print(f"Generated decremental conjecturing LaTeX for {generated} benchmark(s) in: {args.out}")


if __name__ == "__main__":
    main()
