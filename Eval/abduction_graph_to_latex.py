#!/usr/bin/env python3
"""Generate PGFPlots figures for AbductionGraph sharing statistics.

Input: one or more abduction_statistics.csv files produced by the evaluation
scripts.  The ML side emits graph-sharing metrics once per top-level
AbductionProver loop.  This script generates one family of figures per benchmark
found, unless one or more --benchmark options are passed.

This script is intentionally limited to AbductionGraph representation metrics:
node/edge growth, node reuse, child-node sharing, indegree, and SCC structure.
Generic contributive-node-loop metrics belong in abduction_statistics_to_latex.py.
Decremental-conjecturing metrics belong in abduction_decremental_to_latex.py.

The figures are meant to support the paper claim that AbductionGraph avoids the
hypothetical tree blow-up by sharing equivalent child nodes and by representing
cyclic dependencies directly.
"""

from __future__ import annotations

import argparse
import csv
import math
from collections import defaultdict
from pathlib import Path
from typing import Callable, Iterable, Optional


def truthy(x: object) -> bool:
    return str(x).strip().lower() in {"1", "true", "yes", "y", "ok", "proved", "success"}



def title_with_benchmark(title: str, benchmark: str) -> str:
    return f"{title} ({benchmark})" if benchmark else title


def outcome_group(rows: list[dict]) -> str:
    return "proved" if any(is_clean_proof(r) for r in rows) else "unproved"


def outcome_style(outcome: str) -> tuple[str, str, str, str]:
    if outcome == "proved":
        return ("proved", "blue", "*", "solid")
    return ("unproved", "red", "square*", "dashed")


def to_int(x: object, default: int = 0) -> int:
    try:
        text = str(x).strip()
        if text == "":
            return default
        return int(float(text))
    except Exception:
        return default


def to_float(x: object, default: float = 0.0) -> float:
    try:
        text = str(x).strip()
        if text == "":
            return default
        return float(text)
    except Exception:
        return default


def discover_csvs(results_root: Optional[Path], explicit_csvs: list[Path]) -> list[Path]:
    csvs: list[Path] = []
    for p in explicit_csvs:
        if not p.exists():
            raise FileNotFoundError(p)
        csvs.append(p)
    if results_root:
        if results_root.is_file():
            csvs.append(results_root)
        elif results_root.is_dir():
            csvs.extend(sorted(results_root.rglob("abduction_statistics.csv")))
    out: list[Path] = []
    seen = set()
    for p in csvs:
        q = p.resolve()
        if q in seen:
            continue
        seen.add(q)
        out.append(p)
    return out


def read_rows(csvs: Iterable[Path]) -> list[dict]:
    rows: list[dict] = []
    for path in csvs:
        with path.open(newline="", encoding="utf-8") as f:
            for raw in csv.DictReader(f):
                row = dict(raw)
                row["source_csv"] = str(path)
                row["benchmark"] = (row.get("benchmark") or path.parent.name).strip() or path.parent.name
                rows.append(row)
    return rows


def distinct_benchmarks(rows: Iterable[dict]) -> list[str]:
    return sorted({str(row.get("benchmark", "")).strip() for row in rows if str(row.get("benchmark", "")).strip()})


def filter_rows_by_method(rows: list[dict], method: str) -> list[dict]:
    wanted = str(method or "").strip()
    if wanted in {"", "all"}:
        return rows
    return [row for row in rows if str(row.get("method", "")).strip() == wanted]


def method_output_dir(base: Path, method: str) -> Path:
    wanted = str(method or "").strip()
    if wanted in {"", "abduction", "all"}:
        return base
    safe = "".join(ch if ch.isalnum() or ch in {"-", "_"} else "_" for ch in wanted)
    return base / safe


def is_clean_proof(row: dict) -> bool:
    status = str(row.get("status", "")).strip().lower()
    proof_text = str(row.get("proof_found", "")).strip()
    if proof_text:
        return truthy(proof_text) and status in {"ok", "proved", "success"}
    return status in {"proved", "success"}


def status_group(rows: list[dict]) -> str:
    return outcome_group(rows)


def actual_loop_rows(rows: list[dict]) -> list[dict]:
    return [r for r in rows if r.get("loop_kind") == "loop" and to_int(r.get("loop_index")) > 0]


def group_problem_rows(rows: list[dict]) -> dict[tuple[str, str], list[dict]]:
    grouped: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for row in rows:
        grouped[(str(row.get("benchmark", "")), str(row.get("target_id", "")))].append(row)
    for key in grouped:
        grouped[key].sort(key=lambda r: to_int(r.get("loop_index")))
    return dict(grouped)


def fmt_num(x: float) -> str:
    if abs(x - round(x)) < 1e-9:
        return str(int(round(x)))
    return f"{x:.6g}"


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


def log_minor_y_ticks(ymin: float, ymax: float) -> str:
    if ymax <= 1.0:
        return "{}"
    lo_exp = int(math.floor(math.log10(max(ymin, 1e-12))))
    hi_exp = int(math.ceil(math.log10(max(ymax, 1.0))))
    ticks: list[float] = []
    for exp in range(lo_exp, hi_exp + 1):
        base = 10.0 ** exp
        for m in range(2, 10):
            tick = float(m) * base
            if ymin < tick < ymax:
                ticks.append(tick)
    return "{" + ",".join(fmt_num(t) for t in ticks) + "}"


def pgf_coordinates(points: Iterable[tuple[float, float]]) -> str:
    return "{" + " ".join(f"({fmt_num(x)},{fmt_num(y)})" for x, y in points) + "}"


def make_axis_begin(
    title: str,
    ylabel: str,
    xmax: float,
    ymax: float,
    *,
    ymin: float = 0.0,
    log_y: bool = False,
    legend_pos: str = "north east",
) -> list[str]:
    xmax = max(1.0, xmax)
    ymin = 1.0 if log_y else ymin
    ymax = max(ymin + 1e-9, ymax)
    options = [
        f"title={{{tex_escape(title)}}},",
        r"xlabel={Top-level loop round},",
        f"ylabel={{{tex_escape(ylabel)}}},",
        r"width=0.95\linewidth,",
        r"height=0.62\linewidth,",
        r"grid=both,",
        r"minor grid style={draw=gray!24,line width=0.15pt},",
        r"major grid style={draw=gray!42,line width=0.25pt},",
        r"minor x tick num=1,",
        r"minor y tick num=9," if log_y else r"minor y tick num=3,",
        r"legend cell align=left,",
        f"legend pos={legend_pos},",
        r"legend style={draw=black,fill=white,fill opacity=0.85,text opacity=1,rounded corners=1pt},",
        r"tick align=outside,",
        r"every axis plot/.append style={line width=1.0pt},",
        r"enlarge x limits=false,",
        f"xmin=1, xmax={fmt_num(xmax)},",
        f"ymin={fmt_num(ymin)}, ymax={fmt_num(ymax)},",
    ]
    if xmax <= 30:
        options.append(r"xtick distance=1,")
    if log_y:
        options.extend([
            r"ymode=log,",
            r"log basis y=10,",
            r"unbounded coords=discard,",
            r"yminorgrids=true,",
            r"ytick={1,10,100,1000,10000,100000,1000000},",
            f"minor ytick={log_minor_y_ticks(ymin, ymax)},",
        ])
    return [r"\begin{tikzpicture}", r"\begin{axis}[", *options, r"]"]


def write_line_graph(
    groups: dict[tuple[str, str], list[dict]],
    out_path: Path,
    *,
    value_of_row: Callable[[dict], Optional[float]],
    title: str,
    ylabel: str,
    log_y: bool = False,
    ymax_min: float = 1.0,
    legend_pos: str = "north east",
) -> None:
    series: list[tuple[str, str, str, list[tuple[float, float]]]] = []
    xmax = 1.0
    ymax = ymax_min

    for (benchmark, target_id), rows in sorted(groups.items()):
        loops = actual_loop_rows(rows)
        points: list[tuple[float, float]] = []
        for r in loops:
            x = to_int(r.get("loop_index"))
            y = value_of_row(r)
            if y is None:
                continue
            if log_y and y <= 0.0:
                continue
            points.append((float(x), float(y)))
            xmax = max(xmax, float(x))
            ymax = max(ymax, float(y))
        if points:
            series.append((benchmark, target_id, status_group(rows), points))

    if not series:
        out_path.write_text("% No AbductionGraph data found.\n", encoding="utf-8")
        return

    lines = make_axis_begin(title, ylabel, xmax, ymax * (1.08 if ymax > 0 else 1.0), log_y=log_y, legend_pos=legend_pos)

    # Only two legend entries: no per-problem labels.
    for _label, colour, _mark, style in [outcome_style("proved"), outcome_style("unproved")]:
        lines.append(rf"\addlegendimage{{{colour},{style},line width=1.0pt}}")
        lines.append(rf"\addlegendentry{{{_label}}}")

    for _benchmark, _target_id, status, points in series:
        _label, colour, _mark, style = outcome_style(status)
        if len(points) == 1:
            single_mark = "+" if status == "proved" else "x"
            lines.append(
                rf"\addplot[{colour},only marks,mark={single_mark},mark size=1.7pt,line width=0.95pt,opacity=1.0] coordinates {pgf_coordinates(points)};"
            )
        else:
            lines.append(
                rf"\addplot[{colour},{style},no marks,line width=0.95pt,opacity=0.72] coordinates {pgf_coordinates(points)};"
            )
    lines.extend([r"\end{axis}", r"\end{tikzpicture}", ""])
    out_path.write_text("\n".join(lines), encoding="utf-8")




def metric_value(row: dict, key: str) -> Optional[float]:
    text = str(row.get(key, "")).strip()
    if text == "":
        return None
    return to_float(text)


def percent_metric_value(row: dict, key: str) -> Optional[float]:
    value = metric_value(row, key)
    if value is None:
        return None
    return 100.0 * value

def write_notes(out_path: Path, benchmark: str) -> None:
    text = f"""AbductionGraph figure notes for benchmark {benchmark or '<all>'}.

These plots use abduction_statistics.csv.  The ML instrumentation records cheap
node/edge creation and reuse counters online inside synchronized AbductionGraph
updates, then records graph-level snapshots at the end of each top-level loop.
All x-axes are one-based top-level loop rounds: round 1 is the first completed
iteration of the main AbductionProver loop, not the initial root-only graph.

Counter plots:
- graph_nodes counts the full implementation graph: OR-nodes, AND-nodes, and
  OR-to-AND edge-nodes.  graph_or_nodes, graph_and_nodes, and
  graph_or2and_edge_nodes show the three node categories separately.
- graph_node_reuse_rate, graph_ornode_reuse_rate, and graph_andnode_reuse_rate
  show cumulative reuse rates for all node kinds, logical OR-subgoals, and
  AND-decomposition nodes separately.

Structural plots:
- graph_avg_indegree and graph_largest_scc_size are computed over the full
  implementation graph, including OR-nodes, AND-nodes, and OR-to-AND edge nodes.
- graph_or_projected_* is computed over the OR-projection: parent OR -> child OR
  whenever the full graph contains parent OR -> edge-node -> AND-node -> child OR.
  This is the cleanest structural view of logical subgoal sharing.
- graph_and_projected_* is computed over the AND-projection: parent AND -> child
  AND whenever the full graph contains parent AND -> OR -> edge-node -> child AND.
  This is mainly a diagnostic view of decomposition-event sharing.
- Projected edge-count plots are intentionally not generated by default: they are
  easy to misread, and zero-valued early rounds disappear on logarithmic axes.
"""
    out_path.write_text(text, encoding="utf-8")


def write_figures_for_benchmark(rows: list[dict], out_dir: Path, benchmark: str) -> bool:
    rows = [r for r in rows if str(r.get("benchmark", "")) == benchmark]
    rows = [r for r in rows if str(r.get("graph_nodes", "")).strip() != ""]
    if not rows:
        print(f"No AbductionGraph metric rows found for benchmark {benchmark}; skipping.")
        return False

    groups = group_problem_rows(rows)
    suffix = f"_{benchmark}" if benchmark else ""

    count_specs = [
        ("abduction_graph_nodes_by_top_loop", "Full implementation-graph nodes by top-level loop", "OR+AND+edge nodes", "graph_nodes"),
        ("abduction_graph_ornodes_by_top_loop", "OR-nodes by top-level loop", "OR-nodes", "graph_or_nodes"),
        ("abduction_graph_andnodes_by_top_loop", "AND-nodes by top-level loop", "AND-nodes", "graph_and_nodes"),
        ("abduction_graph_or2and_edge_nodes_by_top_loop", "OR-to-AND edge-nodes by top-level loop", "OR-to-AND edge-nodes", "graph_or2and_edge_nodes"),
    ]
    for filename, title, ylabel, column in count_specs:
        write_line_graph(
            groups,
            out_dir / f"{filename}{suffix}.tex",
            value_of_row=lambda r, column=column: metric_value(r, column),
            title=title_with_benchmark(title, benchmark),
            ylabel=ylabel,
            log_y=True,
            legend_pos="north west",
        )

    reuse_specs = [
        ("abduction_graph_node_reuse_rate_by_top_loop", "All-node reuse rate in AbductionGraph", "All-node reuse rate (%)", "graph_node_reuse_rate"),
        ("abduction_graph_ornode_reuse_rate_by_top_loop", "OR-node reuse rate in AbductionGraph", "OR-node reuse rate (%)", "graph_ornode_reuse_rate"),
        ("abduction_graph_andnode_reuse_rate_by_top_loop", "AND-node reuse rate in AbductionGraph", "AND-node reuse rate (%)", "graph_andnode_reuse_rate"),
    ]
    for filename, title, ylabel, column in reuse_specs:
        write_line_graph(
            groups,
            out_dir / f"{filename}{suffix}.tex",
            value_of_row=lambda r, column=column: percent_metric_value(r, column),
            title=title_with_benchmark(title, benchmark),
            ylabel=ylabel,
            log_y=False,
            ymax_min=100.0,
            legend_pos="south east",
        )

    structural_specs = [
        ("abduction_graph_or_projected_avg_indegree_by_top_loop", "Average indegree in OR-projected graph", "OR-projected average indegree", "graph_or_projected_avg_indegree", False),
        ("abduction_graph_and_projected_avg_indegree_by_top_loop", "Average indegree in AND-projected graph", "AND-projected average indegree", "graph_and_projected_avg_indegree", False),
        ("abduction_graph_largest_scc_by_top_loop", "Largest SCC in full AbductionGraph", "Largest SCC size", "graph_largest_scc_size", True),
        ("abduction_graph_or_projected_largest_scc_by_top_loop", "Largest SCC in OR-projected graph", "OR-projected largest SCC size", "graph_or_projected_largest_scc_size", True),
        ("abduction_graph_and_projected_largest_scc_by_top_loop", "Largest SCC in AND-projected graph", "AND-projected largest SCC size", "graph_and_projected_largest_scc_size", True),
    ]
    for filename, title, ylabel, column, log_y in structural_specs:
        write_line_graph(
            groups,
            out_dir / f"{filename}{suffix}.tex",
            value_of_row=lambda r, column=column: metric_value(r, column),
            title=title_with_benchmark(title, benchmark),
            ylabel=ylabel,
            log_y=log_y,
            ymax_min=1.0,
            legend_pos="north west",
        )
    write_notes(out_dir / f"abduction_graph_figures{suffix}_notes.txt", benchmark)
    return True

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", nargs="*", type=Path, help="Explicit abduction_statistics.csv files")
    parser.add_argument("--results-root", type=Path, default=None)
    parser.add_argument(
        "--benchmark",
        action="append",
        default=[],
        help="Generate figures for this benchmark. Can be passed multiple times. If omitted, figures are generated separately for every benchmark found.",
    )
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument(
        "--method",
        default="abduction",
        help="Method to plot from abduction_statistics.csv. Defaults to pure 'abduction'. Use 'preprocessed_abduction' for the Abduction phase after TBC seeding, or 'all' only for ad-hoc diagnostics.",
    )
    args = parser.parse_args()

    csvs = discover_csvs(args.results_root, args.csv)
    if not csvs:
        print("No abduction_statistics.csv files found; skipping AbductionGraph figures.")
        return

    rows = filter_rows_by_method(read_rows(csvs), args.method)
    benchmarks = list(args.benchmark) if args.benchmark else distinct_benchmarks(rows)
    if not benchmarks:
        print("No benchmark names found in AbductionGraph statistics; skipping.")
        return

    out_dir = method_output_dir(args.out, args.method)
    out_dir.mkdir(parents=True, exist_ok=True)
    generated = 0
    for benchmark in benchmarks:
        if write_figures_for_benchmark(rows, out_dir, benchmark):
            generated += 1

    if generated == 0:
        print("No AbductionGraph metric rows found for the selected benchmarks; skipping.")
    else:
        print(f"Generated AbductionGraph LaTeX for method={args.method!r}, {generated} benchmark(s) in: {out_dir}")


if __name__ == "__main__":
    main()
