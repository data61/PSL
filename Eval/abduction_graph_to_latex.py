#!/usr/bin/env python3
"""Generate PGFPlots figures for AbductionGraph sharing statistics.

Input: one or more abduction_statistics.csv files produced by the evaluation
scripts.  The ML side emits graph-sharing metrics once per top-level
AbductionProver loop.  This script generates one family of figures per benchmark
found, unless one or more --benchmark options are passed.

This script is primarily limited to AbductionGraph representation metrics:
node/edge growth, node reuse, child-node sharing, indegree, and SCC structure.
It also emits one paper-facing two-panel summary that pairs OR-node reuse
with the contributive-frontier ratio, because these two diagnostics are
intended to be discussed together in the paper.  Other generic
contributive-node-loop metrics belong in abduction_statistics_to_latex.py.
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
    proof_text = str(row.get("proof_found", "")).strip()
    if proof_text:
        return truthy(proof_text)
    status = str(row.get("status", "")).strip().lower()
    return status in {"ok", "proved", "success"}

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


def quantile(sorted_values: list[float], q: float) -> Optional[float]:
    if not sorted_values:
        return None
    if len(sorted_values) == 1:
        return sorted_values[0]
    pos = (len(sorted_values) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return sorted_values[lo]
    weight = pos - lo
    return sorted_values[lo] * (1.0 - weight) + sorted_values[hi] * weight


def trim_after_first_zero_worth(rows: list[dict]) -> list[dict]:
    """Keep rows up to and including the first worth_expanding = 0 row."""
    trimmed: list[dict] = []
    for row in rows:
        trimmed.append(row)
        if to_int(row.get("worth_expanding")) == 0:
            break
    return trimmed


def summary_quantile_series(
    groups: dict[tuple[str, str], list[dict]],
    *,
    value_of_row: Callable[[dict], Optional[float]],
    trim_after_zero: bool,
) -> tuple[
    dict[str, list[tuple[float, float]]],
    dict[str, list[tuple[float, float]]],
    dict[str, list[tuple[float, float]]],
    float,
    float,
]:
    by_status_loop: dict[str, dict[int, list[float]]] = {
        "proved": defaultdict(list),
        "unproved": defaultdict(list),
    }
    xmax = 1.0
    ymax = 100.0

    for (_benchmark, _target_id), rows in sorted(groups.items()):
        loops = actual_loop_rows(rows)
        if trim_after_zero:
            loops = trim_after_first_zero_worth(loops)
        status = outcome_group(rows)
        for row in loops:
            loop = to_int(row.get("loop_index"))
            value = value_of_row(row)
            if value is None:
                continue
            by_status_loop[status][loop].append(float(value))
            xmax = max(xmax, float(loop))
            ymax = max(ymax, float(value))

    median_series: dict[str, list[tuple[float, float]]] = {}
    q1_series: dict[str, list[tuple[float, float]]] = {}
    q3_series: dict[str, list[tuple[float, float]]] = {}

    for status in ["proved", "unproved"]:
        med_pts: list[tuple[float, float]] = []
        q1_pts: list[tuple[float, float]] = []
        q3_pts: list[tuple[float, float]] = []
        for loop in sorted(by_status_loop[status]):
            values = sorted(by_status_loop[status][loop])
            q1 = quantile(values, 0.25)
            med = quantile(values, 0.50)
            q3 = quantile(values, 0.75)
            if q1 is None or med is None or q3 is None:
                continue
            q1_pts.append((float(loop), q1))
            med_pts.append((float(loop), med))
            q3_pts.append((float(loop), q3))
        if med_pts:
            median_series[status] = med_pts
            q1_series[status] = q1_pts
            q3_series[status] = q3_pts

    return median_series, q1_series, q3_series, xmax, ymax


def write_summary_quantile_graph(
    groups: dict[tuple[str, str], list[dict]],
    out_path: Path,
    *,
    value_of_row: Callable[[dict], Optional[float]],
    title: str,
    ylabel: str,
    trim_after_zero: bool = False,
    extra_axis_options: Optional[list[str]] = None,
) -> None:
    median_series, q1_series, q3_series, xmax, ymax = summary_quantile_series(
        groups,
        value_of_row=value_of_row,
        trim_after_zero=trim_after_zero,
    )

    if not median_series:
        out_path.write_text("% No summary-quantile data found.\n", encoding="utf-8")
        return

    lines = make_axis_begin(
        title,
        ylabel,
        xmax,
        max(100.0, ymax),
        ymin=0.0,
        log_y=False,
        legend_pos="north west",
        extra_options=extra_axis_options,
    )

    for label, colour, _mark, style in [outcome_style("proved"), outcome_style("unproved")]:
        lines.append(rf"\addlegendimage{{{colour},{style},line width=1.25pt}}")
        lines.append(rf"\addlegendentry{{{label} median}}")

    for status in ["proved", "unproved"]:
        if status not in median_series:
            continue
        _label, colour, _mark, style = outcome_style(status)
        lines.append(rf"\addplot[{colour},{style},no marks,line width=0.65pt,opacity=0.34,forget plot] coordinates {pgf_coordinates(q1_series[status])};")
        lines.append(rf"\addplot[{colour},{style},no marks,line width=0.65pt,opacity=0.34,forget plot] coordinates {pgf_coordinates(q3_series[status])};")
        lines.append(rf"\addplot[{colour},{style},no marks,line width=1.25pt,opacity=0.95] coordinates {pgf_coordinates(median_series[status])};")

    lines.extend([r"\end{axis}", r"\end{tikzpicture}", ""])
    out_path.write_text("\n".join(lines), encoding="utf-8")


def make_axis_begin(
    title: str,
    ylabel: str,
    xmax: float,
    ymax: float,
    *,
    ymin: float = 0.0,
    log_y: bool = False,
    legend_pos: str = "north east",
    extra_options: Optional[list[str]] = None,
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
    if extra_options:
        options.extend(extra_options)
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

def expandable_ratio_value(row: dict) -> Optional[float]:
    raw = row.get("reachable_or_nodes")
    if raw is None or str(raw).strip() == "":
        raw = row.get("reachable_keys")
    reachable_or_nodes = to_int(raw)
    if reachable_or_nodes <= 0:
        return None
    return 100.0 * float(to_int(row.get("worth_expanding"))) / float(reachable_or_nodes)


def write_summary_quantile_panel(
    lines: list[str],
    *,
    median_series: dict[str, list[tuple[float, float]]],
    q1_series: dict[str, list[tuple[float, float]]],
    q3_series: dict[str, list[tuple[float, float]]],
    add_legend: bool,
) -> None:
    if add_legend:
        for label, colour, _mark, style in [outcome_style("proved"), outcome_style("unproved")]:
            lines.append(rf"\addlegendimage{{{colour},{style},line width=1.25pt}}")
            lines.append(rf"\addlegendentry{{{label} median}}")

    for status in ["proved", "unproved"]:
        if status not in median_series:
            continue
        _label, colour, _mark, style = outcome_style(status)
        lines.append(rf"\addplot[{colour},{style},no marks,line width=0.65pt,opacity=0.34,forget plot] coordinates {pgf_coordinates(q1_series[status])};")
        lines.append(rf"\addplot[{colour},{style},no marks,line width=0.65pt,opacity=0.34,forget plot] coordinates {pgf_coordinates(q3_series[status])};")
        lines.append(rf"\addplot[{colour},{style},no marks,line width=1.25pt,opacity=0.95] coordinates {pgf_coordinates(median_series[status])};")


def write_reuse_frontier_summary_groupplot(
    groups: dict[tuple[str, str], list[dict]],
    out_path: Path,
    *,
    benchmark: str,
) -> None:
    reuse_med, reuse_q1, reuse_q3, reuse_xmax, _reuse_ymax = summary_quantile_series(
        groups,
        value_of_row=lambda row: percent_metric_value(row, "graph_ornode_reuse_rate"),
        trim_after_zero=False,
    )
    frontier_med, frontier_q1, frontier_q3, frontier_xmax, _frontier_ymax = summary_quantile_series(
        groups,
        value_of_row=expandable_ratio_value,
        trim_after_zero=True,
    )

    if not reuse_med and not frontier_med:
        out_path.write_text("% No OR-node reuse/frontier summary data found.\n", encoding="utf-8")
        return

    xmax = max(reuse_xmax, frontier_xmax)
    xtick_line = r"  xtick distance=1," if xmax <= 30 else ""

    lines = [
        r"% Requires: \usepgfplotslibrary{groupplots}",
        r"\begin{tikzpicture}",
        r"\begin{groupplot}[",
        r"  group style={group size=2 by 1, horizontal sep=1.35cm},",
        r"  width=0.48\linewidth,",
        r"  height=0.42\linewidth,",
        r"  xlabel={Top-level loop round},",
        r"  ymin=0, ymax=100,",
        f"  xmin=1, xmax={fmt_num(xmax)},",
        r"  ytick={0,20,40,60,80,100},",
        r"  grid=both,",
        r"  minor grid style={draw=gray!24,line width=0.15pt},",
        r"  major grid style={draw=gray!42,line width=0.25pt},",
        r"  minor x tick num=1,",
        r"  minor y tick num=3,",
        r"  legend cell align=left,",
        r"  legend pos=north west,",
        r"  legend style={draw=black,fill=white,fill opacity=0.85,text opacity=1,rounded corners=1pt,font=\scriptsize},",
        r"  tick align=outside,",
        r"  every axis plot/.append style={line width=1.0pt},",
        r"  enlarge x limits=false,",
        r"  scaled y ticks=false,",
    ]
    if xtick_line:
        lines.append(xtick_line)
    lines.extend([
        r"]",
        rf"\nextgroupplot[title={{{tex_escape(title_with_benchmark('OR-node reuse summary', benchmark))}}}, ylabel={{OR-node reuse rate (\%)}}, ylabel style={{xshift=0.9em}}]",
    ])
    write_summary_quantile_panel(
        lines,
        median_series=reuse_med,
        q1_series=reuse_q1,
        q3_series=reuse_q3,
        add_legend=True,
    )
    lines.append(
        rf"\nextgroupplot[title={{{tex_escape(title_with_benchmark('Contributive-frontier summary', benchmark))}}}, ylabel={{Contributive OR-leaf ratio (\%)}}, ylabel style={{xshift=1.2em}}]"
    )
    write_summary_quantile_panel(
        lines,
        median_series=frontier_med,
        q1_series=frontier_q1,
        q3_series=frontier_q3,
        add_legend=False,
    )
    lines.extend([r"\end{groupplot}", r"\end{tikzpicture}", ""])
    out_path.write_text("\n".join(lines), encoding="utf-8")


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

Summary plots:
- Summary curves show the median per-loop value for proved and unproved runs.
  The two thinner curves around each median are the 25th- and 75th-percentile
  curves for the same group and loop.
- The two-panel paper-facing summary places OR-node reuse on the left and the
  contributive-frontier ratio on the right: the former describes structural
  sharing in AbductionGraph, while the latter describes how much of the
  root-reachable OR frontier remains expandable.

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

    write_summary_quantile_graph(
        groups,
        out_dir / f"abduction_graph_ornode_reuse_rate_summary_by_top_loop{suffix}.tex",
        value_of_row=lambda row: percent_metric_value(row, "graph_ornode_reuse_rate"),
        title=title_with_benchmark("OR-node reuse-rate summary", benchmark),
        ylabel="OR-node reuse rate (%)",
        trim_after_zero=False,
        extra_axis_options=[r"ytick={0,20,40,60,80,100},", r"scaled y ticks=false,"],
    )

    write_reuse_frontier_summary_groupplot(
        groups,
        out_dir / f"abduction_graph_reuse_frontier_summary_by_loop{suffix}.tex",
        benchmark=benchmark,
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
        help="Method to plot from abduction_statistics.csv. Defaults to pure 'abduction' (Pure AbductionProver). Use 'preprocessed_abduction' for the Combo Prover's Abduction phase after TBC seeding, or 'all' only for ad-hoc diagnostics.",
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
