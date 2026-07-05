#!/usr/bin/env python3
"""Generate PGFPlots figures for AbductionProver loop-level statistics.

Input: one or more abduction_statistics.csv files.
Output: LaTeX/PGFPlots .tex files for every benchmark found, unless one or more
--benchmark options are passed.

This script is intentionally limited to the generic top-level-loop statistics
that explain contributive-node focusing:

* contributive OR-leaf nodes (formerly worth_expanding),
* root-reachable OR-nodes (reachable_or_nodes),
* the ratio between contributive OR-leaves and root-reachable OR-nodes,
* refutation-cache hit rate,
* per-loop counterexample-filtering counts,
* per-loop Sledgehammer abduction-filtering counts, and
* aggregate filtering-funnel summaries,
* median/quantile summary curves for key rates,
* refutation-survival/abduction-retention correlation tables, and
* the first loop in which no contributive OR-leaf remains.

AbductionGraph sharing metrics belong in abduction_graph_to_latex.py.
Decremental-conjecturing metrics belong in abduction_decremental_to_latex.py.

The generated line plots intentionally do not include one legend entry per
problem: there can be about 50 problems, so individual legends obscure the plot.
Instead, blue solid lines mean proved problems and red dashed lines mean unproved problems.
Spaghetti plots use no per-loop markers; single-point series use an unfilled +/x marker so they remain visible.

For count plots, the y-axis is logarithmic by default.  Zero values cannot be
shown on a log axis, so zero contributive-node rows are omitted from the line
plot; the separate first-zero histogram records exactly where those zero rows
first occur.
"""

from __future__ import annotations

import argparse
import csv
import math
from collections import Counter, defaultdict
from pathlib import Path
from typing import Callable, Iterable, Optional


def truthy(x: object) -> bool:
    return str(x).strip().lower() in {"1", "true", "yes", "y"}



def title_with_benchmark(title: str, benchmark: str) -> str:
    return f"{title} ({benchmark})" if benchmark else title


def outcome_style(outcome: str) -> tuple[str, str, str, str]:
    if outcome == "proved":
        return ("proved", "blue", "*", "solid")
    return ("unproved", "red", "square*", "dashed")


def to_int(x: object, default: int = 0) -> int:
    try:
        return int(float(str(x).strip()))
    except Exception:
        return default


def to_float(x: object, default: float = 0.0) -> float:
    try:
        return float(str(x).strip())
    except Exception:
        return default


def discover_csvs(results_root: Optional[Path], explicit_csvs: list[Path]) -> list[Path]:
    csvs: list[Path] = []
    for p in explicit_csvs:
        if not p.exists():
            raise FileNotFoundError(f"No such Abduction statistics CSV: {p}")
        csvs.append(p)
    if results_root:
        if not results_root.exists():
            raise FileNotFoundError(f"No such results root: {results_root}")
        csvs.extend(sorted(results_root.rglob("abduction_statistics.csv")))

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


def actual_loop_rows(rows: list[dict]) -> list[dict]:
    return [r for r in rows if r.get("loop_kind") == "loop" and to_int(r.get("loop_index"), 0) > 0]


def is_clean_proof(row: dict) -> bool:
    """Return True when the summary CSV says the target was proved.

    The evaluator now validates completed Abduction proof artifacts before
    setting proof_found=True, so downstream plots should trust proof_found
    rather than reclassifying proved-but-process-abnormal rows as failures.
    """
    proof_text = str(row.get("proof_found", "")).strip()
    if proof_text:
        return truthy(proof_text)

    status = str(row.get("status", "")).strip().lower()
    return status in {"ok", "proved", "success"}

def outcome_group(rows: list[dict]) -> str:
    return "proved" if any(is_clean_proof(r) for r in rows) else "unproved"


def trim_after_first_zero_worth(rows: list[dict]) -> list[dict]:
    """Keep rows up to and including the first worth_expanding = 0 row.

    This makes old CSV files generated before the early-exit fix plot like the
    new behavior: once no worth-expanding node remains, later loop rows are not
    meaningful search progress.
    """
    trimmed: list[dict] = []
    for r in rows:
        trimmed.append(r)
        if to_int(r.get("worth_expanding")) == 0:
            break
    return trimmed


def group_problem_rows(rows: list[dict]) -> dict[tuple[str, str], list[dict]]:
    grouped: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for row in rows:
        grouped[(row.get("benchmark", ""), row.get("target_id", ""))].append(row)
    for key in grouped:
        grouped[key].sort(key=lambda r: to_int(r.get("loop_index"), 0))
    return grouped


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
    """Explicit minor ticks for log-y plots: 2..9 in each visible decade.

    PGFPlots' minor y tick num does not reliably create the desired
    logarithmic minor grid lines when we also specify major y ticks.  Therefore
    we explicitly request ticks at 2,3,...,9 times each power of ten.
    """
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

    return "{" + ",".join(fmt_num(tick) for tick in ticks) + "}"


def pgf_coordinates(points: Iterable[tuple[float, float]]) -> str:
    pts = " ".join(f"({fmt_num(x)},{fmt_num(y)})" for x, y in points)
    return "{" + pts + "}"


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


def pearson(xs: list[float], ys: list[float]) -> Optional[float]:
    n = len(xs)
    if n < 2 or n != len(ys):
        return None
    mx = sum(xs) / n
    my = sum(ys) / n
    dx = [x - mx for x in xs]
    dy = [y - my for y in ys]
    den_x = math.sqrt(sum(x * x for x in dx))
    den_y = math.sqrt(sum(y * y for y in dy))
    if den_x <= 0.0 or den_y <= 0.0:
        return None
    return sum(x * y for x, y in zip(dx, dy)) / (den_x * den_y)


def ranks(values: list[float]) -> list[float]:
    order = sorted(enumerate(values), key=lambda p: p[1])
    out = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and order[j][1] == order[i][1]:
            j += 1
        rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k][0]] = rank
        i = j
    return out


def spearman(xs: list[float], ys: list[float]) -> Optional[float]:
    if len(xs) < 2 or len(xs) != len(ys):
        return None
    return pearson(ranks(xs), ranks(ys))


def make_axis_begin(
    title: str,
    xlabel: str,
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
        f"xlabel={{{tex_escape(xlabel)}}},",
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
        (
            r"legend style={"
            r"draw=black,"
            r"fill=white,"
            r"fill opacity=0.85,"
            r"text opacity=1,"
            r"rounded corners=1pt"
            r"},"
        ),
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
            r"ytick={1,10,100,1000,10000,100000},",
            f"minor ytick={log_minor_y_ticks(ymin, ymax)},",
        ])

    if extra_options:
        options.extend(extra_options)

    return [
        r"\begin{tikzpicture}",
        r"\begin{axis}[",
        *options,
        r"]",
    ]


def write_line_graph(
    problem_groups: dict[tuple[str, str], list[dict]],
    out_path: Path,
    *,
    value_of_row: Callable[[dict], Optional[float]],
    title: str,
    ylabel: str,
    ymax_min: float = 1.0,
    log_y: bool = False,
    legend_pos: str = "north east",
    trim_after_zero: bool = True,
    extra_axis_options: Optional[list[str]] = None,
) -> None:
    series: list[tuple[str, str, str, list[tuple[float, float]]]] = []
    xmax = 1.0
    ymax = ymax_min

    for (benchmark, target_id), rows in sorted(problem_groups.items()):
        loops = actual_loop_rows(rows)
        if trim_after_zero:
            loops = trim_after_first_zero_worth(loops)

        points: list[tuple[float, float]] = []
        for r in loops:
            x = to_int(r.get("loop_index"))
            y = value_of_row(r)
            if y is None:
                continue
            if log_y and y <= 0.0:
                # The first-zero histogram records these zero rows.
                continue
            points.append((float(x), float(y)))

        if not loops:
            continue

        # X-axis should reflect the data boundary after trimming, even if the
        # last row was a zero omitted from a log-y plot.
        xmax = max(xmax, max(float(to_int(r.get("loop_index"))) for r in loops))

        if not points:
            continue

        ymax = max(ymax, max(y for _, y in points))
        status = outcome_group(rows)
        series.append((benchmark, target_id, status, points))

    lines = make_axis_begin(
        title=title,
        xlabel="Top-level loop round",
        ylabel=ylabel,
        xmax=xmax,
        ymax=ymax,
        log_y=log_y,
        legend_pos=legend_pos,
        extra_options=extra_axis_options,
    )

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


def worth_expanding_value(row: dict) -> Optional[float]:
    return float(to_int(row.get("worth_expanding")))


def reachable_or_nodes_value(row: dict) -> Optional[float]:
    # New CSVs provide reachable_or_nodes, excluding implementation edge-nodes
    # and AND-nodes.  The fallback keeps the script usable on old CSVs.
    raw = row.get("reachable_or_nodes")
    if raw is None or str(raw).strip() == "":
        raw = row.get("reachable_keys")
    return float(to_int(raw))


def expandable_ratio_value(row: dict) -> Optional[float]:
    raw = row.get("reachable_or_nodes")
    if raw is None or str(raw).strip() == "":
        raw = row.get("reachable_keys")
    reachable_or_nodes = to_int(raw)
    if reachable_or_nodes <= 0:
        return None
    return 100.0 * float(to_int(row.get("worth_expanding"))) / float(reachable_or_nodes)


def refutation_cache_hit_rate_value(row: dict) -> Optional[float]:
    # This value is cumulative up to the current loop.
    rate = str(row.get("refutation_cache_hit_rate", "")).strip()
    if rate:
        return 100.0 * to_float(rate)

    hits = to_int(row.get("refutation_cache_hits"))
    misses = to_int(row.get("refutation_cache_misses"))
    total = hits + misses
    if total <= 0:
        return None
    return 100.0 * float(hits) / float(total)


def filter_refutation_checked_value(row: dict) -> Optional[float]:
    return float(to_int(row.get("filter_refutation_checked")))


def filter_refutation_refuted_value(row: dict) -> Optional[float]:
    return float(to_int(row.get("filter_refutation_refuted")))


def filter_refutation_survived_value(row: dict) -> Optional[float]:
    return float(to_int(row.get("filter_refutation_survived")))


def filter_refutation_survival_rate_value(row: dict) -> Optional[float]:
    rate = str(row.get("filter_refutation_survival_rate", "")).strip()
    if rate:
        return 100.0 * to_float(rate)
    checked = to_int(row.get("filter_refutation_checked"))
    survived = to_int(row.get("filter_refutation_survived"))
    if checked <= 0:
        return None
    return 100.0 * float(survived) / float(checked)


def filter_abduction_checked_value(row: dict) -> Optional[float]:
    return float(to_int(row.get("filter_abduction_checked_conjectures")))


def filter_abduction_used_value(row: dict) -> Optional[float]:
    return float(to_int(row.get("filter_abduction_used_conjectures")))


def filter_abduction_discarded_value(row: dict) -> Optional[float]:
    return float(to_int(row.get("filter_abduction_discarded_conjectures")))


def filter_abduction_retention_rate_value(row: dict) -> Optional[float]:
    rate = str(row.get("filter_abduction_retention_rate", "")).strip()
    if rate:
        return 100.0 * to_float(rate)
    checked = to_int(row.get("filter_abduction_checked_conjectures"))
    used = to_int(row.get("filter_abduction_used_conjectures"))
    if checked <= 0:
        return None
    return 100.0 * float(used) / float(checked)




def append_unique_point(points: list[tuple[float, float]], point: tuple[float, float]) -> None:
    if not points or points[-1] != point:
        points.append(point)


def transition_rate_points(rows: list[dict]) -> list[tuple[float, float]]:
    points: list[tuple[float, float]] = []
    for r in trim_after_first_zero_worth(actual_loop_rows(rows)):
        x = filter_refutation_survival_rate_value(r)
        y = filter_abduction_retention_rate_value(r)
        if x is None or y is None:
            continue
        append_unique_point(points, (float(x), float(y)))
    return points


def cumulative_rate_points(rows: list[dict]) -> list[tuple[float, float]]:
    points: list[tuple[float, float]] = []
    ref_checked = 0
    ref_survived = 0
    abd_checked = 0
    abd_used = 0
    for r in trim_after_first_zero_worth(actual_loop_rows(rows)):
        ref_checked += to_int(r.get("filter_refutation_checked"))
        ref_survived += to_int(r.get("filter_refutation_survived"))
        abd_checked += to_int(r.get("filter_abduction_checked_conjectures"))
        abd_used += to_int(r.get("filter_abduction_used_conjectures"))
        if ref_checked <= 0 or abd_checked <= 0:
            continue
        append_unique_point(points, (100.0 * ref_survived / ref_checked, 100.0 * abd_used / abd_checked))
    return points


def write_filter_correlation_trajectory_graph(
    problem_groups: dict[tuple[str, str], list[dict]],
    out_path: Path,
    *,
    benchmark: str,
    cumulative: bool,
) -> None:
    series: list[tuple[str, str, str, list[tuple[float, float]]]] = []
    point_builder = cumulative_rate_points if cumulative else transition_rate_points

    for (bench, target_id), rows in sorted(problem_groups.items()):
        pts = point_builder(rows)
        if pts:
            # For the cumulative view, we only want the last available cumulative
            # point for each problem.  The transition view keeps the full
            # loop-by-loop trajectory.
            if cumulative:
                pts = [pts[-1]]
            series.append((bench, target_id, outcome_group(rows), pts))

    if not series:
        out_path.write_text("% No filter-rate trajectory data found.\n", encoding="utf-8")
        return

    title = (
        "Cumulative refutation-survival vs abduction-retention"
        if cumulative else
        "Per-loop refutation-survival vs abduction-retention transitions"
    )

    lines = [
        r"\begin{tikzpicture}",
        r"\begin{axis}[",
        r"width=0.95\linewidth,",
        r"height=0.62\linewidth,",
        f"title={{{title_with_benchmark(title, benchmark)}}},",
        r"xlabel={Refutation survival rate (\%)},",
        r"ylabel={Abduction retention rate (\%)},",
        r"xmin=0,",
        r"xmax=102,",
        r"ymin=0,",
        r"ymax=102,",
        r"xtick={0,20,40,60,80,100},",
        r"ytick={0,20,40,60,80,100},",
        r"grid=both,",
        r"minor grid style={draw=black!8,line width=0.15pt},",
        r"major grid style={draw=black!18,line width=0.25pt},",
        r"minor x tick num=1,",
        r"minor y tick num=1,",
        r"legend style={at={(0.02,0.98)},anchor=north west,draw=black,fill=white,fill opacity=0.85,text opacity=1,rounded corners=1pt},",
        r"legend cell align=left,",
        r"tick align=outside,",
        r"scaled x ticks=false,",
        r"scaled y ticks=false,",
        r"]",
    ]

    if cumulative:
        for label, colour, mark, _style in [outcome_style("proved"), outcome_style("unproved")]:
            legend_mark = "+" if label == "proved" else "x"
            lines.append(rf"\addlegendimage{{{colour},only marks,mark={legend_mark},mark size=2.0pt,line width=0.95pt}}")
            lines.append(rf"\addlegendentry{{{label}}}")

        for _bench, _target_id, outcome, pts in series:
            _label, colour, _mark, _style = outcome_style(outcome)
            x, y = pts[-1]
            point_mark = "+" if outcome == "proved" else "x"
            lines.append(
                rf"\addplot[{colour},only marks,mark={point_mark},mark size=2.0pt,line width=0.95pt,opacity=1.0] coordinates {{({fmt_num(x)},{fmt_num(y)})}};"
            )
    else:
        for label, colour, _mark, style in [outcome_style("proved"), outcome_style("unproved")]:
            lines.append(rf"\addlegendimage{{{colour},{style},line width=1.0pt,->}}")
            lines.append(rf"\addlegendentry{{{label}}}")

        for _bench, _target_id, outcome, pts in series:
            _label, colour, mark, style = outcome_style(outcome)
            if len(pts) == 1:
                # A single-loop trajectory has no arrow segment.  Use an unfilled,
                # outcome-specific marker and an opaque colour so overlapping red/blue
                # data cannot create misleading mixed-colour filled circles.
                x, y = pts[0]
                single_mark = "+" if outcome == "proved" else "x"
                lines.append(
                    rf"\addplot[{colour},only marks,mark={single_mark},mark size=2.0pt,line width=0.95pt,opacity=1.0] coordinates {{({fmt_num(x)},{fmt_num(y)})}};"
                )
                continue
            for (x1, y1), (x2, y2) in zip(pts, pts[1:]):
                if (x1, y1) == (x2, y2):
                    continue
                lines.append(
                    rf"\addplot[{colour},{style},no marks,line width=0.95pt,opacity=0.72,->] coordinates {{({fmt_num(x1)},{fmt_num(y1)}) ({fmt_num(x2)},{fmt_num(y2)})}};"
                )

    lines.extend([r"\end{axis}", r"\end{tikzpicture}", ""])
    out_path.write_text("\n".join(lines), encoding="utf-8")


def write_summary_quantile_graph(
    problem_groups: dict[tuple[str, str], list[dict]],
    out_path: Path,
    *,
    value_of_row: Callable[[dict], Optional[float]],
    title: str,
    ylabel: str,
    ymax_min: float = 1.0,
    log_y: bool = False,
    trim_after_zero: bool = True,
    extra_axis_options: Optional[list[str]] = None,
) -> None:
    by_status_loop: dict[str, dict[int, list[float]]] = {"proved": defaultdict(list), "unproved": defaultdict(list)}
    xmax = 1.0
    ymax = ymax_min

    for (_benchmark, _target_id), rows in sorted(problem_groups.items()):
        loops = actual_loop_rows(rows)
        if trim_after_zero:
            loops = trim_after_first_zero_worth(loops)
        status = outcome_group(rows)
        for r in loops:
            loop = to_int(r.get("loop_index"))
            y = value_of_row(r)
            if y is None:
                continue
            if log_y and y <= 0.0:
                continue
            by_status_loop[status][loop].append(float(y))
            xmax = max(xmax, float(loop))
            ymax = max(ymax, float(y))

    median_series: dict[str, list[tuple[float, float]]] = {}
    q1_series: dict[str, list[tuple[float, float]]] = {}
    q3_series: dict[str, list[tuple[float, float]]] = {}
    for status in ["proved", "unproved"]:
        med_pts: list[tuple[float, float]] = []
        q1_pts: list[tuple[float, float]] = []
        q3_pts: list[tuple[float, float]] = []
        for loop in sorted(by_status_loop[status]):
            vals = sorted(by_status_loop[status][loop])
            q1 = quantile(vals, 0.25)
            med = quantile(vals, 0.50)
            q3 = quantile(vals, 0.75)
            if q1 is None or med is None or q3 is None:
                continue
            q1_pts.append((float(loop), q1))
            med_pts.append((float(loop), med))
            q3_pts.append((float(loop), q3))
        if med_pts:
            median_series[status] = med_pts
            q1_series[status] = q1_pts
            q3_series[status] = q3_pts

    if not median_series:
        out_path.write_text("% No summary-quantile data found.\n", encoding="utf-8")
        return

    lines = make_axis_begin(
        title=title,
        xlabel="Top-level loop round",
        ylabel=ylabel,
        xmax=xmax,
        ymax=ymax,
        log_y=log_y,
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


def write_filtering_funnel_graph(
    problem_groups: dict[tuple[str, str], list[dict]],
    out_path: Path,
    *,
    benchmark: str,
) -> None:
    totals = {
        "checked": 0,
        "refuted": 0,
        "survived": 0,
        "submitted": 0,
        "used": 0,
        "discarded": 0,
    }
    for (_benchmark, _target_id), rows in problem_groups.items():
        for r in trim_after_first_zero_worth(actual_loop_rows(rows)):
            totals["checked"] += to_int(r.get("filter_refutation_checked"))
            totals["refuted"] += to_int(r.get("filter_refutation_refuted"))
            totals["survived"] += to_int(r.get("filter_refutation_survived"))
            totals["submitted"] += to_int(r.get("filter_abduction_checked_conjectures"))
            totals["used"] += to_int(r.get("filter_abduction_used_conjectures"))
            totals["discarded"] += to_int(r.get("filter_abduction_discarded_conjectures"))

    if all(v <= 0 for v in totals.values()):
        out_path.write_text("% No filtering-funnel data found.\n", encoding="utf-8")
        return

    order = [
        ("checked", "Checked"),
        ("refuted", "Refuted"),
        ("survived", "Survived"),
        ("submitted", "Submitted"),
        ("used", "Used"),
        ("discarded", "Discarded"),
    ]
    ymax = max(1, max(totals.values()))
    coords = " ".join(f"({label},{totals[key]})" for key, label in order if totals[key] > 0)
    lines = [
        r"\begin{tikzpicture}",
        r"\begin{axis}[",
        rf"title={{{title_with_benchmark('Conjecture-filtering funnel', benchmark)}}},",
        r"xlabel={Filtering stage},",
        r"ylabel={Cumulative per-loop unique conjecture occurrences},",
        r"width=0.95\linewidth,",
        r"height=0.56\linewidth,",
        r"ybar,",
        r"bar width=9pt,",
        r"ymode=log,",
        r"log basis y=10,",
        r"ymin=1,",
        rf"ymax={fmt_num(y_max_for_funnel(ymax))},",
        r"symbolic x coords={Checked,Refuted,Survived,Submitted,Used,Discarded},",
        r"xtick=data,",
        r"x tick label style={rotate=25,anchor=east},",
        r"grid=both,",
        r"minor grid style={draw=black!8,line width=0.15pt},",
        r"major grid style={draw=black!18,line width=0.25pt},",
        r"tick align=outside,",
        r"]",
        rf"\addplot[fill=black!18,draw=black] coordinates {{{coords}}};",
        r"\end{axis}",
        r"\end{tikzpicture}",
        "",
    ]
    out_path.write_text("\n".join(lines), encoding="utf-8")
    notes = (
        "This funnel sums per-loop unique conjecture counts over all runs in the benchmark.\n"
        "The counts are unique within a top-level loop, but not globally deduplicated across loops or problems.\n"
        "The Submitted/Used/Discarded stages refer to Sledgehammer abduction checks, not all survived conjectures.\n"
    )
    (out_path.parent / (out_path.stem + "_notes.txt")).write_text(notes, encoding="utf-8")


def y_max_for_funnel(value: int) -> float:
    if value <= 1:
        return 10.0
    return 10.0 ** math.ceil(math.log10(value * 1.15))


def correlation_rows(problem_groups: dict[tuple[str, str], list[dict]], *, cumulative: bool) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    buckets: dict[str, list[tuple[float, float]]] = {"all": [], "proved": [], "unproved": []}
    builder = cumulative_rate_points if cumulative else transition_rate_points
    for (_benchmark, _target_id), problem_rows in problem_groups.items():
        pts = builder(problem_rows)
        if cumulative and pts:
            pts = [pts[-1]]
        status = outcome_group(problem_rows)
        for x, y in pts:
            buckets["all"].append((x, y))
            buckets[status].append((x, y))

    for bucket_name in ["all", "proved", "unproved"]:
        pts = buckets[bucket_name]
        xs = [x for x, _y in pts]
        ys = [y for _x, y in pts]
        rows.append({
            "subset": bucket_name,
            "n": len(pts),
            "pearson": pearson(xs, ys),
            "spearman": spearman(xs, ys),
        })
    return rows


def write_filter_correlation_tables(
    problem_groups: dict[tuple[str, str], list[dict]],
    out_prefix: Path,
    *,
    benchmark: str,
) -> None:
    table_rows: list[dict[str, object]] = []
    for mode_name, cumulative in [("transition", False), ("cumulative", True)]:
        for row in correlation_rows(problem_groups, cumulative=cumulative):
            row = dict(row)
            row["mode"] = mode_name
            table_rows.append(row)

    csv_path = out_prefix.with_suffix(".csv")
    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["mode", "subset", "n", "pearson", "spearman"])
        writer.writeheader()
        for row in table_rows:
            out = dict(row)
            for key in ["pearson", "spearman"]:
                value = out[key]
                out[key] = "" if value is None else f"{value:.6g}"
            writer.writerow(out)

    def fmt_corr(x: object) -> str:
        return "--" if x is None else f"{float(x):.3f}"

    lines = [
        r"\begin{tabular}{llrrr}",
        r"\toprule",
        "Mode & Subset & $n$ & Pearson & Spearman " + r"\\",
        r"\midrule",
    ]
    for row in table_rows:
        lines.append(
            f"{tex_escape(row['mode'])} & {tex_escape(row['subset'])} & {row['n']} & {fmt_corr(row['pearson'])} & {fmt_corr(row['spearman'])} " + r"\\"
        )
    lines.extend([r"\bottomrule", r"\end{tabular}", ""])
    tex_path = out_prefix.with_suffix(".tex")
    tex_path.write_text("\n".join(lines), encoding="utf-8")


def write_first_zero_hist(problem_groups: dict[tuple[str, str], list[dict]], out_path: Path, benchmark: str = "") -> None:
    counts: Counter[int] = Counter()
    unproved_without_zero: list[str] = []

    for (benchmark, target_id), rows in sorted(problem_groups.items()):
        if outcome_group(rows) == "proved":
            continue

        loops = actual_loop_rows(rows)
        zero_loop = None
        for r in loops:
            if to_int(r.get("worth_expanding")) == 0:
                zero_loop = to_int(r.get("loop_index"))
                break

        if zero_loop is None:
            unproved_without_zero.append(f"{benchmark}:{target_id}")
        else:
            counts[zero_loop] += 1

    xmax = max(counts.keys(), default=1)
    ymax = max(counts.values(), default=1)
    coords = [(float(k), float(counts[k])) for k in sorted(counts)]

    lines = [
        r"\begin{tikzpicture}",
        r"\begin{axis}[",
        f"title={{{title_with_benchmark('Unproved runs exhausting the contributive frontier', benchmark)}}},",
        r"xlabel={Top-level loop round},",
        r"ylabel={Number of problems},",
        r"width=0.95\linewidth,",
        r"height=0.58\linewidth,",
        r"ybar,",
        r"bar width=7pt,",
        r"grid=both,",
        r"minor grid style={draw=gray!15,line width=0.15pt},",
        r"major grid style={draw=gray!30,line width=0.25pt},",
        r"tick align=outside,",
        r"enlarge x limits=false,",
        f"xmin=1, xmax={fmt_num(max(1.0, float(xmax)))},",
        f"ymin=0, ymax={fmt_num(max(1.0, float(ymax) + 1.0))},",
        f"xtick={{{','.join(str(i) for i in range(1, max(1, xmax) + 1))}}},",
        r"]",
        rf"\addplot[draw=black, fill=gray!55] coordinates {pgf_coordinates(coords)};",
        r"\end{axis}",
        r"\end{tikzpicture}",
        "",
    ]
    out_path.write_text("\n".join(lines), encoding="utf-8")

    note_lines = [
        "% This histogram counts only unproved runs that reached a loop with",
        "% worth_expanding = 0, i.e. runs where the contributive frontier was",
        "% exhausted.  Unproved runs that timed out or stopped before frontier",
        "% exhaustion are not counted in the bars.",
        "%",
        "% Unproved runs with no loop whose contributive OR-leaf count became 0:",
    ]
    if unproved_without_zero:
        for item in unproved_without_zero:
            note_lines.append(f"%   {item}")
    else:
        note_lines.append("%   (none)")
    (out_path.parent / (out_path.stem + "_notes.txt")).write_text("\n".join(note_lines) + "\n", encoding="utf-8")


def write_figures_for_benchmark(rows: list[dict], out_dir: Path, benchmark: str, *, linear_count_y: bool) -> bool:
    rows = [row for row in rows if row.get("benchmark") == benchmark]
    if not rows:
        print(f"No matching Abduction statistics rows found for benchmark {benchmark}; skipping.")
        return False

    problem_groups = group_problem_rows(rows)
    suffix = f"_{benchmark}" if benchmark else ""
    use_log_counts = not linear_count_y

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_worth_expanding_by_loop{suffix}.tex",
        value_of_row=worth_expanding_value,
        title=title_with_benchmark("Contributive OR-leaf nodes by loop", benchmark),
        ylabel="Number of contributive OR-leaf nodes",
        log_y=use_log_counts,
        legend_pos="north west",
        extra_axis_options=[
            r"minor x tick num=4,",
            r"minor y tick num=9,",
            r"minor grid style={draw=gray!28,line width=0.15pt},",
            r"major grid style={draw=gray!45,line width=0.25pt},",
        ],
    )

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_reachable_by_loop{suffix}.tex",
        value_of_row=reachable_or_nodes_value,
        title=title_with_benchmark("Root-reachable OR-nodes by loop", benchmark),
        ylabel="Number of root-reachable OR-nodes",
        log_y=use_log_counts,
        legend_pos="north west",
        extra_axis_options=[
            r"minor x tick num=4,",
            r"minor y tick num=9,",
            r"minor grid style={draw=gray!28,line width=0.15pt},",
            r"major grid style={draw=gray!45,line width=0.25pt},",
        ],
    )

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_expandable_ratio_by_loop{suffix}.tex",
        value_of_row=expandable_ratio_value,
        title=title_with_benchmark("Proportion of contributive OR-leaf nodes by loop", benchmark),
        ylabel="Contributive OR-leaf / root-reachable OR-node (%)",
        ymax_min=100.0,
        extra_axis_options=[r"ytick={0,20,40,60,80,100},", r"yticklabel style={/pgf/number format/fixed},"],
    )

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_refutation_cache_hit_rate_by_loop{suffix}.tex",
        value_of_row=refutation_cache_hit_rate_value,
        title=title_with_benchmark("Refutation cache hit rate by loop", benchmark),
        ylabel="Cache hits / cache lookups (%)",
        ymax_min=100.0,
        extra_axis_options=[r"ytick={0,20,40,60,80,100},", r"yticklabel style={/pgf/number format/fixed},"],
    )

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_refutation_checked_by_loop{suffix}.tex",
        value_of_row=filter_refutation_checked_value,
        title=title_with_benchmark("Conjectures checked by counterexample filtering", benchmark),
        ylabel="Unique conjectures checked",
        log_y=use_log_counts,
        legend_pos="north west",
    )

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_refutation_refuted_by_loop{suffix}.tex",
        value_of_row=filter_refutation_refuted_value,
        title=title_with_benchmark("Conjectures refuted by counterexample filtering", benchmark),
        ylabel="Unique conjectures refuted",
        log_y=use_log_counts,
        legend_pos="north west",
    )

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_refutation_survived_by_loop{suffix}.tex",
        value_of_row=filter_refutation_survived_value,
        title=title_with_benchmark("Conjectures surviving counterexample filtering", benchmark),
        ylabel="Unique conjectures surviving",
        log_y=use_log_counts,
        legend_pos="north west",
    )

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_refutation_survival_rate_by_loop{suffix}.tex",
        value_of_row=filter_refutation_survival_rate_value,
        title=title_with_benchmark("Counterexample-filter survival rate", benchmark),
        ylabel="Survived / checked (%)",
        ymax_min=100.0,
        extra_axis_options=[r"ytick={0,20,40,60,80,100},", r"yticklabel style={/pgf/number format/fixed},"],
    )

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_filter_checked_by_loop{suffix}.tex",
        value_of_row=filter_abduction_checked_value,
        title=title_with_benchmark("Conjectures submitted to Sledgehammer abduction check", benchmark),
        ylabel="Unique conjectures submitted",
        log_y=use_log_counts,
        legend_pos="north west",
    )

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_filter_used_by_loop{suffix}.tex",
        value_of_row=filter_abduction_used_value,
        title=title_with_benchmark("Conjectures used by Sledgehammer abduction check", benchmark),
        ylabel="Unique conjectures used",
        log_y=use_log_counts,
        legend_pos="north west",
    )

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_filter_discarded_by_loop{suffix}.tex",
        value_of_row=filter_abduction_discarded_value,
        title=title_with_benchmark("Conjectures discarded by Sledgehammer abduction check", benchmark),
        ylabel="Unique conjectures discarded",
        log_y=use_log_counts,
        legend_pos="north west",
    )

    write_line_graph(
        problem_groups,
        out_dir / f"abduction_filter_retention_rate_by_loop{suffix}.tex",
        value_of_row=filter_abduction_retention_rate_value,
        title=title_with_benchmark("Sledgehammer abduction-check retention rate", benchmark),
        ylabel="Used / submitted (%)",
        ymax_min=100.0,
        extra_axis_options=[r"ytick={0,20,40,60,80,100},", r"yticklabel style={/pgf/number format/fixed},"],
    )

    write_summary_quantile_graph(
        problem_groups,
        out_dir / f"abduction_expandable_ratio_summary_by_loop{suffix}.tex",
        value_of_row=expandable_ratio_value,
        title=title_with_benchmark("Contributive-frontier selectivity summary", benchmark),
        ylabel="Contributive OR-leaf / root-reachable OR-node (%)",
        ymax_min=100.0,
        extra_axis_options=[r"ytick={0,20,40,60,80,100},"],
    )

    write_summary_quantile_graph(
        problem_groups,
        out_dir / f"abduction_refutation_cache_hit_rate_summary_by_loop{suffix}.tex",
        value_of_row=refutation_cache_hit_rate_value,
        title=title_with_benchmark("Refutation-cache hit-rate summary", benchmark),
        ylabel="Cache hits / cache lookups (%)",
        ymax_min=100.0,
        extra_axis_options=[r"ytick={0,20,40,60,80,100},"],
    )

    write_summary_quantile_graph(
        problem_groups,
        out_dir / f"abduction_refutation_survival_rate_summary_by_loop{suffix}.tex",
        value_of_row=filter_refutation_survival_rate_value,
        title=title_with_benchmark("Counterexample-filter survival-rate summary", benchmark),
        ylabel="Survived / checked (%)",
        ymax_min=100.0,
        extra_axis_options=[r"ytick={0,20,40,60,80,100},"],
    )

    write_summary_quantile_graph(
        problem_groups,
        out_dir / f"abduction_filter_retention_rate_summary_by_loop{suffix}.tex",
        value_of_row=filter_abduction_retention_rate_value,
        title=title_with_benchmark("Sledgehammer abduction-retention summary", benchmark),
        ylabel="Used / submitted (%)",
        ymax_min=100.0,
        extra_axis_options=[r"ytick={0,20,40,60,80,100},"],
    )

    write_filtering_funnel_graph(
        problem_groups,
        out_dir / f"abduction_filtering_funnel{suffix}.tex",
        benchmark=benchmark,
    )

    write_filter_correlation_trajectory_graph(
        problem_groups,
        out_dir / f"abduction_filter_rate_transition_trajectory{suffix}.tex",
        benchmark=benchmark,
        cumulative=False,
    )

    write_filter_correlation_trajectory_graph(
        problem_groups,
        out_dir / f"abduction_filter_rate_cumulative_scatter{suffix}.tex",
        benchmark=benchmark,
        cumulative=True,
    )

    write_filter_correlation_tables(
        problem_groups,
        out_dir / f"abduction_filter_rate_correlation{suffix}",
        benchmark=benchmark,
    )

    write_first_zero_hist(
        problem_groups,
        out_dir / f"abduction_first_zero_expandable_hist{suffix}.tex",
        benchmark,
    )
    return True


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", nargs="*", type=Path)
    parser.add_argument("--results-root", type=Path, default=None)
    parser.add_argument("--out", type=Path, default=Path("Eval/latex"))
    parser.add_argument(
        "--benchmark",
        action="append",
        default=[],
        help="Generate figures for this benchmark. Can be passed multiple times. If omitted, figures are generated separately for every benchmark found.",
    )
    parser.add_argument(
        "--linear-count-y",
        action="store_true",
        help="Use a linear y-axis for reachable/worth-expanding count plots instead of the default log y-axis.",
    )
    parser.add_argument(
        "--method",
        default="abduction",
        help="Method to plot from abduction_statistics.csv. Defaults to pure 'abduction'. Use 'preprocessed_abduction' for the Abduction phase after TBC seeding, or 'all' only for ad-hoc diagnostics.",
    )
    args = parser.parse_args()

    csvs = discover_csvs(args.results_root, args.csv)
    if not csvs:
        print("No abduction_statistics.csv files found; skipping Abduction statistics figures.")
        return

    rows = filter_rows_by_method(read_rows(csvs), args.method)
    benchmarks = list(args.benchmark) if args.benchmark else distinct_benchmarks(rows)
    if not benchmarks:
        print("No benchmark names found in Abduction statistics; skipping.")
        return

    out_dir = method_output_dir(args.out, args.method)
    out_dir.mkdir(parents=True, exist_ok=True)
    generated = 0
    for benchmark in benchmarks:
        if write_figures_for_benchmark(rows, out_dir, benchmark, linear_count_y=args.linear_count_y):
            generated += 1

    if generated == 0:
        print("No matching Abduction statistics rows found; skipping Abduction statistics figures.")
    else:
        print(f"Generated Abduction statistics figures for method={args.method!r}, {generated} benchmark(s) in: {out_dir}")


if __name__ == "__main__":
    main()
