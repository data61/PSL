#!/usr/bin/env python3
r"""Generate black-and-white PGFPlots figures for AbductionProver filter statistics.

Main outputs per benchmark:

* abduction_filter_problem_decomposition_<benchmark>.tex
  Raw-count decomposition by problem.

* abduction_filter_problem_percentage_<benchmark>.tex
  100%-stacked per-problem composition plot.

* abduction_filter_loop_mean_proportions_<benchmark>.tex
  Mean per-problem proportions by top-level loop.

* abduction_orelse_problem_decomposition_<benchmark>.tex
* abduction_orelse_problem_percentage_<benchmark>.tex
* abduction_orelse_loop_mean_proportions_<benchmark>.tex
  Analogous plots for the cheap OR-filter reason breakdown.

The script also keeps the previous aggregate loop/totals figures for diagnostics.

Notes:
- Filled regions use TikZ patterns rather than only grayscale fills.
- A black triangle marker indicates a proved target according to summary.csv for the
  selected method.
- The generated .tex files require: \usetikzlibrary{patterns}
"""

from __future__ import annotations

import argparse
import csv
import math
import re
from collections import defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

DEFAULT_METHOD = "abduction"

ORELSE_REASON_COLUMNS = [
    ("filter_orelse_too_large", "Too large"),
    ("filter_orelse_eq_to_final_goal_from_tactic", "Same as goal"),
    ("filter_orelse_concl_is_eq_to_final_goal", "Conclusion=goal"),
    ("filter_orelse_has_func_with_three_occs_in_a_row", "Triple func."),
    ("filter_orelse_concls_are_same", "Same concl."),
    ("filter_orelse_concl_of_conj_refuted", "Refuted concl."),
]

STAGE_COLUMNS = [
    ("cheap", "Cheap OR", "filter_orelse_rejected_conjectures"),
    ("counterexample", "CEX refuted", "filter_refutation_refuted"),
    ("abduction_discarded", "SH discarded", "filter_abduction_discarded_conjectures"),
    ("abduction_used", "SH used", "filter_abduction_used_conjectures"),
]

GRAYS = [10, 28, 46, 64, 78, 90, 18, 36, 54, 72]
PATTERNS = [
    "north east lines",
    "north west lines",
    "vertical lines",
    "horizontal lines",
    "grid",
    "crosshatch",
    "dots",
    "crosshatch dots",
    "fivepointed stars",
    "bricks",
]


def column_key(col):
    return col[0]


def column_label(col):
    return col[1]


def column_data_key(col):
    return col[2] if len(col) >= 3 else col[0]


def to_int(x, default=0):
    try:
        s = str(x).strip()
        if not s:
            return default
        return int(float(s))
    except Exception:
        return default


def tex_escape(s):
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


def fmt_num(x):
    y = float(x)
    if abs(y - round(y)) < 1e-9:
        return str(int(round(y)))
    return f"{y:.6g}"


def title_with_benchmark(title, benchmark):
    return f"{title} ({benchmark})" if benchmark else title


def safe_suffix(s):
    return "".join(ch if ch.isalnum() or ch in {"-", "_"} else "_" for ch in s)


def natural_key(s):
    return [int(part) if part.isdigit() else part.lower() for part in re.split(r"(\d+)", str(s))]


def compact_problem_label(target_id):
    return Path(str(target_id)).stem or str(target_id)


def y_max_for_log(value):
    if value <= 1:
        return 10.0
    return 10.0 ** math.ceil(math.log10(value * 1.15))


def y_max_for_linear(value):
    if value <= 0:
        return 1.0
    return max(1.0, value * 1.12)


def discover_csvs(results_root, explicit_csvs):
    csvs = []
    for p in explicit_csvs:
        if not p.exists():
            raise FileNotFoundError(f"No such Abduction statistics CSV: {p}")
        csvs.append(p)
    if results_root:
        if not results_root.exists():
            raise FileNotFoundError(f"No such results root: {results_root}")
        csvs.extend(sorted(results_root.rglob("abduction_statistics.csv")))
    seen = set()
    out = []
    for p in csvs:
        q = p.resolve()
        if q not in seen:
            seen.add(q)
            out.append(p)
    return out


def discover_summary_csvs_from_stats(stats_csvs):
    summaries = []
    seen = set()
    for stats_csv in stats_csvs:
        candidate = stats_csv.with_name("summary.csv")
        if candidate.exists():
            q = candidate.resolve()
            if q not in seen:
                seen.add(q)
                summaries.append(candidate)
    return summaries


def read_rows(csvs):
    rows = []
    for path in csvs:
        with path.open(encoding="utf-8", newline="") as f:
            for raw in csv.DictReader(f):
                row = dict(raw)
                row["benchmark"] = (row.get("benchmark") or path.parent.name).strip() or path.parent.name
                rows.append(row)
    return rows


def infer_proved_from_summary_row(row):
    proof_found = str(row.get("proof_found", "")).strip().lower()
    if proof_found in {"true", "1", "yes"}:
        return True
    status = str(row.get("status", "")).strip().lower()
    proof_lines = to_int(row.get("proof_num_lines"), 0)
    return status == "ok" and proof_lines > 0


def read_summary_proof_map(summary_csvs, method):
    proved = {}
    wanted = str(method or "").strip()
    for path in summary_csvs:
        with path.open(encoding="utf-8", newline="") as f:
            for raw in csv.DictReader(f):
                row = dict(raw)
                row_method = str(row.get("method", "")).strip()
                if wanted not in {"", "all"} and row_method != wanted:
                    continue
                benchmark = (row.get("benchmark") or path.parent.name).strip() or path.parent.name
                target_id = str(row.get("target_id", "")).strip()
                if not target_id:
                    continue
                proved[(benchmark, target_id)] = infer_proved_from_summary_row(row)
    return proved


def filter_rows_by_method(rows, method):
    wanted = str(method or "").strip()
    if wanted in {"", "all"}:
        return rows
    return [row for row in rows if str(row.get("method", "")).strip() == wanted]


def method_output_dir(base, method):
    wanted = str(method or "").strip()
    if wanted in {"", "abduction", "all"}:
        return base
    return base / safe_suffix(wanted)


def actual_loop_rows(rows):
    return [r for r in rows if r.get("loop_kind") == "loop" and to_int(r.get("loop_index"), 0) > 0]


def trim_after_first_zero_worth(rows):
    trimmed = []
    for r in rows:
        trimmed.append(r)
        if to_int(r.get("worth_expanding"), 0) == 0:
            break
    return trimmed


def group_problem_rows(rows):
    grouped = defaultdict(list)
    for row in rows:
        grouped[(row.get("benchmark", ""), row.get("target_id", ""))].append(row)
    for key in grouped:
        grouped[key].sort(key=lambda r: to_int(r.get("loop_index"), 0))
    return grouped


def distinct_benchmarks(rows):
    return sorted({str(row.get("benchmark", "")).strip() for row in rows if str(row.get("benchmark", "")).strip()})


def aggregate_by_loop(problem_groups, columns):
    totals = defaultdict(lambda: defaultdict(int))
    for (_benchmark, _target_id), problem_rows in problem_groups.items():
        for row in trim_after_first_zero_worth(actual_loop_rows(problem_rows)):
            loop = to_int(row.get("loop_index"), 0)
            if loop <= 0:
                continue
            for col in columns:
                totals[loop][column_key(col)] += to_int(row.get(column_data_key(col)))
    return totals


def aggregate_totals(problem_groups, columns):
    by_loop = aggregate_by_loop(problem_groups, columns)
    totals = defaultdict(int)
    for loop_totals in by_loop.values():
        for key, value in loop_totals.items():
            totals[key] += value
    return dict(totals)


def aggregate_by_problem(problem_groups, columns, proved_map=None):
    rows = []
    proved_map = proved_map or {}
    for (benchmark, target_id), problem_rows in problem_groups.items():
        item = {"benchmark": benchmark, "target_id": target_id, "proved": bool(proved_map.get((benchmark, target_id), False))}
        for col in columns:
            item[column_key(col)] = 0
        for row in trim_after_first_zero_worth(actual_loop_rows(problem_rows)):
            for col in columns:
                item[column_key(col)] += to_int(row.get(column_data_key(col)))
        item["total"] = sum(item[column_key(col)] for col in columns)
        rows.append(item)
    return rows


def order_problem_aggregates(problem_rows, order):
    if order == "total":
        return sorted(problem_rows, key=lambda r: (r.get("total", 0), natural_key(r.get("target_id", ""))))
    if order == "reverse-total":
        return sorted(problem_rows, key=lambda r: (-r.get("total", 0), natural_key(r.get("target_id", ""))))
    return sorted(problem_rows, key=lambda r: natural_key(r.get("target_id", "")))


def mean_proportions_by_loop(problem_groups, columns):
    accum = defaultdict(lambda: {"n": 0, "sums": defaultdict(float)})
    for (_benchmark, _target_id), problem_rows in problem_groups.items():
        for row in trim_after_first_zero_worth(actual_loop_rows(problem_rows)):
            loop = to_int(row.get("loop_index"), 0)
            if loop <= 0:
                continue
            values = {column_key(col): to_int(row.get(column_data_key(col))) for col in columns}
            total = sum(values.values())
            if total <= 0:
                continue
            accum[loop]["n"] += 1
            for key, value in values.items():
                accum[loop]["sums"][key] += float(value) / float(total)
    result = {}
    for loop, data in accum.items():
        n = int(data["n"])
        if n <= 0:
            continue
        result[loop] = {"n": n}
        for col in columns:
            result[loop][column_key(col)] = 100.0 * data["sums"].get(column_key(col), 0.0) / float(n)
    return result


def plot_options_for_series(index, *, use_patterns=True):
    gray = GRAYS[index % len(GRAYS)]
    if use_patterns:
        pattern = PATTERNS[index % len(PATTERNS)]
        return f"draw=black,fill=white,pattern={pattern},pattern color=black"
    return f"draw=black,fill=black!{gray}"


def marker_plot_options():
    return "only marks,mark=triangle*,mark options={solid,fill=black,scale=0.85},black"


def write_stacked_loop_bar_graph(out_path, *, benchmark, title, ylabel, columns, by_loop, linear_y, legend_columns=2):
    if not by_loop:
        out_path.write_text("% No filter data found.\n", encoding="utf-8")
        return False
    loops = sorted(by_loop)
    ymax = max(sum(by_loop[loop].get(column_key(col), 0) for col in columns) for loop in loops)
    if ymax <= 0:
        out_path.write_text("% No positive filter data found.\n", encoding="utf-8")
        return False

    axis_options = [
        "% Requires: \\usetikzlibrary{patterns}",
        rf"title={{{title_with_benchmark(title, tex_escape(benchmark))}}},",
        r"xlabel={Top-level loop round},",
        rf"ylabel={{{ylabel}}},",
        r"width=0.95\linewidth,",
        r"height=0.58\linewidth,",
        r"ybar stacked,",
        r"bar width=6pt,",
        r"xmin=0.5,",
        rf"xmax={fmt_num(max(loops) + 0.5)},",
        rf"xtick={{{','.join(str(loop) for loop in loops)}}},",
        r"grid=both,",
        r"minor grid style={draw=black!8,line width=0.15pt},",
        r"major grid style={draw=black!18,line width=0.25pt},",
        r"tick align=outside,",
        r"axis line style={black},",
        r"legend style={at={(0.02,0.98)},anchor=north west,draw=black,fill=white,fill opacity=0.92,text opacity=1,rounded corners=1pt,font=\scriptsize},",
        rf"legend columns={legend_columns},",
        r"legend cell align=left,",
    ]
    if linear_y:
        axis_options.extend([r"ymin=0,", rf"ymax={fmt_num(y_max_for_linear(ymax))},", r"scaled y ticks=false,"])
    else:
        axis_options.extend([r"ymode=log,", r"log basis y=10,", r"ymin=1,", rf"ymax={fmt_num(y_max_for_log(ymax))},", r"minor y tick num=9,"])

    lines = [r"\begin{tikzpicture}", r"\begin{axis}["]
    lines.extend(axis_options)
    lines.append(r"]")
    for i, col in enumerate(columns):
        key, label = column_key(col), column_label(col)
        coords = " ".join(
            f"({loop},{by_loop[loop].get(key, 0)})"
            for loop in loops
            if linear_y or by_loop[loop].get(key, 0) > 0
        )
        lines.append(rf"\addplot+[{plot_options_for_series(i, use_patterns=True)},ybar] coordinates {{{coords}}};")
        lines.append(rf"\addlegendentry{{{tex_escape(label)}}}")
    lines.extend([r"\end{axis}", r"\end{tikzpicture}", ""])
    out_path.write_text("\n".join(lines), encoding="utf-8")
    return True


def write_totals_bar_graph(out_path, *, benchmark, columns, totals, title, ylabel, linear_y):
    positive = [(column_key(col), column_label(col), totals.get(column_key(col), 0)) for col in columns if totals.get(column_key(col), 0) > 0]
    if not positive:
        out_path.write_text("% No positive filter data found.\n", encoding="utf-8")
        return False
    labels = [label for _key, label, _value in positive]
    ymax = max(value for _key, _label, value in positive)
    coords = " ".join(f"({idx},{value})" for idx, (_key, _label, value) in enumerate(positive, start=1))
    xticks = ",".join(str(i) for i in range(1, len(positive) + 1))
    xticklabels = ",".join("{" + tex_escape(label) + "}" for label in labels)

    lines = [
        "% Requires: \\usetikzlibrary{patterns}",
        r"\begin{tikzpicture}",
        r"\begin{axis}[",
        rf"title={{{title_with_benchmark(title, tex_escape(benchmark))}}},",
        r"xlabel={Filter effect},",
        rf"ylabel={{{ylabel}}},",
        r"width=0.95\linewidth,",
        r"height=0.56\linewidth,",
        r"ybar,",
        r"bar width=9pt,",
        rf"xtick={{{xticks}}},",
        rf"xticklabels={{{xticklabels}}},",
        r"x tick label style={rotate=25,anchor=east},",
        r"grid=both,",
        r"minor grid style={draw=black!8,line width=0.15pt},",
        r"major grid style={draw=black!18,line width=0.25pt},",
        r"tick align=outside,",
        r"axis line style={black},",
    ]
    if linear_y:
        lines.extend([r"ymin=0,", rf"ymax={fmt_num(y_max_for_linear(ymax))},"])
    else:
        lines.extend([r"ymode=log,", r"log basis y=10,", r"ymin=1,", rf"ymax={fmt_num(y_max_for_log(ymax))},", r"minor y tick num=9,"])
    lines.extend([
        r"]",
        rf"\addplot+[{plot_options_for_series(1, use_patterns=True)},ybar] coordinates {{{coords}}};",
        r"\end{axis}",
        r"\end{tikzpicture}",
        "",
    ])
    out_path.write_text("\n".join(lines), encoding="utf-8")
    return True


def make_problem_xticklabels(ordered, max_problem_labels):
    n = len(ordered)
    if n <= max_problem_labels:
        return ",".join("{" + tex_escape(compact_problem_label(row.get("target_id", ""))) + "}" for row in ordered)
    return ",".join("{" + str(i) + "}" for i in range(1, n + 1))


def write_problem_decomposition_graph(out_path, *, benchmark, title, columns, problem_rows, problem_order, max_problem_labels, ylabel, percentage=False):
    ordered = order_problem_aggregates(problem_rows, problem_order)
    if not ordered:
        out_path.write_text("% No problem-level filter data found.\n", encoding="utf-8")
        return False
    if max((row.get("total", 0) for row in ordered), default=0) <= 0:
        out_path.write_text("% No positive problem-level filter data found.\n", encoding="utf-8")
        return False

    n = len(ordered)
    xticks = ",".join(str(i) for i in range(1, n + 1))
    xticklabels = make_problem_xticklabels(ordered, max_problem_labels)
    xlabel = "Problem id" if problem_order == "id" else "Problem rank"
    if percentage:
        ymax = 108.0
    else:
        max_total = max(row.get("total", 0) for row in ordered)
        ymax = y_max_for_linear(max_total * 1.08)

    lines = [
        "% Requires: \\usetikzlibrary{patterns}",
        r"\begin{tikzpicture}",
        r"\begin{axis}[%",
        r"width=0.96\linewidth,",
        r"height=0.58\linewidth,",
        rf"title={{{title_with_benchmark(title, tex_escape(benchmark))}}},",
        rf"xlabel={{{xlabel}}},",
        rf"ylabel={{{ylabel}}},",
        r"xmin=0.5,",
        rf"xmax={fmt_num(n + 0.5)},",
        r"ymin=0,",
        rf"ymax={fmt_num(ymax)},",
        r"grid=both,",
        rf"xtick={{{xticks}}},",
        rf"xticklabels={{{xticklabels}}},",
        r"x tick label style={rotate=90,anchor=east,font=\tiny},",
        r"minor x tick num=1,",
        r"minor y tick num=1,",
        r"major grid style={draw=black!18,line width=0.25pt},",
        r"minor grid style={draw=black!8,line width=0.15pt},",
        r"tick align=outside,",
        r"axis line style={black},",
        r"stack plots=y,",
        r"area style,",
        r"const plot,",
        r"clip=false,",
        r"scaled y ticks=false,",
        r"legend style={at={(0.02,0.98)},anchor=north west,draw=black,fill=white,fill opacity=0.92,text opacity=1,rounded corners=1pt,font=\scriptsize},",
        r"legend columns=2,",
        r"legend cell align=left,",
        r"]",
    ]
    for i, col in enumerate(columns):
        key, label = column_key(col), column_label(col)
        coords = []
        for idx, row in enumerate(ordered, start=1):
            if percentage:
                total = row.get("total", 0)
                value = 0.0 if total <= 0 else 100.0 * float(row.get(key, 0)) / float(total)
            else:
                value = row.get(key, 0)
            coords.append(f"({idx - 0.5:.6f},{fmt_num(value)})")
        last_row = ordered[-1]
        if percentage:
            total = last_row.get("total", 0)
            last_value = 0.0 if total <= 0 else 100.0 * float(last_row.get(key, 0)) / float(total)
        else:
            last_value = last_row.get(key, 0)
        coords.append(f"({n + 0.5:.6f},{fmt_num(last_value)})")
        lines.append(rf"\addplot+[{plot_options_for_series(i, use_patterns=True)}] coordinates {{{' '.join(coords)}}} \closedcycle;")
        lines.append(rf"\addlegendentry{{{tex_escape(label)}}}")

    proved_rows = [(idx, row) for idx, row in enumerate(ordered, start=1) if row.get("proved")]
    if proved_rows:
        if percentage:
            proved_coords = " ".join(f"({idx},103)" for idx, _row in proved_rows)
        else:
            max_total = max(row.get("total", 0) for row in ordered)
            bump = max(1.0, 0.03 * max_total)
            proved_coords = " ".join(f"({idx},{fmt_num(row.get('total', 0) + bump)})" for idx, row in proved_rows)
        lines.append(rf"\addplot+[{marker_plot_options()}] coordinates {{{proved_coords}}};")
        lines.append(r"\addlegendentry{Proved}")

    lines.extend([r"\end{axis}", r"\end{tikzpicture}", ""])
    out_path.write_text("\n".join(lines), encoding="utf-8")
    return True


def write_loop_mean_proportion_graph(out_path, *, benchmark, title, columns, mean_props):
    if not mean_props:
        out_path.write_text("% No loop-round proportion data found.\n", encoding="utf-8")
        return False
    loops = sorted(mean_props)
    lines = [
        "% Requires: \\usetikzlibrary{patterns}",
        r"\begin{tikzpicture}",
        r"\begin{axis}[%",
        r"width=0.95\linewidth,",
        r"height=0.56\linewidth,",
        rf"title={{{title_with_benchmark(title, tex_escape(benchmark))}}},",
        r"xlabel={Top-level loop round},",
        r"ylabel={Mean per-problem share (\\%)},",
        r"ybar stacked,",
        r"bar width=7pt,",
        r"xmin=0.5,",
        rf"xmax={fmt_num(max(loops) + 0.5)},",
        rf"xtick={{{','.join(str(loop) for loop in loops)}}},",
        r"ymin=0,",
        r"ymax=100,",
        r"ytick={0,20,40,60,80,100},",
        r"grid=both,",
        r"minor x tick num=1,",
        r"minor y tick num=1,",
        r"major grid style={draw=black!18,line width=0.25pt},",
        r"minor grid style={draw=black!8,line width=0.15pt},",
        r"tick align=outside,",
        r"axis line style={black},",
        r"scaled y ticks=false,",
        r"legend style={at={(0.02,0.98)},anchor=north west,draw=black,fill=white,fill opacity=0.92,text opacity=1,rounded corners=1pt,font=\scriptsize},",
        r"legend columns=2,",
        r"legend cell align=left,",
        r"]",
    ]
    for i, col in enumerate(columns):
        key, label = column_key(col), column_label(col)
        coords = " ".join(f"({loop},{fmt_num(mean_props[loop].get(key, 0.0))})" for loop in loops)
        lines.append(rf"\addplot+[{plot_options_for_series(i, use_patterns=True)},ybar] coordinates {{{coords}}};")
        lines.append(rf"\addlegendentry{{{tex_escape(label)}}}")
    lines.extend([r"\end{axis}", r"\end{tikzpicture}", ""])
    out_path.write_text("\n".join(lines), encoding="utf-8")
    return True


def write_loop_mean_proportion_csv(out_path, columns, mean_props):
    if not mean_props:
        out_path.write_text("loop_index,n_problems\n", encoding="utf-8")
        return
    with out_path.open("w", encoding="utf-8", newline="") as f:
        fieldnames = ["loop_index", "n_problems"] + [column_key(col) for col in columns]
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for loop in sorted(mean_props):
            row = {"loop_index": loop, "n_problems": int(mean_props[loop].get("n", 0))}
            for col in columns:
                row[column_key(col)] = f"{mean_props[loop].get(column_key(col), 0.0):.6f}"
            writer.writerow(row)


def write_problem_label_map(out_path, problem_rows, problem_order):
    ordered = order_problem_aggregates(problem_rows, problem_order)
    with out_path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["problem_index", "target_id", "total", "proved"])
        writer.writeheader()
        for idx, row in enumerate(ordered, start=1):
            writer.writerow({
                "problem_index": idx,
                "target_id": row.get("target_id", ""),
                "total": row.get("total", 0),
                "proved": str(bool(row.get("proved", False))).lower(),
            })


def write_notes(out_dir, benchmark, problem_order):
    suffix = f"_{safe_suffix(benchmark)}" if benchmark else ""
    text = (
        "Interpretation of the AbductionProver filter-attrition figures\n"
        "==============================================================\n\n"
        "The figures generated by abduction_filter_funnel_to_latex.py use the same "
        "per-loop unique-counting principle as the ML filter instrumentation. "
        "Repeated visits to the same canonical conjecture in the same top-level loop "
        "are counted once, while the same conjecture may be counted again in another "
        "loop or another problem.\n\n"
        "The problem-decomposition figures sum those per-loop unique counts over the "
        "top-level loops of each problem. They should therefore be read as a "
        "decomposition of filter effects, not as a count of globally unique conjectures "
        "over the entire run. The default problem order is target id, not runtime or "
        "filter-volume rank. Current problem order option: " + problem_order + ".\n\n"
        "Problem-decomposition plots are emitted in two forms: raw-count stacked plots "
        "and 100%-stacked percentage plots by problem. The raw-count version shows "
        "absolute filter volume, while the percentage version shows composition "
        "independent of total volume.\n\n"
        "Filled regions use black-and-white TikZ patterns rather than only grayscale "
        "fills, to remain distinguishable in monochrome printing. A black triangle "
        "marker above a bar indicates that the corresponding problem was proved "
        "according to summary.csv for the selected method.\n\n"
        "The 100%-stacked loop-round figures use mean per-problem proportions. For "
        "each problem and loop, the script first normalises by that problem-loop's "
        "positive filter-activity total, and then averages the shares across problems. "
        "This is intended to show whether the relative filter mix changes over loop "
        "rounds without allowing one unusually large problem to dominate the plot.\n\n"
        "The stage plots are not exact mass-conserving funnels, because the existing "
        "counters are collected at different call sites and are not all nested in one "
        "single candidate stream. The OR-else reason plots attribute each cheap "
        "rejection to the first condition that fired in the original short-circuit order.\n"
    )
    (out_dir / f"abduction_filter_attrition_notes{suffix}.txt").write_text(text, encoding="utf-8")


def write_figures_for_benchmark(rows, out_dir, benchmark, *, linear_y, problem_order, max_problem_labels, proved_map):
    bench_rows = [r for r in rows if str(r.get("benchmark", "")).strip() == benchmark]
    if not bench_rows:
        return False

    problem_groups = group_problem_rows(bench_rows)
    suffix = f"_{safe_suffix(benchmark)}" if benchmark else ""

    by_loop_stages = aggregate_by_loop(problem_groups, STAGE_COLUMNS)
    by_loop_reasons = aggregate_by_loop(problem_groups, ORELSE_REASON_COLUMNS)
    totals_stages = aggregate_totals(problem_groups, STAGE_COLUMNS)
    problem_stages = aggregate_by_problem(problem_groups, STAGE_COLUMNS, proved_map=proved_map)
    problem_reasons = aggregate_by_problem(problem_groups, ORELSE_REASON_COLUMNS, proved_map=proved_map)
    mean_stage_props = mean_proportions_by_loop(problem_groups, STAGE_COLUMNS)
    mean_reason_props = mean_proportions_by_loop(problem_groups, ORELSE_REASON_COLUMNS)

    generated = False
    generated |= write_problem_decomposition_graph(
        out_dir / f"abduction_filter_problem_decomposition{suffix}.tex",
        benchmark=benchmark,
        title="Filter-effect decomposition by problem",
        columns=STAGE_COLUMNS,
        problem_rows=problem_stages,
        problem_order=problem_order,
        max_problem_labels=max_problem_labels,
        ylabel="Per-loop unique conjecture occurrences",
        percentage=False,
    )
    generated |= write_problem_decomposition_graph(
        out_dir / f"abduction_filter_problem_percentage{suffix}.tex",
        benchmark=benchmark,
        title="Filter-effect composition by problem",
        columns=STAGE_COLUMNS,
        problem_rows=problem_stages,
        problem_order=problem_order,
        max_problem_labels=max_problem_labels,
        ylabel="Share of per-problem filter effects (\\%)",
        percentage=True,
    )
    generated |= write_loop_mean_proportion_graph(
        out_dir / f"abduction_filter_loop_mean_proportions{suffix}.tex",
        benchmark=benchmark,
        title="Mean filter-effect proportions by loop",
        columns=STAGE_COLUMNS,
        mean_props=mean_stage_props,
    )
    generated |= write_problem_decomposition_graph(
        out_dir / f"abduction_orelse_problem_decomposition{suffix}.tex",
        benchmark=benchmark,
        title="Cheap OR-filter reasons by problem",
        columns=ORELSE_REASON_COLUMNS,
        problem_rows=problem_reasons,
        problem_order=problem_order,
        max_problem_labels=max_problem_labels,
        ylabel="Per-loop unique cheap-filter rejections",
        percentage=False,
    )
    generated |= write_problem_decomposition_graph(
        out_dir / f"abduction_orelse_problem_percentage{suffix}.tex",
        benchmark=benchmark,
        title="Cheap OR-filter reason composition by problem",
        columns=ORELSE_REASON_COLUMNS,
        problem_rows=problem_reasons,
        problem_order=problem_order,
        max_problem_labels=max_problem_labels,
        ylabel="Share of per-problem cheap-filter rejections (\\%)",
        percentage=True,
    )
    generated |= write_loop_mean_proportion_graph(
        out_dir / f"abduction_orelse_loop_mean_proportions{suffix}.tex",
        benchmark=benchmark,
        title="Mean cheap OR-filter reason proportions by loop",
        columns=ORELSE_REASON_COLUMNS,
        mean_props=mean_reason_props,
    )

    # Backward-compatible diagnostic figures.
    generated |= write_stacked_loop_bar_graph(
        out_dir / f"abduction_gradual_filter_effects{suffix}.tex",
        benchmark=benchmark,
        title="Filter effects by top-level loop",
        ylabel="Per-loop unique conjecture occurrences",
        columns=STAGE_COLUMNS,
        by_loop=by_loop_stages,
        linear_y=linear_y,
        legend_columns=2,
    )
    generated |= write_stacked_loop_bar_graph(
        out_dir / f"abduction_orelse_reason_breakdown{suffix}.tex",
        benchmark=benchmark,
        title="Cheap OR-filter rejection reasons by loop",
        ylabel="Per-loop unique cheap-filter rejections",
        columns=ORELSE_REASON_COLUMNS,
        by_loop=by_loop_reasons,
        linear_y=linear_y,
        legend_columns=2,
    )
    generated |= write_totals_bar_graph(
        out_dir / f"abduction_filter_stage_totals{suffix}.tex",
        benchmark=benchmark,
        columns=STAGE_COLUMNS,
        totals=totals_stages,
        title="Aggregate filter effects",
        ylabel="Cumulative per-loop unique conjecture occurrences",
        linear_y=linear_y,
    )

    write_loop_mean_proportion_csv(out_dir / f"abduction_filter_loop_mean_proportions{suffix}.csv", STAGE_COLUMNS, mean_stage_props)
    write_loop_mean_proportion_csv(out_dir / f"abduction_orelse_loop_mean_proportions{suffix}.csv", ORELSE_REASON_COLUMNS, mean_reason_props)
    write_problem_label_map(out_dir / f"abduction_filter_problem_order{suffix}.csv", problem_stages, problem_order)

    if generated:
        write_notes(out_dir, benchmark, problem_order)
    return generated


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", nargs="*", type=Path, help="Explicit abduction_statistics.csv files")
    parser.add_argument("--results-root", type=Path, default=None, help="Root directory containing */abduction_statistics.csv files")
    parser.add_argument("--out", type=Path, default=Path("Eval/latex"), help="Output directory for generated .tex files")
    parser.add_argument(
        "--benchmark",
        action="append",
        default=[],
        help="Generate figures for this benchmark. Can be passed multiple times. If omitted, figures are generated separately for every benchmark found.",
    )
    parser.add_argument(
        "--method",
        default=DEFAULT_METHOD,
        help="Method to plot from abduction_statistics.csv. Defaults to pure 'abduction'. Use 'preprocessed_abduction' for the Abduction phase after TBC seeding, or 'all' for diagnostics.",
    )
    parser.add_argument(
        "--problem-order",
        choices=["id", "total", "reverse-total"],
        default="id",
        help="Order for per-problem decomposition figures. Default: id, so the x-axis follows problem ids rather than sorting by filter volume.",
    )
    parser.add_argument(
        "--max-problem-labels",
        type=int,
        default=60,
        help="Show target-id tick labels when the number of problems is at most this value. Otherwise show numeric indices and write a companion order CSV. Default: 60.",
    )
    axis_group = parser.add_mutually_exclusive_group()
    axis_group.add_argument(
        "--linear-count-y",
        action="store_true",
        help="Use a linear y-axis for count plots. This is the default, because stacked log bars are hard to interpret.",
    )
    axis_group.add_argument(
        "--log-count-y",
        action="store_true",
        help="Use a logarithmic y-axis for aggregate count plots. Use mainly for ad-hoc diagnostics, not paper-facing stacked plots.",
    )
    args = parser.parse_args()

    csvs = discover_csvs(args.results_root, args.csv)
    if not csvs:
        print("No abduction_statistics.csv files found; skipping filter-attrition figures.")
        return

    rows = filter_rows_by_method(read_rows(csvs), args.method)
    summary_csvs = discover_summary_csvs_from_stats(csvs)
    proved_map = read_summary_proof_map(summary_csvs, args.method)
    benchmarks = list(args.benchmark) if args.benchmark else distinct_benchmarks(rows)
    if not benchmarks:
        print("No benchmark names found in Abduction statistics; skipping filter-attrition figures.")
        return

    out_dir = method_output_dir(args.out, args.method)
    out_dir.mkdir(parents=True, exist_ok=True)

    generated = 0
    for benchmark in benchmarks:
        if write_figures_for_benchmark(
            rows,
            out_dir,
            benchmark,
            linear_y=not args.log_count_y,
            problem_order=args.problem_order,
            max_problem_labels=args.max_problem_labels,
            proved_map=proved_map,
        ):
            generated += 1

    if generated == 0:
        print("No matching Abduction filter-attrition data found; skipping.")
    else:
        print(f"Generated Abduction filter-attrition figures for method={args.method!r}, {generated} benchmark(s) in: {out_dir}")


if __name__ == "__main__":
    main()
