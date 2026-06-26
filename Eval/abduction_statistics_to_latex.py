#!/usr/bin/env python3
"""Generate PGFPlots figures from AbductionProver per-loop statistics CSV files.

Input: one or more abduction_statistics.csv files.
Output: LaTeX/PGFPlots .tex files, primarily for Prod/full AbductionProver runs.

The generated line plots intentionally do not include one legend entry per problem:
there can be about 50 problems, so individual legends obscure the plot. Instead,
solid lines mean proved problems and dashed lines mean unproved problems.

The plot labels follow the paper terminology: "worth_expanding" is shown as
contributive OR-leaf nodes, while "reachable_keys" is shown as
root-descendant nodes.

For count plots, the y-axis is logarithmic by default.  Zero values cannot be
shown on a log axis, so zero worth-expanding rows are omitted from the line plot;
the separate first-zero histogram records exactly where those zero rows first occur.
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
        csvs.extend(sorted(results_root.glob("*/abduction_statistics.csv")))

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


def actual_loop_rows(rows: list[dict]) -> list[dict]:
    return [r for r in rows if r.get("loop_kind") == "loop" and to_int(r.get("loop_index"), 0) > 0]


def is_clean_proof(row: dict) -> bool:
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


def status_group(rows: list[dict]) -> str:
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
        f"title={{{title}}},",
        f"xlabel={{{xlabel}}},",
        f"ylabel={{{ylabel}}},",
        r"width=0.95\linewidth,",
        r"height=0.62\linewidth,",
        r"grid=both,",
        r"minor grid style={draw=gray!24,line width=0.15pt},",
        r"major grid style={draw=gray!42,line width=0.25pt},",
        r"minor x tick num=1,",
        r"minor y tick num=9," if log_y else r"minor y tick num=3,",
        r"legend cell align=left,",
        f"legend pos={legend_pos},",
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
        status = status_group(rows)
        series.append((benchmark, target_id, status, points))

    lines = make_axis_begin(
        title=title,
        xlabel="Loop index",
        ylabel=ylabel,
        xmax=xmax,
        ymax=ymax,
        log_y=log_y,
        legend_pos=legend_pos,
        extra_options=extra_axis_options,
    )

    # Only two legend entries: no per-problem labels.
    lines.extend([
        r"\addlegendimage{blue, solid}",
        r"\addlegendentry{proved}",
        r"\addlegendimage{red, dashed}",
        r"\addlegendentry{unproved}",
    ])

    for _benchmark, _target_id, status, points in series:
        style = "blue, solid" if status == "proved" else "red, dashed"
        lines.append(
            rf"\addplot+[{style}, no marks, opacity=0.72] coordinates {pgf_coordinates(points)};"
        )

    lines.extend([r"\end{axis}", r"\end{tikzpicture}", ""])
    out_path.write_text("\n".join(lines), encoding="utf-8")


def worth_expanding_value(row: dict) -> Optional[float]:
    return float(to_int(row.get("worth_expanding")))


def reachable_keys_value(row: dict) -> Optional[float]:
    return float(to_int(row.get("reachable_keys")))


def expandable_ratio_value(row: dict) -> Optional[float]:
    reachable = to_int(row.get("reachable_keys"))
    if reachable <= 0:
        return None
    return float(to_int(row.get("worth_expanding"))) / float(reachable)


def refutation_cache_hit_rate_value(row: dict) -> Optional[float]:
    # This value is cumulative up to the current loop.
    rate = str(row.get("refutation_cache_hit_rate", "")).strip()
    if rate:
        return to_float(rate)

    hits = to_int(row.get("refutation_cache_hits"))
    misses = to_int(row.get("refutation_cache_misses"))
    total = hits + misses
    if total <= 0:
        return None
    return float(hits) / float(total)


def write_first_zero_hist(problem_groups: dict[tuple[str, str], list[dict]], out_path: Path) -> None:
    counts: Counter[int] = Counter()
    unproved_without_zero: list[str] = []

    for (benchmark, target_id), rows in sorted(problem_groups.items()):
        if status_group(rows) != "unproved":
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
        r"title={Unproved problems: first loop with no contributive OR-leaf nodes},",
        r"xlabel={Loop index},",
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
        f"xmin=0.5, xmax={fmt_num(max(1.5, float(xmax) + 0.5))},",
        f"ymin=0, ymax={fmt_num(max(1.0, float(ymax) + 1.0))},",
        r"xtick=data,",
        r"]",
        rf"\addplot+[draw=black, fill=gray!55] coordinates {pgf_coordinates(coords)};",
        r"\end{axis}",
        r"\end{tikzpicture}",
        "",
    ]
    out_path.write_text("\n".join(lines), encoding="utf-8")

    note_lines = [
        "% Unproved problems with no loop whose contributive OR-leaf count became 0:",
    ]
    if unproved_without_zero:
        for item in unproved_without_zero:
            note_lines.append(f"%   {item}")
    else:
        note_lines.append("%   (none)")
    (out_path.parent / (out_path.stem + "_notes.txt")).write_text("\n".join(note_lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", nargs="*", type=Path)
    parser.add_argument("--results-root", type=Path, default=None)
    parser.add_argument("--out", type=Path, default=Path("Eval/latex"))
    parser.add_argument(
        "--benchmark",
        action="append",
        default=[],
        help="Restrict the figures to this benchmark. Can be passed multiple times.",
    )
    parser.add_argument(
        "--linear-count-y",
        action="store_true",
        help="Use a linear y-axis for reachable/worth-expanding count plots instead of the default log y-axis.",
    )
    args = parser.parse_args()

    csvs = discover_csvs(args.results_root, args.csv)
    if not csvs:
        print("No abduction_statistics.csv files found; skipping Abduction statistics figures.")
        return

    rows = read_rows(csvs)
    if args.benchmark:
        wanted = set(args.benchmark)
        rows = [row for row in rows if row.get("benchmark") in wanted]

    if not rows:
        print("No matching Abduction statistics rows found; skipping Abduction statistics figures.")
        return

    problem_groups = group_problem_rows(rows)
    args.out.mkdir(parents=True, exist_ok=True)

    suffix = "_" + "_".join(args.benchmark) if args.benchmark else ""
    use_log_counts = not args.linear_count_y

    write_line_graph(
        problem_groups,
        args.out / f"abduction_worth_expanding_by_loop{suffix}.tex",
        value_of_row=worth_expanding_value,
        title="Contributive OR-leaf nodes by loop",
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
        args.out / f"abduction_reachable_by_loop{suffix}.tex",
        value_of_row=reachable_keys_value,
        title="Root-descendant nodes by loop",
        ylabel="Number of root-descendant nodes",
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
        args.out / f"abduction_expandable_ratio_by_loop{suffix}.tex",
        value_of_row=expandable_ratio_value,
        title="Proportion of contributive OR-leaf nodes by loop",
        ylabel="Contributive OR-leaf / root-descendant",
        ymax_min=1.0,
        extra_axis_options=[r"yticklabel style={/pgf/number format/fixed},"],
    )

    write_line_graph(
        problem_groups,
        args.out / f"abduction_refutation_cache_hit_rate_by_loop{suffix}.tex",
        value_of_row=refutation_cache_hit_rate_value,
        title="Refutation cache hit rate by loop",
        ylabel="Cache hits / cache lookups",
        ymax_min=1.0,
        extra_axis_options=[r"yticklabel style={/pgf/number format/fixed},"],
    )

    write_first_zero_hist(
        problem_groups,
        args.out / f"abduction_first_zero_expandable_hist{suffix}.tex",
    )

    print(f"Generated Abduction statistics figures in: {args.out}")


if __name__ == "__main__":
    main()
