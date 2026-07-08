#!/usr/bin/env python3
r"""
Post-process PSL/TBC/Abduction evaluation summary.csv files into LaTeX/PGFPlots.

Typical use inside the PSL repository:

  python3 Eval/summary_to_latex_v10.py \
      --results-root Eval/results \
      --out Eval/latex

or explicitly:

  python3 Eval/summary_to_latex_v10.py \
      Eval/results/Isaplanner/summary.csv \
      Eval/results/Prod/summary.csv \
      Eval/results/TIP15/summary.csv \
      --out Eval/latex

Generated files:
  summary_table_all.tex
  correlation_table.tex
  fig_solved_bar_all.tex
  fig_cactus_all.tex
  fig_cactus_<benchmark>.tex
  fig_lines_time_all.tex
  fig_lines_time_<benchmark>.tex
  fig_cactus_lines_time_<benchmark>.tex

LaTeX preamble requirements:
  \usepackage{booktabs}
  \usepackage{tikz}
  \usetikzlibrary{patterns}
  \usepackage{pgfplots}
  \pgfplotsset{compat=1.18}
  \usepgfplotslibrary{groupplots}
"""

from __future__ import annotations

import argparse
import csv
import math
import statistics
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional


DEFAULT_METHOD_ORDER = ["psl", "tbc", "abduction", "preprocessed_abduction"]
DEFAULT_METHOD_LABEL = {
    "psl": "PSL",
    "tbc": "TBC",
    "abduction": "Pure AbductionProver",
    "preprocessed_abduction": "Combo Prover",
}
DEFAULT_BENCHMARK_ORDER = ["Isaplanner", "Prod", "TIP15"]

# Marker-only plotting styles.
# These are intentionally simple PGFPlots marker names.
METHOD_MARK = {
    "psl": "o",
    "tbc": "square",
    "abduction": "star",
    "preprocessed_abduction": "triangle",
}





@dataclass(frozen=True)
class EvalRow:
    benchmark: str
    method: str
    target_id: str
    status: str
    error_kind: str
    elapsed_sec: Optional[float]
    proof_found: bool
    proof_num_lines: Optional[float]
    timeout: Optional[float]


def truthy(x: object) -> bool:
    return str(x).strip().lower() in {"1", "true", "yes", "y"}


def to_float(x: object) -> Optional[float]:
    """Parse a value as a finite float.

    Empty cells and non-numeric strings become None. Numeric zero is
    preserved. NaN and +/-inf are treated as invalid because PGFPlots
    cannot safely consume them as coordinates.
    """
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


def is_finite_number(x: Optional[float]) -> bool:
    return x is not None and math.isfinite(x)


def tex_escape(s: object) -> str:
    """Escape plain text for LaTeX without re-escaping inserted macros.

    This is for labels and table cells that are plain text. It is
    character-based, so a backslash becomes \textbackslash{} and the braces
    in that replacement are not subsequently escaped.
    """
    repl = {
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
    return "".join(repl.get(ch, ch) for ch in str(s))


def safe_coord_name(s: str) -> str:
    # PGFPlots symbolic coordinates should not contain commas/braces.
    return s.replace(",", "-").replace("{", "").replace("}", "")


def fmt_num(x: Optional[float], digits: int = 2) -> str:
    if x is None or (isinstance(x, float) and (math.isnan(x) or math.isinf(x))):
        return "--"
    if abs(x - round(x)) < 10 ** (-(digits + 1)):
        return str(int(round(x)))
    return f"{x:.{digits}f}"


def median(xs: Iterable[float]) -> Optional[float]:
    ys = list(xs)
    return statistics.median(ys) if ys else None


def mean(xs: Iterable[float]) -> Optional[float]:
    ys = list(xs)
    return statistics.mean(ys) if ys else None


def percentile(xs: Iterable[float], p: float) -> Optional[float]:
    ys = sorted(xs)
    if not ys:
        return None
    if len(ys) == 1:
        return ys[0]
    k = (len(ys) - 1) * p
    lo = math.floor(k)
    hi = math.ceil(k)
    if lo == hi:
        return ys[lo]
    return ys[lo] * (hi - k) + ys[hi] * (k - lo)



def pearson(xs: list[float], ys: list[float]) -> Optional[float]:
    if len(xs) != len(ys) or len(xs) < 3:
        return None
    mx, my = statistics.mean(xs), statistics.mean(ys)
    sx = sum((x - mx) ** 2 for x in xs)
    sy = sum((y - my) ** 2 for y in ys)
    if sx == 0 or sy == 0:
        return None
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / math.sqrt(sx * sy)


def ols_line(xs: list[float], ys: list[float]) -> tuple[Optional[float], Optional[float]]:
    """Return (intercept, slope) for y = a + b*x."""
    if len(xs) != len(ys) or len(xs) < 2:
        return None, None
    mx, my = statistics.mean(xs), statistics.mean(ys)
    sxx = sum((x - mx) ** 2 for x in xs)
    if sxx == 0:
        return None, None
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    b = sxy / sxx
    a = my - b * mx
    return a, b



def discover_csvs(results_root: Optional[Path], explicit_csvs: list[Path]) -> list[Path]:
    csvs: list[Path] = []
    for p in explicit_csvs:
        if p.exists():
            csvs.append(p)
        else:
            raise FileNotFoundError(f"No such summary CSV: {p}")
    if results_root:
        if not results_root.exists():
            raise FileNotFoundError(f"No such results root: {results_root}")
        csvs.extend(sorted(results_root.glob("*/summary.csv")))
    # Remove duplicates while preserving order.
    seen = set()
    unique = []
    for p in csvs:
        q = p.resolve()
        if q not in seen:
            seen.add(q)
            unique.append(p)
    return unique


def read_summary_csv(path: Path) -> list[EvalRow]:
    rows: list[EvalRow] = []
    with path.open(encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for raw in reader:
            benchmark = (raw.get("benchmark") or path.parent.name).strip() or path.parent.name
            rows.append(
                EvalRow(
                    benchmark=benchmark,
                    method=(raw.get("method") or "").strip(),
                    target_id=(raw.get("target_id") or raw.get("target_file") or "").strip(),
                    status=(raw.get("status") or "").strip(),
                    error_kind=(raw.get("error_kind") or "").strip(),
                    elapsed_sec=to_float(raw.get("elapsed_sec")),
                    proof_found=truthy(raw.get("proof_found")),
                    proof_num_lines=to_float(raw.get("proof_num_lines")),
                    timeout=to_float(raw.get("timeout")),
                )
            )
    return rows


def ordered_present(values: Iterable[str], preferred_order: list[str]) -> list[str]:
    vals = list(dict.fromkeys(v for v in values if v))
    preferred = [v for v in preferred_order if v in vals]
    rest = sorted(v for v in vals if v not in preferred)
    return preferred + rest


def timeout_for_rows(rows: list[EvalRow]) -> Optional[float]:
    """Return an explicit timeout from the CSV rows, if present.

    Do not infer timeout from elapsed_sec. PAR2 is meaningful only with a
    real benchmark timeout. Inferring it from max(elapsed_sec) would reward
    methods that fail quickly.
    """
    ts = [r.timeout for r in rows if is_finite_number(r.timeout)]
    return max(ts) if ts else None


def par2(rows: list[EvalRow]) -> Optional[float]:
    """PAR2: solved runtime; unsolved penalty = 2 * explicit timeout.

    Returns None when no explicit timeout is recorded in the input rows.
    """
    if not rows:
        return None
    t = timeout_for_rows(rows)
    if t is None:
        return None
    vals = []
    for r in rows:
        if r.proof_found and is_finite_number(r.elapsed_sec):
            vals.append(r.elapsed_sec)
        else:
            vals.append(2.0 * t)
    return statistics.mean(vals)


def row_stats(rows: list[EvalRow]) -> dict[str, Optional[float] | int]:
    solved = [r for r in rows if r.proof_found and is_finite_number(r.elapsed_sec)]
    solved_times = [r.elapsed_sec for r in solved if is_finite_number(r.elapsed_sec)]
    solved_lines = [r.proof_num_lines for r in solved if is_finite_number(r.proof_num_lines)]

    # Classify only unsolved rows into mutually exclusive categories.
    # This guarantees:
    #   N = Solved + No proof + TO + Err
    unsolved = [r for r in rows if not r.proof_found]

    timeout_rows = [
        r for r in unsolved
        if r.status == "timeout" or r.error_kind == "timeout"
    ]

    no_proof = [
        r for r in unsolved
        if r not in timeout_rows and r.error_kind == "no_proof"
    ]

    # Err means every remaining unsolved abnormal case, including interrupted,
    # unknown, empty status, killed process, disk-full failure, etc.
    error_rows = [
        r for r in unsolved
        if r not in timeout_rows and r not in no_proof
    ]

    return {
        "targets": len(rows),
        "solved": len(solved),
        "no_proof": len(no_proof),
        "timeouts": len(timeout_rows),
        "errors": len(error_rows),
        "timeout": timeout_for_rows(rows),
        "median_time": median(solved_times),
        "p90_time": percentile(solved_times, 0.90),
        "par2": par2(rows),
        "median_lines": median(solved_lines),
    }


def group_rows(rows: list[EvalRow]) -> dict[str, dict[str, list[EvalRow]]]:
    grouped: dict[str, dict[str, list[EvalRow]]] = defaultdict(lambda: defaultdict(list))
    for r in rows:
        grouped[r.benchmark][r.method].append(r)
    return grouped



def write_summary_table(
    out: Path,
    grouped: dict[str, dict[str, list[EvalRow]]],
    benchmarks: list[str],
    methods: list[str],
    labels: dict[str, str],
) -> None:
    lines = []
    lines.append(r"\begin{tabular}{llrrrrrr}")
    lines.append(r"\toprule")
    lines.append(
        r"Benchmark & Method & $N$ & Proved & Proved \% & TO & Med. $t$ & PAR2 \\"
    )
    lines.append(r"\midrule")
    for b_idx, b in enumerate(benchmarks):
        first = True
        for m in methods:
            rs = grouped.get(b, {}).get(m, [])
            if not rs:
                continue
            s = row_stats(rs)
            proved_pct = (100.0 * s["solved"] / s["targets"]) if s["targets"] else None
            bench_cell = tex_escape(b) if first else ""
            first = False
            lines.append(
                f"{bench_cell} & {tex_escape(labels.get(m, m))} & "
                f"{s['targets']} & {s['solved']} & {fmt_num(proved_pct, 1)} & "
                f"{s['timeouts']} & "
                f"{fmt_num(s['median_time'], 2)} & {fmt_num(s['par2'], 2)} \\\\"
            )
        if b_idx != len(benchmarks) - 1:
            lines.append(r"\midrule")
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    (out / "summary_table_all.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")

def regression_for(rows: list[EvalRow]) -> dict[str, Optional[float] | int]:
    solved = [
        r for r in rows
        if r.proof_found
        and is_finite_number(r.elapsed_sec)
        and r.elapsed_sec > 0
        and is_finite_number(r.proof_num_lines)
    ]
    xs = [float(r.proof_num_lines) for r in solved]
    ys_log = [math.log10(float(r.elapsed_sec)) for r in solved]
    intercept, slope = ols_line(xs, ys_log)
    multiplier = (10.0 ** slope) if slope is not None else None
    return {
        "n": len(solved),
        "pearson_log_time": pearson(xs, ys_log),
        "slope": slope,
        "mult_per_line": multiplier,
    }


def write_correlation_table(
    out: Path,
    grouped: dict[str, dict[str, list[EvalRow]]],
    benchmarks: list[str],
    methods: list[str],
    labels: dict[str, str],
) -> None:
    lines = []
    lines.append(r"\begin{tabular}{llrrrr}")
    lines.append(r"\toprule")
    lines.append(r"Benchmark & Method & $n$ & Pearson$(\ell,\log_{10} t)$ & Slope $b$ & Mult. $(10^b)$ \\")
    lines.append(r"\midrule")
    for b_idx, b in enumerate(benchmarks):
        first = True
        for m in methods:
            rs = grouped.get(b, {}).get(m, [])
            if not rs:
                continue
            c = regression_for(rs)
            bench_cell = tex_escape(b) if first else ""
            first = False
            lines.append(
                f"{bench_cell} & {tex_escape(labels.get(m, m))} & "
                f"{c['n']} & {fmt_num(c['pearson_log_time'], 2)} & "
                f"{fmt_num(c['slope'], 3)} & {fmt_num(c['mult_per_line'], 2)} " + r"\\"
            )
        if b_idx != len(benchmarks) - 1:
            lines.append(r"\midrule")
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    (out / "correlation_table.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def axis_log_common() -> list[str]:
    return [
        r"  ymode=log,",
        r"  log basis y=10,",
        r"  log ticks with fixed point,",
        r"  grid=both,",
        r"  minor grid style={draw=gray!15},",
        r"  major grid style={draw=gray!30},",
    ]


def axis_loglog_common() -> list[str]:
    return [
        r"  xmode=log,",
        r"  ymode=log,",
        r"  log basis x=10,",
        r"  log basis y=10,",
        r"  log ticks with fixed point,",
        r"  grid=both,",
        r"  minor grid style={draw=gray!15},",
        r"  major grid style={draw=gray!30},",
    ]



def marker_for_method(m: str) -> str:
    return METHOD_MARK.get(m, "*")


def append_plot_if_nonempty(lines: list[str], options: str, coords: str) -> bool:
    """Append an addplot command only when coords is non-empty.

    PGFPlots treats coordinates {} as a fatal error. Returning False lets
    callers skip the matching legend entry as well.
    """
    if not coords.strip():
        return False
    lines.append(rf"\addplot+[{options}] coordinates {{{coords}}};")
    return True


def write_cactus_one(
    out: Path,
    benchmark: str,
    by_method: dict[str, list[EvalRow]],
    methods: list[str],
    labels: dict[str, str],
) -> None:
    lines = []
    lines.append(r"\begin{tikzpicture}")
    lines.append(r"\begin{axis}[")
    lines.extend([
        f"  title={{{tex_escape(benchmark)}}},",
        r"  xlabel={Solved problems},",
        r"  ylabel={Runtime (s)},",
        r"  legend pos=north west,",
        r"  width=0.8\linewidth,",
        r"  height=0.5\linewidth,",
    ])
    lines.extend(axis_log_common())
    lines.append(r"]")
    for m in methods:
        times = sorted(
            r.elapsed_sec for r in by_method.get(m, [])
            if r.proof_found and is_finite_number(r.elapsed_sec) and r.elapsed_sec > 0
        )
        coords = " ".join(f"({i+1},{t:.3f})" for i, t in enumerate(times))
        if append_plot_if_nonempty(lines, f"only marks, mark={marker_for_method(m)}", coords):
            lines.append(rf"\addlegendentry{{{tex_escape(labels.get(m, m))}}}")
    lines.append(r"\end{axis}")
    lines.append(r"\end{tikzpicture}")
    (out / f"fig_cactus_{safe_coord_name(benchmark)}.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_cactus_all(
    out: Path,
    grouped: dict[str, dict[str, list[EvalRow]]],
    benchmarks: list[str],
    methods: list[str],
    labels: dict[str, str],
) -> None:
    if not benchmarks:
        (out / "fig_cactus_all.tex").write_text("% No benchmarks to plot.\n", encoding="utf-8")
        return
    n = len(benchmarks)
    width = "0.33\\linewidth" if n >= 3 else "0.46\\linewidth"
    lines = []
    lines.append(r"\begin{tikzpicture}")
    lines.append(r"\begin{groupplot}[")
    lines.extend([
        rf"  group style={{group size={n} by 1, horizontal sep=1.2cm}},",
        r"  xlabel={Solved problems},",
        r"  ylabel={Runtime (s)},",
        rf"  width={width},",
        r"  height=0.35\linewidth,",
        r"  legend pos=north west,",
    ])
    lines.extend(axis_log_common())
    lines.append(r"]")
    for b_idx, b in enumerate(benchmarks):
        lines.append(rf"\nextgroupplot[title={{{tex_escape(b)}}}]")
        for m in methods:
            times = sorted(
                r.elapsed_sec for r in grouped.get(b, {}).get(m, [])
                if r.proof_found and is_finite_number(r.elapsed_sec) and r.elapsed_sec > 0
            )
            coords = " ".join(f"({i+1},{t:.3f})" for i, t in enumerate(times))
            if append_plot_if_nonempty(lines, f"only marks, mark={marker_for_method(m)}", coords):
                if b_idx == 0:
                    lines.append(rf"\addlegendentry{{{tex_escape(labels.get(m, m))}}}")
    lines.append(r"\end{groupplot}")
    lines.append(r"\end{tikzpicture}")
    (out / "fig_cactus_all.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")



def bar_style_for_method(m: str) -> str:
    # Black-and-white bar styles using patterns, not colour.
    # Requires LaTeX preamble: \usetikzlibrary{patterns}
    styles = {
        "psl": r"draw=black, fill=white",
        "tbc": r"draw=black, fill=white, postaction={pattern=north east lines}",
        "abduction": r"draw=black, fill=white, postaction={pattern=crosshatch}",
    }
    return styles.get(m, r"draw=black, fill=white")



def write_solved_bar_all(
    out: Path,
    grouped: dict[str, dict[str, list[EvalRow]]],
    benchmarks: list[str],
    methods: list[str],
    labels: dict[str, str],
) -> None:
    if not benchmarks:
        (out / "fig_solved_bar_all.tex").write_text("% No benchmarks to plot.\n", encoding="utf-8")
        return
    sym = ",".join(safe_coord_name(b) for b in benchmarks)
    lines = []
    lines.append(r"\begin{tikzpicture}")
    lines.append(r"\begin{axis}[")
    lines.extend([
        r"  ybar,",
        r"  bar width=7pt,",
        rf"  symbolic x coords={{{sym}}},",
        r"  xtick=data,",
        r"  ylabel={Proved goals (\%)},",
        r"  xlabel={Benchmark},",
        r"  ymin=0,",
        r"  ymax=100,",
        r"  width=0.85\linewidth,",
        r"  height=0.42\linewidth,",
        r"  legend style={at={(0.5,1.05)},anchor=south,legend columns=-1},",
        r"]",
    ])
    for m in methods:
        coords = []
        for b in benchmarks:
            rs = grouped.get(b, {}).get(m, [])
            total = len(rs)
            proved = sum(1 for r in rs if r.proof_found)
            proved_pct = (100.0 * proved / total) if total else 0.0
            coords.append(f"({safe_coord_name(b)},{proved_pct:.3f})")
        lines.append(rf"\addplot+[{bar_style_for_method(m)}] coordinates {{{' '.join(coords)}}};")
        lines.append(rf"\addlegendentry{{{tex_escape(labels.get(m, m))}}}")
    lines.append(r"\end{axis}")
    lines.append(r"\end{tikzpicture}")
    (out / "fig_solved_bar_all.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_lines_time_one(
    out: Path,
    benchmark: str,
    by_method: dict[str, list[EvalRow]],
    methods: list[str],
    labels: dict[str, str],
    jitter: float,
) -> None:
    # Runtime-vs-proof-length plots use log-log axes.  Do not apply horizontal
    # jitter here, because additive offsets distort ratios on a logarithmic axis.
    lines = []
    lines.append(r"\begin{tikzpicture}")
    lines.append(r"\begin{axis}[")
    lines.extend([
        f"  title={{{tex_escape(benchmark)}}},",
        r"  xlabel={Proof length (lines)},",
        r"  ylabel={Runtime (s)},",
        r"  legend pos=north west,",
        r"  width=0.8\linewidth,",
        r"  height=0.5\linewidth,",
    ])
    lines.extend(axis_loglog_common())
    lines.append(r"]")
    for m in methods:
        coords = []
        for r in by_method.get(m, []):
            if (
                r.proof_found
                and is_finite_number(r.elapsed_sec)
                and r.elapsed_sec > 0
                and is_finite_number(r.proof_num_lines)
                and r.proof_num_lines > 0
            ):
                coords.append(f"({r.proof_num_lines:.3f},{r.elapsed_sec:.3f})")
        coords_s = " ".join(coords)
        if append_plot_if_nonempty(lines, f"mark={marker_for_method(m)}, only marks", coords_s):
            lines.append(rf"\addlegendentry{{{tex_escape(labels.get(m, m))}}}")
    lines.append(r"\end{axis}")
    lines.append(r"\end{tikzpicture}")
    (out / f"fig_lines_time_{safe_coord_name(benchmark)}.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_lines_time_all(
    out: Path,
    grouped: dict[str, dict[str, list[EvalRow]]],
    benchmarks: list[str],
    methods: list[str],
    labels: dict[str, str],
    jitter: float,
) -> None:
    if not benchmarks:
        (out / "fig_lines_time_all.tex").write_text("% No benchmarks to plot.\n", encoding="utf-8")
        return
    n = len(benchmarks)
    width = "0.33\\linewidth" if n >= 3 else "0.46\\linewidth"

    # Runtime-vs-proof-length plots use log-log axes.  Do not apply horizontal
    # jitter here, because additive offsets distort ratios on a logarithmic axis.
    lines = []
    lines.append(r"\begin{tikzpicture}")
    lines.append(r"\begin{groupplot}[")
    lines.extend([
        rf"  group style={{group size={n} by 1, horizontal sep=1.2cm}},",
        r"  xlabel={Proof length (lines)},",
        r"  ylabel={Runtime (s)},",
        rf"  width={width},",
        r"  height=0.35\linewidth,",
        r"  legend pos=north west,",
    ])
    lines.extend(axis_loglog_common())
    lines.append(r"]")
    for b_idx, b in enumerate(benchmarks):
        lines.append(rf"\nextgroupplot[title={{{tex_escape(b)}}}]")
        for m in methods:
            coords = []
            for r in grouped.get(b, {}).get(m, []):
                if (
                    r.proof_found
                    and is_finite_number(r.elapsed_sec)
                    and r.elapsed_sec > 0
                    and is_finite_number(r.proof_num_lines)
                    and r.proof_num_lines > 0
                ):
                    coords.append(f"({r.proof_num_lines:.3f},{r.elapsed_sec:.3f})")
            coords_s = " ".join(coords)
            if append_plot_if_nonempty(lines, f"mark={marker_for_method(m)}, only marks", coords_s):
                if b_idx == 0:
                    lines.append(rf"\addlegendentry{{{tex_escape(labels.get(m, m))}}}")
    lines.append(r"\end{groupplot}")
    lines.append(r"\end{tikzpicture}")
    (out / "fig_lines_time_all.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def safe_legend_name(prefix: str, benchmark: str) -> str:
    """Return a PGFPlots legend name using only simple letters/digits."""
    cleaned = "".join(ch for ch in safe_coord_name(benchmark) if ch.isalnum())
    return f"{prefix}{cleaned or 'Benchmark'}"


def cactus_coords(rows: list[EvalRow]) -> str:
    times = sorted(
        r.elapsed_sec for r in rows
        if r.proof_found and is_finite_number(r.elapsed_sec) and r.elapsed_sec > 0
    )
    return " ".join(f"({i+1},{t:.3f})" for i, t in enumerate(times))


def lines_time_coords(rows: list[EvalRow]) -> str:
    coords = []
    for r in rows:
        if (
            r.proof_found
            and is_finite_number(r.elapsed_sec)
            and r.elapsed_sec > 0
            and is_finite_number(r.proof_num_lines)
            and r.proof_num_lines > 0
        ):
            coords.append(f"({r.proof_num_lines:.3f},{r.elapsed_sec:.3f})")
    return " ".join(coords)


def write_cactus_lines_time_one(
    out: Path,
    benchmark: str,
    by_method: dict[str, list[EvalRow]],
    methods: list[str],
    labels: dict[str, str],
) -> None:
    """Write a two-panel figure: cactus plot and runtime/proof-length plot.

    The two panels share one external legend.  This is intended for paper-facing
    figures where the individual one-panel plots would waste vertical space.
    Fonts are not scaled: only axis width/height are set.
    """
    legend_name = safe_legend_name("cactusLinesTimeLegend", benchmark)
    lines: list[str] = []
    lines.append(r"\begin{tikzpicture}")
    lines.append(r"\begin{groupplot}[")
    lines.extend([
        r"  group style={group size=2 by 1, horizontal sep=1.35cm},",
        r"  width=0.46\linewidth,",
        r"  height=0.34\linewidth,",
        r"  grid=both,",
        r"  minor grid style={draw=gray!15},",
        r"  major grid style={draw=gray!30},",
        r"  log ticks with fixed point,",
    ])
    lines.append(r"]")

    lines.append(r"\nextgroupplot[")
    lines.extend([
        f"  title={{{tex_escape(benchmark)}}},",
        r"  xlabel={Solved problems},",
        r"  ylabel={Runtime (s)},",
        r"  ymode=log,",
        r"  log basis y=10,",
        rf"  legend to name={legend_name},",
        r"  legend columns=-1,",
        r"  legend cell align=left,",
    ])
    lines.append(r"]")
    for m in methods:
        coords = cactus_coords(by_method.get(m, []))
        if append_plot_if_nonempty(lines, f"only marks, mark={marker_for_method(m)}", coords):
            lines.append(rf"\addlegendentry{{{tex_escape(labels.get(m, m))}}}")

    lines.append(r"\nextgroupplot[")
    lines.extend([
        f"  title={{{tex_escape(benchmark)}}},",
        r"  xlabel={Proof length (lines)},",
        r"  ylabel={},",
        r"  xmode=log,",
        r"  ymode=log,",
        r"  log basis x=10,",
        r"  log basis y=10,",
    ])
    lines.append(r"]")
    for m in methods:
        coords = lines_time_coords(by_method.get(m, []))
        append_plot_if_nonempty(lines, f"mark={marker_for_method(m)}, only marks", coords)

    lines.append(r"\end{groupplot}")
    lines.append(r"\end{tikzpicture}")
    lines.append(r"\par\vspace{0.35em}")
    lines.append(rf"\pgfplotslegendfromname{{{legend_name}}}")
    (out / f"fig_cactus_lines_time_{safe_coord_name(benchmark)}.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")

def parse_label_args(args: list[str]) -> dict[str, str]:
    labels = dict(DEFAULT_METHOD_LABEL)
    for item in args:
        if "=" not in item:
            raise ValueError(f"Bad --method-label entry {item!r}; expected method=Label")
        k, v = item.split("=", 1)
        labels[k.strip()] = v.strip()
    return labels


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("summary_csvs", nargs="*", type=Path)
    ap.add_argument("--results-root", type=Path, default=None,
                    help="Directory containing Isaplanner/summary.csv, Prod/summary.csv, TIP15/summary.csv, etc.")
    ap.add_argument("--out", type=Path, default=Path("Eval/latex"))
    ap.add_argument("--method-order", nargs="+", default=DEFAULT_METHOD_ORDER)
    ap.add_argument("--benchmark-order", nargs="+", default=DEFAULT_BENCHMARK_ORDER)
    ap.add_argument("--method-label", nargs="*", default=[],
                    help="Optional labels, e.g. --method-label psl=PSL tbc=TBC abduction=Pure-AbductionProver preprocessed_abduction=Combo-Prover")
    ap.add_argument("--jitter", type=float, default=0.0,
                    help="Deprecated/ignored: proof-length/runtime plots now use log-log axes without jitter.")
    args = ap.parse_args()

    csvs = discover_csvs(args.results_root, args.summary_csvs)
    if not csvs:
        raise SystemExit("No summary.csv files found. Pass CSV paths or use --results-root Eval/results.")

    all_rows: list[EvalRow] = []
    for p in csvs:
        all_rows.extend(read_summary_csv(p))

    grouped = group_rows(all_rows)
    benchmarks = ordered_present(grouped.keys(), args.benchmark_order)
    methods = ordered_present((r.method for r in all_rows), args.method_order)
    labels = parse_label_args(args.method_label)

    args.out.mkdir(parents=True, exist_ok=True)

    if not benchmarks:
        (args.out / "summary_table_all.tex").write_text("% No benchmark rows found.\n", encoding="utf-8")
        (args.out / "correlation_table.tex").write_text("% No benchmark rows found.\n", encoding="utf-8")
        (args.out / "fig_solved_bar_all.tex").write_text("% No benchmark rows found.\n", encoding="utf-8")
        (args.out / "fig_cactus_all.tex").write_text("% No benchmark rows found.\n", encoding="utf-8")
        (args.out / "fig_lines_time_all.tex").write_text("% No benchmark rows found.\n", encoding="utf-8")
        print(f"Read {len(all_rows)} rows from {len(csvs)} summary CSV file(s).")
        print("No benchmark rows found; wrote placeholder LaTeX files.")
        return

    write_summary_table(args.out, grouped, benchmarks, methods, labels)
    write_correlation_table(args.out, grouped, benchmarks, methods, labels)
    write_solved_bar_all(args.out, grouped, benchmarks, methods, labels)
    write_cactus_all(args.out, grouped, benchmarks, methods, labels)
    write_lines_time_all(args.out, grouped, benchmarks, methods, labels, args.jitter)
    for b in benchmarks:
        write_cactus_one(args.out, b, grouped[b], methods, labels)
        write_lines_time_one(args.out, b, grouped[b], methods, labels, args.jitter)
        write_cactus_lines_time_one(args.out, b, grouped[b], methods, labels)

    print(f"Read {len(all_rows)} rows from {len(csvs)} summary CSV file(s).")
    print(f"Benchmarks: {', '.join(benchmarks)}")
    print(f"Methods: {', '.join(methods)}")
    print(f"Wrote LaTeX files to {args.out}")


if __name__ == "__main__":
    main()
