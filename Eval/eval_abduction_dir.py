#!/usr/bin/env python3

import argparse
import csv
import os
import signal
import shutil
import subprocess
import time
from pathlib import Path
from typing import Dict, List, Optional, Set


DEFAULT_LOGIC = {
    "abduction": "Smart_Isabelle",
    "preprocessed_abduction": "Smart_Isabelle",
    "psl": "PSL",
    "tbc": "TBC",
}

ABDUCTION_LIKE_METHODS = {"abduction", "preprocessed_abduction"}
TBC_SEEDED_METHODS = {"preprocessed_abduction"}


def terminate_process_group(proc: subprocess.Popen) -> None:
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        return

    try:
        proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def safe_name(s: str) -> str:
    return "".join(c if c.isalnum() or c == "_" else "_" for c in s)


def safe_session_name(method: str, target_id: str) -> str:
    stem = Path(target_id).with_suffix("").as_posix()
    return "Eval_" + safe_name(method + "_" + stem)


def normalize_proof_file(path: Path) -> int:
    text = path.read_text(encoding="utf-8", errors="replace")
    raw_lines = [line.rstrip() for line in text.splitlines()]

    lines = []
    previous_blank = False

    for line in raw_lines:
        blank = line.strip() == ""

        if blank:
            if not previous_blank:
                lines.append("")
            previous_blank = True
        else:
            lines.append(line)
            previous_blank = False

    while lines and lines[0] == "":
        lines.pop(0)

    while lines and lines[-1] == "":
        lines.pop()

    path.write_text(
        "\n".join(lines) + ("\n" if lines else ""),
        encoding="utf-8",
    )

    return sum(1 for line in lines if line.strip())




def read_csv_rows_from_dir(directory: Path, pattern: str) -> List[dict]:
    rows: List[dict] = []
    if not directory.exists():
        return rows
    for path in sorted(directory.glob(pattern)):
        try:
            with path.open(encoding="utf-8", newline="") as f:
                for row in csv.DictReader(f):
                    row = dict(row)
                    row["source_file"] = str(path)
                    rows.append(row)
        except Exception:
            pass
    return rows


ABDUCTION_STATISTICS_FIELDNAMES = [
    "method", "benchmark", "target_id", "status", "error_kind", "proof_found",
    "elapsed_sec", "timeout", "threads", "loop_kind", "loop_index", "depth",
    "reachable_keys", "reachable_or_nodes", "reachable_or_leaf_nodes", "worth_expanding", "selected_ornodes",
    "selection_rate",
    "graph_nodes",
    "graph_edges",
    "graph_or_nodes",
    "graph_and_nodes",
    "graph_or2and_edge_nodes",
    "graph_avg_indegree",
    "graph_max_indegree",
    "graph_scc_count",
    "graph_cyclic_scc_count",
    "graph_largest_scc_size",
    "graph_or_projected_edges",
    "graph_or_projected_avg_indegree",
    "graph_or_projected_max_indegree",
    "graph_or_projected_scc_count",
    "graph_or_projected_cyclic_scc_count",
    "graph_or_projected_largest_scc_size",
    "graph_and_projected_edges",
    "graph_and_projected_avg_indegree",
    "graph_and_projected_max_indegree",
    "graph_and_projected_scc_count",
    "graph_and_projected_cyclic_scc_count",
    "graph_and_projected_largest_scc_size",
    "graph_node_attempts",
    "graph_nodes_created",
    "graph_node_reuses",
    "graph_node_reuse_rate",
    "graph_ornode_attempts",
    "graph_ornodes_created",
    "graph_ornodes_reused",
    "graph_ornode_reuse_rate",
    "graph_andnode_attempts",
    "graph_andnodes_created",
    "graph_andnodes_reused",
    "graph_andnode_reuse_rate",
    "graph_edge_node_attempts",
    "graph_edge_nodes_created",
    "graph_edge_nodes_reused",
    "graph_edge_node_reuse_rate",
    "graph_edge_attempts",
    "graph_edges_created",
    "graph_edge_reuses",
    "graph_edge_reuse_rate",
    "or_expansion_attempts",
    "or_expansions_started",
    "or_expansion_reuse_rate",
    "num_processors", "refutation_cache_size", "refutation_cache_hits",
    "refutation_cache_misses", "refutation_cache_hit_rate",
    "filter_refutation_checked", "filter_refutation_refuted", "filter_refutation_survived",
    "filter_refutation_survival_rate",
    "filter_abduction_checked_conjectures", "filter_abduction_used_conjectures",
    "filter_abduction_discarded_conjectures", "filter_abduction_retention_rate",
    "loop_elapsed_sec", "abduction_stats_file",
]


ABDUCTION_DECREMENTAL_FIELDNAMES = [
    "method",
    "benchmark",
    "target_id",
    "status",
    "error_kind",
    "proof_found",
    "elapsed_sec",
    "timeout",
    "threads",
    "top_loop_index",
    "parent_or_name",
    "is_root_or_node",
    "decremental_round_index",
    "decremental_limit",
    "candidate_sets_before",
    "selected_sets",
    "carried_over_sets",
    "skipped_duplicate_sets",
    "skipped_subsumed_sets",
    "actual_proof_attempts",
    "successful_attempts",
    "failed_attempts",
    "new_sets",
    "candidate_sets_after",
    "accepted_edges_in_round",
    "accepted_edges_so_far",
    "selected_cardinality_min",
    "selected_cardinality_median",
    "selected_cardinality_max",
    "attempted_cardinality_min",
    "attempted_cardinality_median",
    "attempted_cardinality_max",
    "next_cardinality_min",
    "next_cardinality_median",
    "next_cardinality_max",
    "selected_depth_min",
    "selected_depth_median",
    "selected_depth_max",
    "attempted_depth_min",
    "attempted_depth_median",
    "attempted_depth_max",
    "next_depth_min",
    "next_depth_median",
    "next_depth_max",
    "decremental_elapsed_sec",
    "abduction_decremental_file",
]



TBC_SEED_PREPROCESSING_FIELDNAMES = [
    "method", "benchmark", "target_id", "status", "error_kind", "proof_found",
    "elapsed_sec", "timeout", "threads", "preprocessing_stats_kind",
    "rounds_requested", "direct_goal_attempted", "direct_goal_proved",
    "direct_goal_elapsed_sec", "generated_conjectures", "refuted_by_counterexample",
    "surviving_conjectures", "parallel_rounds_run", "parallel_candidate_nodes",
    "proved_template_lemmas", "original_goal_proved_by_tbc",
    "original_goal_proved_in_round", "tbc_preprocessing_elapsed_sec",
    "abduction_invoked", "abduction_solved", "abduction_elapsed_sec",
    "total_elapsed_sec", "tbc_seed_stats_file",
]


def collect_tbc_seed_preprocessing_statistics(row: Dict[str, object], stats_dir: str) -> List[dict]:
    stats_path = Path(stats_dir) if stats_dir else Path("__missing_tbc_seed_stats__")
    stats_rows = read_csv_rows_from_dir(stats_path, "*.csv")

    def base_row() -> dict:
        return {
            "method": row.get("method", ""),
            "benchmark": row.get("benchmark", ""),
            "target_id": row.get("target_id", ""),
            "status": row.get("status", ""),
            "error_kind": row.get("error_kind", ""),
            "proof_found": row.get("proof_found", ""),
            "elapsed_sec": row.get("elapsed_sec", ""),
            "timeout": row.get("timeout", ""),
            "threads": row.get("threads", ""),
        }

    technical_columns = [
        "rounds_requested", "direct_goal_attempted", "direct_goal_proved",
        "direct_goal_elapsed_sec", "generated_conjectures", "refuted_by_counterexample",
        "surviving_conjectures", "parallel_rounds_run", "parallel_candidate_nodes",
        "proved_template_lemmas", "original_goal_proved_by_tbc",
        "original_goal_proved_in_round", "tbc_preprocessing_elapsed_sec",
        "abduction_invoked", "abduction_solved", "abduction_elapsed_sec",
        "total_elapsed_sec",
    ]

    if not stats_rows:
        out = base_row()
        out["preprocessing_stats_kind"] = "missing"
        for column in technical_columns:
            out[column] = ""
        out["tbc_seed_stats_file"] = ""
        return [out]

    out_rows: List[dict] = []
    for stats_row in stats_rows:
        out = base_row()
        out["preprocessing_stats_kind"] = "preprocessing"
        for column in technical_columns:
            out[column] = stats_row.get(column, "")
        out["tbc_seed_stats_file"] = stats_row.get("source_file", "")
        out_rows.append(out)
    return out_rows


def collect_abduction_statistics(row: Dict[str, object], stats_dir: str) -> List[dict]:
    stats_path = Path(stats_dir) if stats_dir else Path("__missing_abduction_stats__")
    loop_rows = read_csv_rows_from_dir(stats_path, "*.loops.csv")

    def base_row() -> dict:
        return {
            "method": row.get("method", ""),
            "benchmark": row.get("benchmark", ""),
            "target_id": row.get("target_id", ""),
            "status": row.get("status", ""),
            "error_kind": row.get("error_kind", ""),
            "proof_found": row.get("proof_found", ""),
            "elapsed_sec": row.get("elapsed_sec", ""),
            "timeout": row.get("timeout", ""),
            "threads": row.get("threads", ""),
        }

    if not loop_rows:
        out = base_row()
        out.update({
            "loop_kind": "no_loop",
            "loop_index": 0,
            "depth": 0,
            "reachable_keys": 0,
            "reachable_or_nodes": 0,
            "reachable_or_leaf_nodes": 0,
            "worth_expanding": 0,
            "selected_ornodes": 0,
            "selection_rate": "",
            "graph_nodes": "",
            "graph_edges": "",
            "graph_or_nodes": "",
            "graph_and_nodes": "",
            "graph_or2and_edge_nodes": "",
            "graph_avg_indegree": "",
            "graph_max_indegree": "",
            "graph_scc_count": "",
            "graph_cyclic_scc_count": "",
            "graph_largest_scc_size": "",
            "graph_or_projected_edges": "",
            "graph_or_projected_avg_indegree": "",
            "graph_or_projected_max_indegree": "",
            "graph_or_projected_scc_count": "",
            "graph_or_projected_cyclic_scc_count": "",
            "graph_or_projected_largest_scc_size": "",
            "graph_and_projected_edges": "",
            "graph_and_projected_avg_indegree": "",
            "graph_and_projected_max_indegree": "",
            "graph_and_projected_scc_count": "",
            "graph_and_projected_cyclic_scc_count": "",
            "graph_and_projected_largest_scc_size": "",
            "graph_node_attempts": "",
            "graph_nodes_created": "",
            "graph_node_reuses": "",
            "graph_node_reuse_rate": "",
            "graph_ornode_attempts": "",
            "graph_ornodes_created": "",
            "graph_ornodes_reused": "",
            "graph_ornode_reuse_rate": "",
            "graph_andnode_attempts": "",
            "graph_andnodes_created": "",
            "graph_andnodes_reused": "",
            "graph_andnode_reuse_rate": "",
            "graph_edge_node_attempts": "",
            "graph_edge_nodes_created": "",
            "graph_edge_nodes_reused": "",
            "graph_edge_node_reuse_rate": "",
            "graph_edge_attempts": "",
            "graph_edges_created": "",
            "graph_edge_reuses": "",
            "graph_edge_reuse_rate": "",
            "or_expansion_attempts": "",
            "or_expansions_started": "",
            "or_expansion_reuse_rate": "",
            "num_processors": "",
            "refutation_cache_size": "",
            "refutation_cache_hits": "",
            "refutation_cache_misses": "",
            "refutation_cache_hit_rate": "",
            "filter_refutation_checked": "",
            "filter_refutation_refuted": "",
            "filter_refutation_survived": "",
            "filter_refutation_survival_rate": "",
            "filter_abduction_checked_conjectures": "",
            "filter_abduction_used_conjectures": "",
            "filter_abduction_discarded_conjectures": "",
            "filter_abduction_retention_rate": "",
            "loop_elapsed_sec": "",
            "abduction_stats_file": "",
        })
        return [out]

    statistic_rows: List[dict] = []
    for idx, loop_row in enumerate(loop_rows, start=1):
        out = base_row()
        out.update({
            "loop_kind": "loop",
            "loop_index": idx,
            "depth": loop_row.get("depth", ""),
            "reachable_keys": loop_row.get("reachable_keys", ""),
            "reachable_or_nodes": loop_row.get("reachable_or_nodes", loop_row.get("reachable_keys", "")),
            "reachable_or_leaf_nodes": loop_row.get("reachable_or_leaf_nodes", ""),
            "worth_expanding": loop_row.get("worth_expanding", ""),
            "selected_ornodes": loop_row.get("selected_ornodes", ""),
            "selection_rate": loop_row.get("selection_rate", ""),
            "graph_nodes": loop_row.get("graph_nodes", ""),
            "graph_edges": loop_row.get("graph_edges", ""),
            "graph_or_nodes": loop_row.get("graph_or_nodes", ""),
            "graph_and_nodes": loop_row.get("graph_and_nodes", ""),
            "graph_or2and_edge_nodes": loop_row.get("graph_or2and_edge_nodes", ""),
            "graph_avg_indegree": loop_row.get("graph_avg_indegree", ""),
            "graph_max_indegree": loop_row.get("graph_max_indegree", ""),
            "graph_scc_count": loop_row.get("graph_scc_count", ""),
            "graph_cyclic_scc_count": loop_row.get("graph_cyclic_scc_count", ""),
            "graph_largest_scc_size": loop_row.get("graph_largest_scc_size", ""),
            "graph_or_projected_edges": loop_row.get("graph_or_projected_edges", ""),
            "graph_or_projected_avg_indegree": loop_row.get("graph_or_projected_avg_indegree", ""),
            "graph_or_projected_max_indegree": loop_row.get("graph_or_projected_max_indegree", ""),
            "graph_or_projected_scc_count": loop_row.get("graph_or_projected_scc_count", ""),
            "graph_or_projected_cyclic_scc_count": loop_row.get("graph_or_projected_cyclic_scc_count", ""),
            "graph_or_projected_largest_scc_size": loop_row.get("graph_or_projected_largest_scc_size", ""),
            "graph_and_projected_edges": loop_row.get("graph_and_projected_edges", ""),
            "graph_and_projected_avg_indegree": loop_row.get("graph_and_projected_avg_indegree", ""),
            "graph_and_projected_max_indegree": loop_row.get("graph_and_projected_max_indegree", ""),
            "graph_and_projected_scc_count": loop_row.get("graph_and_projected_scc_count", ""),
            "graph_and_projected_cyclic_scc_count": loop_row.get("graph_and_projected_cyclic_scc_count", ""),
            "graph_and_projected_largest_scc_size": loop_row.get("graph_and_projected_largest_scc_size", ""),
            "graph_node_attempts": loop_row.get("graph_node_attempts", ""),
            "graph_nodes_created": loop_row.get("graph_nodes_created", ""),
            "graph_node_reuses": loop_row.get("graph_node_reuses", ""),
            "graph_node_reuse_rate": loop_row.get("graph_node_reuse_rate", ""),
            "graph_ornode_attempts": loop_row.get("graph_ornode_attempts", ""),
            "graph_ornodes_created": loop_row.get("graph_ornodes_created", ""),
            "graph_ornodes_reused": loop_row.get("graph_ornodes_reused", ""),
            "graph_ornode_reuse_rate": loop_row.get("graph_ornode_reuse_rate", ""),
            "graph_andnode_attempts": loop_row.get("graph_andnode_attempts", ""),
            "graph_andnodes_created": loop_row.get("graph_andnodes_created", ""),
            "graph_andnodes_reused": loop_row.get("graph_andnodes_reused", ""),
            "graph_andnode_reuse_rate": loop_row.get("graph_andnode_reuse_rate", ""),
            "graph_edge_node_attempts": loop_row.get("graph_edge_node_attempts", ""),
            "graph_edge_nodes_created": loop_row.get("graph_edge_nodes_created", ""),
            "graph_edge_nodes_reused": loop_row.get("graph_edge_nodes_reused", ""),
            "graph_edge_node_reuse_rate": loop_row.get("graph_edge_node_reuse_rate", ""),
            "graph_edge_attempts": loop_row.get("graph_edge_attempts", ""),
            "graph_edges_created": loop_row.get("graph_edges_created", ""),
            "graph_edge_reuses": loop_row.get("graph_edge_reuses", ""),
            "graph_edge_reuse_rate": loop_row.get("graph_edge_reuse_rate", ""),
            "or_expansion_attempts": loop_row.get("or_expansion_attempts", ""),
            "or_expansions_started": loop_row.get("or_expansions_started", ""),
            "or_expansion_reuse_rate": loop_row.get("or_expansion_reuse_rate", ""),
            "num_processors": loop_row.get("num_processors", ""),
            "refutation_cache_size": loop_row.get("refutation_cache_size", ""),
            "refutation_cache_hits": loop_row.get("refutation_cache_hits", ""),
            "refutation_cache_misses": loop_row.get("refutation_cache_misses", ""),
            "refutation_cache_hit_rate": loop_row.get("refutation_cache_hit_rate", ""),
            "filter_refutation_checked": loop_row.get("filter_refutation_checked", ""),
            "filter_refutation_refuted": loop_row.get("filter_refutation_refuted", ""),
            "filter_refutation_survived": loop_row.get("filter_refutation_survived", ""),
            "filter_refutation_survival_rate": loop_row.get("filter_refutation_survival_rate", ""),
            "filter_abduction_checked_conjectures": loop_row.get("filter_abduction_checked_conjectures", ""),
            "filter_abduction_used_conjectures": loop_row.get("filter_abduction_used_conjectures", ""),
            "filter_abduction_discarded_conjectures": loop_row.get("filter_abduction_discarded_conjectures", ""),
            "filter_abduction_retention_rate": loop_row.get("filter_abduction_retention_rate", ""),
            "loop_elapsed_sec": loop_row.get("elapsed_sec", ""),
            "abduction_stats_file": loop_row.get("source_file", ""),
        })
        statistic_rows.append(out)
    return statistic_rows

def collect_abduction_decremental_statistics(row: Dict[str, object], stats_dir: str) -> List[dict]:
    """Collect round-level decremental-conjecturing statistics."""
    stats_path = Path(stats_dir) if stats_dir else Path("__missing_abduction_stats__")
    dec_rows = read_csv_rows_from_dir(stats_path, "*.decremental.csv")

    def base_row() -> dict:
        return {
            "method": row.get("method", ""),
            "benchmark": row.get("benchmark", ""),
            "target_id": row.get("target_id", ""),
            "status": row.get("status", ""),
            "error_kind": row.get("error_kind", ""),
            "proof_found": row.get("proof_found", ""),
            "elapsed_sec": row.get("elapsed_sec", ""),
            "timeout": row.get("timeout", ""),
            "threads": row.get("threads", ""),
        }

    out_rows: List[dict] = []
    decremental_columns = ['top_loop_index', 'parent_or_name', 'is_root_or_node', 'decremental_round_index', 'decremental_limit', 'candidate_sets_before', 'selected_sets', 'carried_over_sets', 'skipped_duplicate_sets', 'skipped_subsumed_sets', 'actual_proof_attempts', 'successful_attempts', 'failed_attempts', 'new_sets', 'candidate_sets_after', 'accepted_edges_in_round', 'accepted_edges_so_far', 'selected_cardinality_min', 'selected_cardinality_median', 'selected_cardinality_max', 'attempted_cardinality_min', 'attempted_cardinality_median', 'attempted_cardinality_max', 'next_cardinality_min', 'next_cardinality_median', 'next_cardinality_max', 'selected_depth_min', 'selected_depth_median', 'selected_depth_max', 'attempted_depth_min', 'attempted_depth_median', 'attempted_depth_max', 'next_depth_min', 'next_depth_median', 'next_depth_max', 'decremental_elapsed_sec']
    for dec_row in dec_rows:
        out = base_row()
        for column in decremental_columns:
            out[column] = dec_row.get(column, "")
        out["abduction_decremental_file"] = dec_row.get("source_file", "")
        out_rows.append(out)
    return out_rows



def output_reports_abduction_success(output: str) -> bool:
    return "And we proved the goal." in output


def extract_abduction_internal_elapsed(output: str) -> Optional[float]:
    """Return the time printed by AbductionProver itself, if present.

    This is useful when Isabelle/Sledgehammer leaves background work alive after
    AbductionProver has already printed and written a proof; the external
    evaluator may then kill Isabelle at the hard timeout even though the proof
    was found much earlier.
    """
    matches = re.findall(r"We spent\s+([0-9]+(?:\.[0-9]+)?)\s+seconds\.\s+And we proved the goal\.", output)
    if not matches:
        return None
    try:
        return float(matches[-1])
    except ValueError:
        return None

def classify_error(
    status: str,
    returncode: Optional[int],
    output: str,
    proof_found: bool,
) -> str:
    # A verified proof must take precedence over later timeout/give-up noise.
    # In particular, AbductionProver can print/write a proof and then leave
    # background Sledgehammer/ATP activity that eventually emits "Gave up" or
    # causes the external evaluator to kill Isabelle.
    if proof_found:
        return ""
    if status == "timeout":
        return "timeout"
    if status == "interrupted":
        return "interrupted"
    if returncode == 0:
        return "no_proof"

    lower = output.lower()

    if "inner syntax error" in lower or "outer syntax error" in lower:
        return "syntax_error"
    if "failed to finish proof" in lower:
        return "unfinished_proof"
    if "exception" in lower:
        return "exception"
    if "error" in lower:
        return "error"

    return "nonzero_returncode"


def collect_targets(method_root: Path) -> Dict[str, Path]:
    if not method_root.exists():
        raise RuntimeError(f"Method target directory does not exist: {method_root}")

    targets = sorted(
        p for p in method_root.rglob("*.thy")
        if p.name != "Test_Base.thy" and not p.name.endswith(".thy~")
    )

    result = {}
    for p in targets:
        target_id = p.relative_to(method_root).as_posix()
        result[target_id] = p

    return result


def write_root_file(
    root_file: Path,
    session_name: str,
    logic: str,
    theory_dir: Path,
    theory_stem: str,
) -> None:
    root_file.write_text(
        f"""session {session_name} = {logic} +
  directories
    "{theory_dir}"
  theories
    {theory_stem}
""",
        encoding="utf-8",
    )


def run_one(
    *,
    isabelle: str,
    repo_root: Path,
    out_dir: Path,
    method: str,
    logic: str,
    benchmark: str,
    target_id: str,
    target: Path,
    timeout: int,
    threads: int,
) -> Dict[str, object]:
    session_name = safe_session_name(method, target_id)
    safe_target = safe_name(Path(target_id).with_suffix("").as_posix())

    log_dir = out_dir / "logs" / method
    proof_target_dir = out_dir / "proofs" / method / safe_target
    stats_target_dir = out_dir / "abduction_stats" / safe_target
    tbc_seed_stats_target_dir = out_dir / "tbc_seed_stats" / safe_target
    session_dir = out_dir / "sessions" / method / safe_target

    log_dir.mkdir(parents=True, exist_ok=True)

    if proof_target_dir.exists():
        shutil.rmtree(proof_target_dir)
    proof_target_dir.mkdir(parents=True, exist_ok=True)

    if method in ABDUCTION_LIKE_METHODS:
        if stats_target_dir.exists():
            shutil.rmtree(stats_target_dir)
        stats_target_dir.mkdir(parents=True, exist_ok=True)

    if method in TBC_SEEDED_METHODS:
        if tbc_seed_stats_target_dir.exists():
            shutil.rmtree(tbc_seed_stats_target_dir)
        tbc_seed_stats_target_dir.mkdir(parents=True, exist_ok=True)

    if session_dir.exists():
        shutil.rmtree(session_dir)
    session_dir.mkdir(parents=True, exist_ok=True)

    log_file = log_dir / f"{safe_target}.log"
    theory_dir = target.parent.resolve()

    root_file = session_dir / "ROOT"
    write_root_file(
        root_file=root_file,
        session_name=session_name,
        logic=logic,
        theory_dir=theory_dir,
        theory_stem=target.stem,
    )

    env = os.environ.copy()
    env["PSL_EVAL_MODE"] = "1"
    env["PSL_EVAL_METHOD"] = method
    env["PSL_EVAL_PROOF_DIR"] = str(proof_target_dir)
    if method in ABDUCTION_LIKE_METHODS:
        env["PSL_EVAL_ABDUCTION_STATS_DIR"] = str(stats_target_dir)
    if method in TBC_SEEDED_METHODS:
        env["PSL_EVAL_TBC_PREPROCESS_STATS_DIR"] = str(tbc_seed_stats_target_dir)
    env["PSL_EVAL_TIMEOUT"] = str(timeout)
    env["PSL_EVAL_THREADS"] = str(threads)

    cmd = [
        isabelle,
        "build",
        "-c",
        "-d", str(repo_root),
        "-d", str(session_dir),
        "-o", f"threads={threads}",
        session_name,
    ]

    start = time.time()

    proc = subprocess.Popen(
        cmd,
        cwd=str(repo_root),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        errors="replace",
        env=env,
        start_new_session=True,
    )

    output = ""
    interrupted = False

    try:
        output, _ = proc.communicate(timeout=timeout)
        elapsed = time.time() - start
        status = "ok" if proc.returncode == 0 else "error"

    except subprocess.TimeoutExpired:
        terminate_process_group(proc)
        try:
            output, _ = proc.communicate(timeout=5)
        except Exception:
            output = output or ""
        elapsed = time.time() - start
        status = "timeout"

    except KeyboardInterrupt:
        interrupted = True
        terminate_process_group(proc)
        try:
            output, _ = proc.communicate(timeout=5)
        except Exception:
            output = output or ""
        elapsed = time.time() - start
        status = "interrupted"

    output = output or ""
    log_file.write_text(output, encoding="utf-8", errors="replace")

    proof_paths = sorted(proof_target_dir.glob("*.proof"))
    proof_file_found = bool(proof_paths)

    proof_files: List[str] = []
    proof_num_lines = ""
    total_proof_lines = 0

    if proof_file_found:
        for proof_path in proof_paths:
            total_proof_lines += normalize_proof_file(proof_path)
            proof_files.append(str(proof_path))
        proof_num_lines = str(total_proof_lines)

    abduction_success_after_late_noise = (
        method in ABDUCTION_LIKE_METHODS
        and proof_file_found
        and total_proof_lines > 0
        and output_reports_abduction_success(output)
    )

    proof_found = (
        (status == "ok" and proof_file_found and total_proof_lines > 0)
        or abduction_success_after_late_noise
    )

    if abduction_success_after_late_noise:
        status = "ok"
        internal_elapsed = extract_abduction_internal_elapsed(output)
        if internal_elapsed is not None:
            elapsed = internal_elapsed

    error_kind = classify_error(
        status=status,
        returncode=proc.returncode,
        output=output,
        proof_found=proof_found,
    )

    return {
        "method": method,
        "benchmark": benchmark,
        "target_id": target_id,
        "target_file": str(target),
        "session": session_name,
        "logic": logic,
        "status": status,
        "error_kind": error_kind,
        "elapsed_sec": round(elapsed, 3),
        "returncode": proc.returncode,
        "proof_found": proof_found,
        "proof_file_found": proof_file_found,
        "proof_file": ";".join(proof_files),
        "proof_num_lines": proof_num_lines,
        "log_file": str(log_file),
        "timeout": timeout,
        "threads": threads,
        "abduction_stats_dir": str(stats_target_dir) if method in ABDUCTION_LIKE_METHODS else "",
        "tbc_seed_stats_dir": str(tbc_seed_stats_target_dir) if method in TBC_SEEDED_METHODS else "",
        "interrupted": interrupted,
    }


def main() -> None:
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--generated-root",
        default="Eval/generated",
        help="Root containing generated method-specific targets",
    )
    parser.add_argument(
        "--benchmark",
        required=True,
        help="Benchmark subdirectory, e.g. Prod, Isaplanner, TIP15",
    )
    parser.add_argument(
        "--methods",
        nargs="+",
        default=["psl", "tbc", "abduction", "preprocessed_abduction"],
        choices=["psl", "tbc", "abduction", "preprocessed_abduction"],
    )
    parser.add_argument("--isabelle", default="isabelle")
    parser.add_argument("--root", default=".", help="PSL repository root")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--threads", type=int, default=0)
    parser.add_argument("--out", default="Eval/results")
    parser.add_argument(
        "--target-set",
        choices=["intersection", "union"],
        default="intersection",
        help="Use common targets only, or all targets found in any method",
    )
    parser.add_argument(
        "--order",
        choices=["round-robin", "method-major"],
        default="round-robin",
    )

    args = parser.parse_args()

    repo_root = Path(args.root).resolve()
    generated_root = Path(args.generated_root).resolve()
    out_dir = Path(args.out).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    csv_file = out_dir / "summary.csv"
    abduction_statistics_file = out_dir / "abduction_statistics.csv"
    abduction_decremental_file = out_dir / "abduction_decremental_statistics.csv"
    tbc_seed_preprocessing_file = out_dir / "tbc_seed_preprocessing_statistics.csv"

    targets_by_method: Dict[str, Dict[str, Path]] = {}

    for method in args.methods:
        method_root = generated_root / method / args.benchmark
        targets_by_method[method] = collect_targets(method_root)

    target_sets: List[Set[str]] = [
        set(targets_by_method[method].keys())
        for method in args.methods
    ]

    if args.target_set == "intersection":
        target_ids = sorted(set.intersection(*target_sets))
    else:
        target_ids = sorted(set.union(*target_sets))

    if not target_ids:
        raise RuntimeError("No target theories found for the selected methods/benchmark.")

    missing = []
    for method in args.methods:
        method_targets = set(targets_by_method[method].keys())
        for target_id in target_ids:
            if target_id not in method_targets:
                missing.append((method, target_id))

    if missing and args.target_set == "union":
        print("Some method/target pairs are missing and will be skipped:")
        for method, target_id in missing[:20]:
            print(f"  missing: {method} {target_id}")
        if len(missing) > 20:
            print(f"  ... and {len(missing) - 20} more")

    fieldnames = [
        "method",
        "benchmark",
        "target_id",
        "target_file",
        "session",
        "logic",
        "status",
        "error_kind",
        "elapsed_sec",
        "returncode",
        "proof_found",
        "proof_file_found",
        "proof_file",
        "proof_num_lines",
        "log_file",
        "timeout",
        "threads",
    ]

    with csv_file.open("w", newline="", encoding="utf-8") as csv_out, \
         abduction_statistics_file.open("w", newline="", encoding="utf-8") as abd_out, \
         abduction_decremental_file.open("w", newline="", encoding="utf-8") as dec_out, \
         tbc_seed_preprocessing_file.open("w", newline="", encoding="utf-8") as tbc_seed_out:
        writer = csv.DictWriter(csv_out, fieldnames=fieldnames)
        writer.writeheader()
        abduction_writer = csv.DictWriter(abd_out, fieldnames=ABDUCTION_STATISTICS_FIELDNAMES)
        abduction_writer.writeheader()
        decremental_writer = csv.DictWriter(dec_out, fieldnames=ABDUCTION_DECREMENTAL_FIELDNAMES)
        decremental_writer.writeheader()
        tbc_seed_writer = csv.DictWriter(tbc_seed_out, fieldnames=TBC_SEED_PREPROCESSING_FIELDNAMES)
        tbc_seed_writer.writeheader()

        def run_and_write(method: str, target_id: str) -> bool:
            if target_id not in targets_by_method[method]:
                return False

            logic = DEFAULT_LOGIC[method]
            target = targets_by_method[method][target_id]

            print(
                f"=== [{method}] {target_id} ===",
                flush=True,
            )

            row = run_one(
                isabelle=args.isabelle,
                repo_root=repo_root,
                out_dir=out_dir,
                method=method,
                logic=logic,
                benchmark=args.benchmark,
                target_id=target_id,
                target=target,
                timeout=args.timeout,
                threads=args.threads,
            )

            interrupted = bool(row.pop("interrupted"))
            abduction_stats_dir = str(row.pop("abduction_stats_dir", ""))
            tbc_seed_stats_dir = str(row.pop("tbc_seed_stats_dir", ""))

            writer.writerow(row)
            csv_out.flush()

            if method in ABDUCTION_LIKE_METHODS:
                for abd_stat_row in collect_abduction_statistics(row, abduction_stats_dir):
                    abduction_writer.writerow(abd_stat_row)
                abd_out.flush()
                for dec_stat_row in collect_abduction_decremental_statistics(row, abduction_stats_dir):
                    decremental_writer.writerow(dec_stat_row)
                dec_out.flush()

            if method in TBC_SEEDED_METHODS:
                for tbc_seed_row in collect_tbc_seed_preprocessing_statistics(row, tbc_seed_stats_dir):
                    tbc_seed_writer.writerow(tbc_seed_row)
                tbc_seed_out.flush()

            return interrupted

        interrupted = False

        try:
            if args.order == "round-robin":
                for target_id in target_ids:
                    for method in args.methods:
                        interrupted = run_and_write(method, target_id)
                        if interrupted:
                            break
                    if interrupted:
                        break

            else:
                for method in args.methods:
                    for target_id in target_ids:
                        interrupted = run_and_write(method, target_id)
                        if interrupted:
                            break
                    if interrupted:
                        break

        except KeyboardInterrupt:
            print("Interrupted before launching next Isabelle process.", flush=True)

    print(f"Summary written to: {csv_file}")


if __name__ == "__main__":
    main()