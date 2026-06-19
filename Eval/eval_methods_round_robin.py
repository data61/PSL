#!/usr/bin/env python3

import argparse
import csv
import os
import random
import signal
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Set


DEFAULT_LOGIC = {
    "abduction": "Smart_Isabelle",
    "psl": "PSL",
    "tbc": "TBC",
}


def terminate_process_group(proc: subprocess.Popen) -> None:
    """
    Terminate the whole process group started by subprocess.Popen(...,
    start_new_session=True).

    This should kill the Isabelle wrapper and its Poly/ML descendants, as long
    as they did not deliberately escape into another process group.
    """
    if proc.poll() is not None:
        return

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


def brutal_kill_isabelle_processes() -> None:
    """
    Last-resort cleanup.

    WARNING:
      This may kill unrelated Isabelle/jEdit/PolyML processes belonging to the
      same user. Use only on a dedicated evaluation machine/session.
    """
    patterns = [
        "poly",
        "PolyML",
        "isabelle build",
        "isabelle process",
    ]

    for pat in patterns:
        subprocess.run(
            ["pkill", "-9", "-f", pat],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )


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


def classify_error(
    status: str,
    returncode: Optional[int],
    output: str,
    proof_found: bool,
) -> str:
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

    result: Dict[str, Path] = {}

    for p in targets:
        target_id = p.relative_to(method_root).as_posix()

        if target_id in result:
            raise RuntimeError(f"Duplicate target id under {method_root}: {target_id}")

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
    kill_all_isabelle_on_abort: bool,
    keep_isabelle_temp: bool,
) -> Dict[str, object]:
    session_name = safe_session_name(method, target_id)
    safe_target = safe_name(Path(target_id).with_suffix("").as_posix())

    log_dir = out_dir / "logs" / method
    proof_target_dir = out_dir / "proofs" / method / safe_target
    session_dir = out_dir / "sessions" / method / safe_target

    log_dir.mkdir(parents=True, exist_ok=True)

    if proof_target_dir.exists():
        shutil.rmtree(proof_target_dir)
    proof_target_dir.mkdir(parents=True, exist_ok=True)

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

    # Use a per-target Isabelle user home so heaps, browser_info, and other
    # Isabelle-side cache files do not accumulate under ~/.isabelle.
    isabelle_home_user = session_dir / "isabelle_home_user"
    if isabelle_home_user.exists():
        shutil.rmtree(isabelle_home_user)
    isabelle_home_user.mkdir(parents=True, exist_ok=True)

    env = os.environ.copy()
    env["ISABELLE_HOME_USER"] = str(isabelle_home_user)
    env["PSL_EVAL_MODE"] = "1"
    env["PSL_EVAL_METHOD"] = method
    env["PSL_EVAL_PROOF_DIR"] = str(proof_target_dir)
    env["PSL_EVAL_TIMEOUT"] = str(timeout)
    env["PSL_EVAL_THREADS"] = str(threads)

    cmd = [
        isabelle,
        "build",
        "-c",
        "-d", str(repo_root),
        "-d", str(session_dir),
        "-o", f"threads={threads}",
        "-o", "browser_info=false",
        "-o", "document=false",
        session_name,
    ]

    print(f"    session: {session_name}", flush=True)
    print(f"    target : {target}", flush=True)
    print(f"    log    : {log_file}", flush=True)

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

        if kill_all_isabelle_on_abort:
            brutal_kill_isabelle_processes()

        try:
            output, _ = proc.communicate(timeout=5)
        except Exception:
            output = output or ""

        elapsed = time.time() - start
        status = "timeout"

    except KeyboardInterrupt:
        interrupted = True
        terminate_process_group(proc)

        if kill_all_isabelle_on_abort:
            brutal_kill_isabelle_processes()

        try:
            output, _ = proc.communicate(timeout=5)
        except Exception:
            output = output or ""

        elapsed = time.time() - start
        status = "interrupted"

    if not keep_isabelle_temp:
        shutil.rmtree(isabelle_home_user, ignore_errors=True)

    output = output or ""
    log_file.write_text(output, encoding="utf-8", errors="replace")

    proof_paths = sorted(proof_target_dir.glob("*.proof"))
    proof_found = bool(proof_paths)

    proof_files: List[str] = []
    proof_num_lines = ""

    if proof_found:
        total_lines = 0

        for proof_path in proof_paths:
            total_lines += normalize_proof_file(proof_path)
            proof_files.append(str(proof_path))

        proof_num_lines = str(total_lines)

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
        "proof_file": ";".join(proof_files),
        "proof_num_lines": proof_num_lines,
        "log_file": str(log_file),
        "timeout": timeout,
        "threads": threads,
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
        default=["psl", "tbc", "abduction"],
        choices=["psl", "tbc", "abduction"],
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
        "--sample-size",
        type=int,
        default=None,
        help=(
            "Randomly evaluate only this many target theories after applying "
            "--target-set. The sample is reproducible with --sample-seed."
        ),
    )
    parser.add_argument(
        "--sample-seed",
        type=int,
        default=0,
        help="Random seed used with --sample-size. Default: 0.",
    )
    parser.add_argument(
        "--selected-targets-out",
        default=None,
        help=(
            "Optional path where the selected target IDs are written, one per line. "
            "Defaults to <out>/selected_targets.txt when --sample-size is used."
        ),
    )
    parser.add_argument(
        "--order",
        choices=["round-robin", "method-major"],
        default="round-robin",
    )
    parser.add_argument(
        "--kill-all-isabelle-on-abort",
        action="store_true",
        help=(
            "After timeout/Ctrl+C, also pkill PolyML/Isabelle processes. "
            "Dangerous if other Isabelle sessions are running."
        ),
    )
    parser.add_argument(
        "--keep-isabelle-temp",
        action="store_true",
        help=(
            "Keep per-target ISABELLE_HOME_USER directories for debugging. "
            "By default they are deleted after each target."
        ),
    )

    args = parser.parse_args()

    repo_root = Path(args.root).resolve()
    generated_root = Path(args.generated_root).resolve()
    out_dir = Path(args.out).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    csv_file = out_dir / "summary.csv"

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

    total_targets_before_sampling = len(target_ids)

    if args.sample_size is not None:
        if args.sample_size <= 0:
            raise RuntimeError("--sample-size must be a positive integer.")
        if args.sample_size > len(target_ids):
            raise RuntimeError(
                f"--sample-size {args.sample_size} exceeds the number of available "
                f"targets after --target-set={args.target_set}: {len(target_ids)}"
            )

        rng = random.Random(args.sample_seed)
        target_ids = sorted(rng.sample(target_ids, args.sample_size))

        selected_targets_out = (
            Path(args.selected_targets_out).resolve()
            if args.selected_targets_out
            else out_dir / "selected_targets.txt"
        )
        selected_targets_out.parent.mkdir(parents=True, exist_ok=True)
        selected_targets_out.write_text(
            "\n".join(target_ids) + "\n",
            encoding="utf-8",
        )
    else:
        selected_targets_out = None

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

    print(f"Benchmark       : {args.benchmark}")
    print(f"Methods         : {' '.join(args.methods)}")
    if args.sample_size is None:
        print(f"Targets         : {len(target_ids)}")
    else:
        print(f"Targets         : {len(target_ids)} sampled from {total_targets_before_sampling}")
        print(f"Sample seed     : {args.sample_seed}")
        print(f"Selected targets: {selected_targets_out}")
    print(f"Order           : {args.order}")
    print(f"Timeout         : {args.timeout}s")
    print(f"Threads         : {args.threads}")
    print(f"Output CSV      : {csv_file}")
    print(f"Brutal cleanup  : {args.kill_all_isabelle_on_abort}")
    print(f"Keep temp files : {args.keep_isabelle_temp}")
    print("")

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
        "proof_file",
        "proof_num_lines",
        "log_file",
        "timeout",
        "threads",
        "sample_size",
        "sample_seed",
        "target_index",
        "targets_total",
    ]

    with csv_file.open("w", newline="", encoding="utf-8") as csv_out:
        writer = csv.DictWriter(csv_out, fieldnames=fieldnames)
        writer.writeheader()

        def run_and_write(method: str, target_id: str) -> bool:
            if target_id not in targets_by_method[method]:
                return False

            logic = DEFAULT_LOGIC[method]
            target = targets_by_method[method][target_id]

            print(f"=== [{method}] {target_id} ===", flush=True)

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
                kill_all_isabelle_on_abort=args.kill_all_isabelle_on_abort,
                keep_isabelle_temp=args.keep_isabelle_temp,
            )

            interrupted = bool(row.pop("interrupted"))

            row["sample_size"] = args.sample_size if args.sample_size is not None else ""
            row["sample_seed"] = args.sample_seed if args.sample_size is not None else ""
            row["target_index"] = target_ids.index(target_id) + 1
            row["targets_total"] = len(target_ids)

            writer.writerow(row)
            csv_out.flush()

            print(
                f"    result : {row['status']}, "
                f"proof_found={row['proof_found']}, "
                f"elapsed={row['elapsed_sec']}s",
                flush=True,
            )
            print("")

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

            if args.kill_all_isabelle_on_abort:
                brutal_kill_isabelle_processes()

    print(f"Summary written to: {csv_file}")

    if interrupted:
        print("Interrupted. Current Isabelle process group was terminated.")
        if args.kill_all_isabelle_on_abort:
            print("Brutal Isabelle/PolyML cleanup was also performed.")


if __name__ == "__main__":
    main()