#!/usr/bin/env python3

import argparse
import csv
import os
import signal
import subprocess
import time
from pathlib import Path
from typing import Optional
import shutil


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


def safe_session_name(stem: str) -> str:
    return "Eval_" + "".join(c if c.isalnum() or c == "_" else "_" for c in stem)


def normalize_proof_file(path: Path) -> int:
    text = path.read_text(encoding="utf-8", errors="replace")

    raw_lines = [line.rstrip() for line in text.splitlines()]

    lines = []
    previous_blank = False

    for line in raw_lines:
        blank = (line.strip() == "")

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

    path.write_text("\n".join(lines) + ("\n" if lines else ""),
                    encoding="utf-8")

    proof_num_lines = sum(
        1 for line in lines
        if line.strip()
    )

    return proof_num_lines


def classify_error(status: str, returncode: Optional[int], output: str, proof_found: bool) -> str:
    if proof_found:
        return ""
    if status == "timeout":
        return "timeout"
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("target_dir", help="Directory or single .thy file")
    parser.add_argument("--isabelle", default="isabelle")
    parser.add_argument("--root", default=".", help="PSL repository root")
    parser.add_argument("--logic", default="Smart_Isabelle")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--threads", type=int, default=0)
    parser.add_argument("--out", default="Eval")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    target_dir = Path(args.target_dir).resolve()
    out_dir = Path(args.out).resolve()

    log_dir = out_dir / "logs"
    proof_dir = out_dir / "proofs"
    session_dir = out_dir / "sessions"

    log_dir.mkdir(parents=True, exist_ok=True)
    proof_dir.mkdir(parents=True, exist_ok=True)
    session_dir.mkdir(parents=True, exist_ok=True)

    csv_file = out_dir / "summary.csv"

    if target_dir.is_file():
        targets = [target_dir]
    else:
        targets = sorted(
            p for p in target_dir.rglob("*.thy")
            if p.name != "Test_Base.thy" and not p.name.endswith(".thy~")
        )

    if not targets:
        raise RuntimeError(f"No .thy files found under {target_dir}")

    fieldnames = [
        "target_file",
        "session",
        "status",
        "error_kind",
        "elapsed_sec",
        "returncode",
        "proof_found",
        "proof_file",
        "proof_num_lines",
        "log_file",
    ]

    interrupted = False

    with csv_file.open("w", newline="", encoding="utf-8") as csv_out:
        writer = csv.DictWriter(csv_out, fieldnames=fieldnames)
        writer.writeheader()

        for target in targets:
            session_name = safe_session_name(target.stem)
            print(f"=== Running {target} as session {session_name} ===", flush=True)

            log_file = log_dir / f"{target.stem}.log"
            this_session_dir = session_dir / target.stem
            if this_session_dir.exists():
                shutil.rmtree(this_session_dir)
            this_session_dir.mkdir(parents=True, exist_ok=True)

            theory_dir = target.parent.resolve()

            root_file = this_session_dir / "ROOT"
            root_file.write_text(
                f"""session {session_name} = {args.logic} +
  directories
    "{theory_dir}"
  theories
    {target.stem}
""",
                encoding="utf-8",
            )

            before_proofs = set(proof_dir.glob("*.proof"))

            env = os.environ.copy()
            env["PSL_EVAL_MODE"] = "1"
            env["PSL_EVAL_PROOF_DIR"] = str(proof_dir)
            env["PSL_EVAL_TIMEOUT"] = str(args.timeout)
            env["PSL_EVAL_THREADS"] = str(args.threads)

            cmd = [
                args.isabelle,
                "build",
                "-c",
                "-d", str(root),
                "-d", str(this_session_dir),
                "-o", f"threads={args.threads}",
                session_name,
            ]

            start = time.time()
            proc = subprocess.Popen(
                cmd,
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                errors="replace",
                env=env,
                start_new_session=True,
            )

            output = ""
            try:
                output, _ = proc.communicate(timeout=args.timeout)
                elapsed = time.time() - start
                status = "ok" if proc.returncode == 0 else "error"

            except subprocess.TimeoutExpired:
                terminate_process_group(proc)
                output, _ = proc.communicate()
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

            after_proofs = set(proof_dir.glob("*.proof"))
            new_proofs = sorted(after_proofs - before_proofs)

            proof_file = ""
            proof_num_lines = ""
            proof_found = bool(new_proofs)

            if proof_found:
                proof_path = new_proofs[-1]
                proof_file = str(proof_path)
                proof_num_lines = normalize_proof_file(proof_path)

            error_kind = classify_error(
                status=status,
                returncode=proc.returncode,
                output=output,
                proof_found=proof_found,
            )

            writer.writerow({
                "target_file": str(target),
                "session": session_name,
                "status": status,
                "error_kind": error_kind,
                "elapsed_sec": round(elapsed, 3),
                "returncode": proc.returncode,
                "proof_found": proof_found,
                "proof_file": proof_file,
                "proof_num_lines": proof_num_lines,
                "log_file": str(log_file),
            })
            csv_out.flush()

            if interrupted:
                print("Interrupted. Current Isabelle/PolyML process group was terminated.", flush=True)
                break

    print(f"Summary written to: {csv_file}")


if __name__ == "__main__":
    main()