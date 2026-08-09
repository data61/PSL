#!/usr/bin/env python3

import argparse
import re
from pathlib import Path


IMPORTS = {
    "abduction": "imports Main Smart_Isabelle.Smart_Isabelle",
    "preprocessed_abduction": "imports Main Smart_Isabelle.Smart_Isabelle",
    "psl": "imports Main PSL.PSL",
    "tbc": "imports Main TBC.TBC",
    # Keep the Sledgehammer baseline independent of PSL/TBC/Abduction code.
    "sledgehammer": "imports Main",
}


def replace_imports(text: str, method: str) -> str:
    return re.sub(
        r"(?m)^(\s*)imports\b.*$",
        r"\1" + IMPORTS[method],
        text,
        count=1,
    )


def convert_for_abduction(text: str) -> str:
    text = re.sub(
        r"(?m)^(\s*)(theorem|lemma|corollary|proposition)\b",
        r"\1prove_by_abduction",
        text,
        count=1,
    )
    text = re.sub(r"(?m)^\s*oops\s*$\n?", "", text, count=1)
    return text


def convert_for_preprocessed_abduction(text: str) -> str:
    text = re.sub(
        r"(?m)^(\s*)(theorem|lemma|corollary|proposition|prove)\b",
        r"\1prove",
        text,
        count=1,
    )
    text = re.sub(r"(?m)^\s*oops\s*$\n?", "", text, count=1)
    return text

def convert_for_psl(text: str) -> str:
    # PSL needs an active proof state, so keep theorem/lemma and insert try_hard.
    text = re.sub(
        r"(?m)^(\s*)oops\s*$",
        r"\1try_hard\n\1oops",
        text,
        count=1,
    )
    return text


def convert_for_tbc(text: str) -> str:
    # Assumes you add/keep an Isabelle command named evaluate_tbc.
    text = re.sub(
        r"(?m)^(\s*)(theorem|lemma|corollary|proposition)\b",
        r"\1evaluate_tbc",
        text,
        count=1,
    )
    text = re.sub(r"(?m)^\s*oops\s*$\n?", "", text, count=1)
    return text


def convert_for_sledgehammer(text: str) -> str:
    # Direct Sledgehammer baseline, without going through PSL.
    # We keep the original theorem/lemma statement, insert the plain standard
    # Sledgehammer command in the active proof state, and close with oops.
    #
    # Important: We intentionally do NOT bake a timeout into the generated .thy
    # file.  The timeout is supplied at evaluation time via Isabelle's system
    # option "sledgehammer_timeout" in eval_methods_round_robin.py.  This keeps
    # committed targets stable while allowing fair timeout settings per run.
    text = re.sub(
        r"(?m)^(\s*)oops\s*$",
        r"\1sledgehammer\n\1oops",
        text,
        count=1,
    )
    return text


def ensure_theory_end(text: str) -> str:
    """Guarantee a real theory is terminated by a top-level "end".

    TIP_sort_NStoogeSort2Count stops at "oops" and never closes the theory.  That
    is harmless while "oops" is still present, but the abduction/tbc conversions
    above strip it, leaving a theory with no "end" at all -- Isabelle then rejects
    the file with "Malformed theory" only *after* the proof search has run, so the
    target was lost after burning 16m50s for a reason that has nothing to do with
    the prover under evaluation.

    Only files that actually open a theory are touched.  TIP_list_weird_is_normal
    is a seven-line stub containing nothing but the TIP comment header -- no
    "theory ... begin", no statement.  Appending "end" there would produce a file
    that still cannot build ("command \"theory\" expected, but end-of-input was
    found") while looking as though it had been repaired, so it is deliberately
    left alone; that target is unrecoverable without the missing source and fails
    for all methods alike.
    """
    if not re.search(r"(?m)^\s*theory\b", text):
        return text
    if re.search(r"(?m)^\s*end\s*$", text):
        return text
    return text.rstrip() + "\n\nend\n"


def convert_theory_text(text: str, method: str) -> str:
    text = replace_imports(text, method)

    if method == "abduction":
        return ensure_theory_end(convert_for_abduction(text))
    if method == "preprocessed_abduction":
        return ensure_theory_end(convert_for_preprocessed_abduction(text))
    if method == "psl":
        return ensure_theory_end(convert_for_psl(text))
    if method == "tbc":
        return ensure_theory_end(convert_for_tbc(text))
    if method == "sledgehammer":
        return ensure_theory_end(convert_for_sledgehammer(text))

    raise ValueError(f"unknown method: {method}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--method", required=True,
                        choices=["abduction", "preprocessed_abduction", "psl", "tbc", "sledgehammer"])
    parser.add_argument("source_dir")
    parser.add_argument("target_dir")
    args = parser.parse_args()

    source_dir = Path(args.source_dir).resolve()
    target_dir = Path(args.target_dir).resolve()

    for src in sorted(source_dir.rglob("*.thy")):
        if src.name == "Test_Base.thy" or src.name.endswith(".thy~"):
            continue

        rel = src.relative_to(source_dir)
        # Some benchmark trees contain an extra same-named wrapper directory,
        # e.g. UR/TIP/TIP15/TIP15/*.thy while the desired output root is
        # Eval/generated/<method>/TIP15.  Avoid generating
        # Eval/generated/<method>/TIP15/TIP15/*.thy in such cases.
        if rel.parts and rel.parts[0] == source_dir.name and target_dir.name == source_dir.name:
            rel = Path(*rel.parts[1:])
        dst = target_dir / rel
        dst.parent.mkdir(parents=True, exist_ok=True)

        original = src.read_text(encoding="utf-8")
        converted = convert_theory_text(original, args.method)

        dst.write_text(converted, encoding="utf-8")
        print(f"{src} -> {dst}")


if __name__ == "__main__":
    main()