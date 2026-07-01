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
        r"\1prove",
        text,
        count=1,
    )
    text = re.sub(r"(?m)^\s*oops\s*$\n?", "", text, count=1)
    return text


def convert_for_preprocessed_abduction(text: str) -> str:
    text = re.sub(
        r"(?m)^(\s*)(theorem|lemma|corollary|proposition|prove)\b",
        r"\1prove_by_preprocessed_abduction",
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


def convert_theory_text(text: str, method: str) -> str:
    text = replace_imports(text, method)

    if method == "abduction":
        return convert_for_abduction(text)
    if method == "preprocessed_abduction":
        return convert_for_preprocessed_abduction(text)
    if method == "psl":
        return convert_for_psl(text)
    if method == "tbc":
        return convert_for_tbc(text)
    if method == "sledgehammer":
        return convert_for_sledgehammer(text)

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
        dst = target_dir / rel
        dst.parent.mkdir(parents=True, exist_ok=True)

        original = src.read_text(encoding="utf-8")
        converted = convert_theory_text(original, args.method)

        dst.write_text(converted, encoding="utf-8")
        print(f"{src} -> {dst}")


if __name__ == "__main__":
    main()