#!/usr/bin/env python3

import argparse
import re
from pathlib import Path


IMPORTS = {
    "abduction": "imports Main Smart_Isabelle.Smart_Isabelle",
    "psl": "imports Main PSL.PSL",
    "tbc": "imports Main TBC.TBC",
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


def convert_theory_text(text: str, method: str) -> str:
    text = replace_imports(text, method)

    if method == "abduction":
        return convert_for_abduction(text)
    if method == "psl":
        return convert_for_psl(text)
    if method == "tbc":
        return convert_for_tbc(text)

    raise ValueError(f"unknown method: {method}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--method", required=True,
                        choices=["abduction", "psl", "tbc"])
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