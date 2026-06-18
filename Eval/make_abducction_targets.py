#!/usr/bin/env python3

import argparse
import re
from pathlib import Path


def convert_theory_text(text: str) -> str:
    text = re.sub(
        r'(?m)^(\s*)imports\s+"\.\./\.\./Test_Base"\s*$',
        r'\1imports Main Smart_Isabelle.Smart_Isabelle',
        text,
    )

    text = re.sub(
        r"(?m)^(\s*)(theorem|lemma|corollary|proposition)\b",
        r"\1prove",
        text,
    )

    text = re.sub(
        r"(?m)^\s*oops\s*$\n?",
        "",
        text,
    )

    return text


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source_dir")
    parser.add_argument("target_dir")
    args = parser.parse_args()

    source_dir = Path(args.source_dir).resolve()
    target_dir = Path(args.target_dir).resolve()

    for src in sorted(source_dir.glob("*.thy")):
        dst = target_dir / src.name
        dst.parent.mkdir(parents=True, exist_ok=True)

        original = src.read_text(encoding="utf-8")
        converted = convert_theory_text(original)

        dst.write_text(converted, encoding="utf-8")
        print(f"{src} -> {dst}")


if __name__ == "__main__":
    main()