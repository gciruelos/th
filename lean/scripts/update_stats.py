#!/usr/bin/env python3
"""Regenerate README source counts and elaborated theorem-proof DAG sizes."""

from __future__ import annotations

import argparse
from collections import Counter
import html
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
BEGIN = "<!-- BEGIN GENERATED FILE STATS -->"
END = "<!-- END GENERATED FILE STATS -->"


def code_only(source: str) -> str:
    """Mask nested comments and quoted text, preserving line boundaries."""
    code = []
    i = 0
    depth = 0
    while i < len(source):
        start = i
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            code.append(" ")
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
            code.append(" ")
        elif source[i] == "r" and (raw := re.match(r'r(#+)"', source[i:])) is not None:
            delimiter = '"' + raw[1]
            end = source.find(delimiter, i + raw.end())
            i = len(source) if end < 0 else end + len(delimiter)
            code.append(" ")
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            code.append(" ")
        elif source[i] == "«":
            end = source.find("»", i + 1)
            i = len(source) if end < 0 else end + 1
            code.append(" ")
        else:
            code.append(source[i])
            i += 1
            continue
        code.append("\n" * source[start:i].count("\n"))
    return "".join(code)


def sorry_count(source: str) -> int:
    return len(re.findall(r"(?<![\w'])sorry(?![\w'])", code_only(source)))


def source_counts(code: str) -> Counter:
    """Count explicit declaration commands, excluding compiler-generated declarations."""
    commands = re.findall(
        r"^[ \t]*(?:@\[[^\]]*\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe|partial|local|nonrec)\s+)*"
        r"(theorem|lemma|def|abbrev|opaque|inductive|structure|class|instance)\b",
        code, re.MULTILINE)
    kinds = Counter(commands)
    return Counter({
        "statements": kinds["theorem"] + kinds["lemma"] + kinds["instance"],
        "definitions": kinds["def"] + kinds["abbrev"] + kinds["opaque"],
        "types": kinds["inductive"] + kinds["structure"] + kinds["class"],
    })


def file_parts(path: Path) -> tuple[str, str]:
    """Factor chapter filenames into their shared prefix and ordered suffix."""
    if path.name.startswith("Chapter0"):
        return "Chapter0", path.name[len("Chapter0"):]
    match = re.fullmatch(r"(Chapter\d+.*?)(Defs|Appendix)?\.lean", path.name)
    if match:
        return match[1], (match[2] or "") + ".lean"
    return path.stem, ".lean"


SUFFIX_ORDER = {"Defs.lean": 0, ".lean": 1, "Appendix.lean": 2, "Lambda.lean": 3}


def file_order(path: Path) -> tuple:
    prefix, suffix = file_parts(path)
    chapter = re.match(r"Chapter(\d+)", prefix)
    return (int(chapter[1]) if chapter else sys.maxsize,
            prefix, SUFFIX_ORDER.get(suffix, 99))


def proof_name(name: str) -> str:
    """Keep generated suffixes, but omit private/module mangling and the Thesis namespace."""
    name = re.sub(r"^_private\..*?\.\d+\.", "", name)
    name = name[len("Thesis."):] if name.startswith("Thesis.") else name
    return html.escape(name).replace("|", "&#124;")


def run(command: list[str]) -> str:
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
        raise RuntimeError(f"Command failed ({result.returncode}): {' '.join(command)}")
    return result.stdout


def generate_table() -> str:
    print("Building Thesis modules...", file=sys.stderr)
    run(["lake", "build"])
    print("Measuring elaborated theorem bodies...", file=sys.stderr)
    output = run(["lake", "env", "lean", "scripts/proof_stats.lean"])
    payloads = [line.split("\t", 1)[1] for line in output.splitlines()
                if line.startswith("THESIS_STATS_JSON\t")]
    if len(payloads) != 1:
        raise RuntimeError(f"Expected one Lean statistics payload, got:\n{output}")
    proofs = {row["module"]: row for row in json.loads(payloads[0])}
    paths = sorted([*(ROOT / "Thesis").rglob("*.lean"), ROOT / "Thesis.lean"], key=file_order)
    rows = ["| Prefix | File | Lines | Statements | Defs | Types | `sorry`s | Max statement DAG (statement) | Max proof DAG (proof) | Theorems with `sorry` |",
            "|:---|:---|---:|---:|---:|---:|---:|:---|:---|:---|"]
    totals = Counter()
    largest = None
    largest_statement = None
    previous_prefix = None
    for path in paths:
        relative = path.relative_to(ROOT)
        module = ".".join(relative.with_suffix("").parts)
        if module not in proofs:
            raise RuntimeError(f"{relative} is not imported by Thesis.lean")
        source = path.read_text(encoding="utf-8")
        code = code_only(source)
        counts = source_counts(code)
        count = len(re.findall(r"(?<![\w'])sorry(?![\w'])", code))
        lines = len(source.splitlines())
        proof = proofs[module]
        prefix, suffix = file_parts(path)
        prefix_cell = f"**{prefix}**" if prefix != previous_prefix else ""
        previous_prefix = prefix
        dag = (f'{proof["max_dag"]:,} (<code>{proof_name(proof["max_declaration"])}</code>)'
               if proof["theorems"] else "—")
        statement_dag = (f'{proof["max_statement_dag"]:,} (<code>{proof_name(proof["max_statement_declaration"])}</code>)'
                         if proof["theorems"] else "—")
        sorries = sorted(set(proof_name(name) for name in proof.get("sorries", [])))
        sorries_cell = ", ".join(f"<code>{name}</code>" for name in sorries) if sorries else "—"
        numeric = [lines, *(counts[key] for key in ("statements", "definitions", "types")), count]
        rows.append(f"| {prefix_cell} | [{suffix}]({relative.as_posix()}) | "
                    + " | ".join(f"{value:,}" for value in numeric)
                    + f" | {statement_dag} | {dag} | {sorries_cell} |")
        totals.update(counts)
        totals.update(lines=lines, sorry=count)
        totals["max_statement_dag"] = max(totals["max_statement_dag"], proof["max_statement_dag"])
        if largest is None or proof["max_dag"] > largest["max_dag"]:
            largest = proof
        if largest_statement is None or proof["max_statement_dag"] > largest_statement["max_statement_dag"]:
            largest_statement = proof
    sums = [totals[key] for key in ("lines", "statements", "definitions", "types", "sorry")]
    rows.append("| **Total / maximum** | | " + " | ".join(f"**{value:,}**" for value in sums)
                + f' | **{totals["max_statement_dag"]:,}** (<code>{proof_name(largest_statement["max_statement_declaration"])}</code>)'
                + f' | **{largest["max_dag"]:,}** (<code>{proof_name(largest["max_declaration"])}</code>) | — |')
    return "\n".join(rows)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Fail if README statistics are stale; do not write.")
    args = parser.parse_args()
    readme = ROOT / "README.md"
    current = readme.read_text(encoding="utf-8")
    if current.count(BEGIN) != 1 or current.count(END) != 1:
        raise RuntimeError("README must contain exactly one generated-statistics marker pair")
    start = current.index(BEGIN) + len(BEGIN)
    stop = current.index(END, start)
    updated = current[:start] + "\n\n" + generate_table() + "\n\n" + current[stop:]
    if args.check:
        if updated != current:
            print("README statistics are stale. Run python3 scripts/update_stats.py", file=sys.stderr)
            return 1
        print("README statistics are current.")
    else:
        readme.write_text(updated, encoding="utf-8")
        print("Updated lean/README.md statistics.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
