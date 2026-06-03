#!/usr/bin/env python3
"""Fetch CP problems from DeepMind CodeContests whose Python3 solutions only import `math`.

For each kept problem we save:
    <out>/<problem>/problem.txt              the statement
    <out>/<problem>/solutions/sol_<i>.py     math-only Python3 solutions
    <out>/<problem>/tests/test_<i>.in/.out   the (long) test cases

A solution is kept only if a static scan of its imports finds nothing but `math`. This is a
deliberately conservative pre-filter: solutions that pass the import check may still fail to
convert/compile downstream — those are reported by the convert stage, not here.

Usage:
    python3 cp_harness/fetch.py --num 20 --out cp_harness/dataset
    python3 cp_harness/fetch.py --problems <name1> <name2> --out cp_harness/dataset
"""

import argparse
import ast
import os
import sys
from pathlib import Path

PYTHON3_LANG_ID = 3  # CodeContests language id for Python 3
ALLOWED_IMPORTS = {"math"}


def imported_modules(source):
    """Return the set of top-level module names a Python source imports, or None if it
    does not parse (syntactically invalid solutions are dropped)."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return None
    modules = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                modules.add(alias.name.split(".")[0])
        elif isinstance(node, ast.ImportFrom):
            if node.module:
                modules.add(node.module.split(".")[0])
    return modules


def is_math_only(source):
    """True if the solution parses and imports nothing outside the allowed set."""
    mods = imported_modules(source)
    if mods is None:
        return False
    return mods.issubset(ALLOWED_IMPORTS)


def save_problem(out_dir, name, item, max_solutions):
    prob_name = name.replace("/", "_").replace(" ", "_")
    prob_dir = out_dir / prob_name

    languages = item["solutions"]["language"]
    sources = item["solutions"]["solution"]
    math_only = [
        sources[i]
        for i, lang in enumerate(languages)
        if lang == PYTHON3_LANG_ID and is_math_only(sources[i])
    ]
    if not math_only:
        return False

    all_inputs = (
        item["public_tests"]["input"]
        + item["private_tests"]["input"]
        + item["generated_tests"]["input"]
    )
    all_outputs = (
        item["public_tests"]["output"]
        + item["private_tests"]["output"]
        + item["generated_tests"]["output"]
    )
    if not all_inputs:
        return False

    prob_dir.mkdir(parents=True, exist_ok=True)
    (prob_dir / "problem.txt").write_text(item.get("description", ""))

    sols_dir = prob_dir / "solutions"
    sols_dir.mkdir(exist_ok=True)
    for i, src in enumerate(math_only[:max_solutions]):
        (sols_dir / f"sol_{i}.py").write_text(src)

    tests_dir = prob_dir / "tests"
    tests_dir.mkdir(exist_ok=True)
    for i, (inp, outp) in enumerate(zip(all_inputs, all_outputs)):
        (tests_dir / f"test_{i}.in").write_text(inp)
        (tests_dir / f"test_{i}.out").write_text(outp)

    print(
        f"[+] {prob_name}: {len(math_only[:max_solutions])} math-only solution(s), "
        f"{len(all_inputs)} test(s)"
    )
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default="cp_harness/dataset", help="Output directory")
    parser.add_argument("--num", type=int, default=10, help="Number of problems to keep")
    parser.add_argument(
        "--max-solutions", type=int, default=3, help="Max solutions saved per problem"
    )
    parser.add_argument(
        "--problems", nargs="*", default=None, help="Specific problem names to fetch"
    )
    parser.add_argument(
        "--split", default="test", help="CodeContests split (test/valid/train)"
    )
    args = parser.parse_args()

    try:
        from datasets import load_dataset
    except ImportError:
        print("ERROR: `datasets` not installed. Run: pip install datasets", file=sys.stderr)
        return 1

    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"[*] Streaming CodeContests ({args.split} split)...")
    ds = load_dataset("deepmind/code_contests", split=args.split, streaming=True)

    kept = 0
    scanned = 0
    for item in ds:
        scanned += 1
        name = item["name"]
        if args.problems and name not in args.problems:
            continue
        if save_problem(out_dir, name, item, args.max_solutions):
            kept += 1
        if not args.problems and kept >= args.num:
            break
        if scanned % 50 == 0:
            print(f"    ...scanned {scanned}, kept {kept}")

    print(f"\n[*] Done. Kept {kept} problem(s) with math-only solutions into {out_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
