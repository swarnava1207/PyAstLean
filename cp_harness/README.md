# CP correctness harness

Tests the **robustness and correctness** of py2lean by translating real competitive-programming
Python solutions to Lean, compiling them, and running them against the problems' long test
cases — comparing the Lean program's output to the expected output (and to the original Python).

Only solutions whose imports are limited to `math` are considered, since that is the library
surface py2lean currently maps.

## Pipeline

```
fetch.py    →  download CodeContests problems + math-only Python3 solutions + tests
convert.py  →  wrap → translate to Lean → compile-check   (buckets: ok / convert_fail / compile_fail)
evaluate.py →  run each `ok` Lean program on every test case, compare stdout to expected
```

### One command

```bash
bash cp_harness/run_all.sh 10        # 10 problems, all test cases
bash cp_harness/run_all.sh 5 5       # 5 problems, 5 tests each (fast iteration)
```

### Or stage by stage

```bash
python3 cp_harness/fetch.py    --num 10 --out cp_harness/dataset
python3 cp_harness/convert.py  --dataset cp_harness/dataset
python3 cp_harness/evaluate.py --dataset cp_harness/dataset --max-tests 5
```

## Dataset layout

```
dataset/<problem>/
  problem.txt
  solutions/sol_<i>.py        original math-only Python3 solutions
  tests/test_<i>.in / .out    the (long) CodeContests test cases
  lean/sol_<i>.lean           generated Lean (only if conversion succeeded)
  lean/sol_<i>.status         ok | convert_fail | compile_fail
  lean/sol_<i>.log            stderr from the failing stage (diagnosis)
  eval/sol_<i>.json           per-test pass/fail for the Lean program
dataset/convert_summary.json  conversion coverage across all problems
dataset/eval_report.json      python-vs-lean pass rates across all problems
```

## How it works

- **Wrapping.** Most CP solutions are bare top-level I/O (`n = int(input()); print(...)`),
  which Lean cannot execute at the top level. `convert.py` wraps such code under
  `if __name__ == "__main__":` (keeping imports at module scope) so py2lean emits a runnable
  `def main : IO Unit`. Solutions that already define `main`/use a `__main__` guard are left
  as-is.
- **Compile-check** ensures the generated Lean elaborates before we try to run it.
- **Execution** uses `lake env lean --run`, feeding `test_<i>.in` on stdin. This reloads
  Mathlib (~4s) per invocation, so the harness is a *correctness* tool, not a speed
  benchmark — use `--max-tests` while iterating.
- **Comparison** is the standard CP normalization (strip trailing whitespace per line and
  overall), matching how judges compare output.

## Reading the results

`convert_summary.json` shows how much of the corpus py2lean can translate+compile. The
`compile_fail`/`convert_fail` logs are the actionable output: they pinpoint unsupported
constructs (e.g. `Starred`, unmapped builtins) to prioritize in py2lean.

`eval_report.json` shows, for the solutions that did compile, whether the Lean translation
*preserves correctness* — the Lean pass rate should match the Python baseline.

## Requirements

- `pip install datasets` (HuggingFace) for `fetch.py`.
- A built `py2lean` backend (`lake build py2lean`).
