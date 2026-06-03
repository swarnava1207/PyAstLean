#!/usr/bin/env bash
# End-to-end CP correctness harness: fetch -> convert -> evaluate.
#
# Tests py2lean's robustness/correctness by translating real CodeContests Python solutions
# (math-only imports) to Lean, compiling them, and running them against the problems' long
# test cases — comparing Lean output to the expected output (and to the original Python).
#
# Usage:
#   bash cp_harness/run_all.sh [NUM_PROBLEMS] [MAX_TESTS_PER_SOL]
#
# Examples:
#   bash cp_harness/run_all.sh 10          # 10 problems, all tests
#   bash cp_harness/run_all.sh 5 5         # 5 problems, 5 tests each (fast iteration)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

NUM="${1:-10}"
MAX_TESTS="${2:-0}"
DATASET="cp_harness/dataset"

echo "==================================================================="
echo " CP harness:  fetch $NUM problem(s)  ->  convert  ->  evaluate"
echo "==================================================================="

echo ""
echo ">>> [1/3] Fetch"
python3 cp_harness/fetch.py --num "$NUM" --out "$DATASET"

echo ""
echo ">>> [2/3] Convert (Python -> Lean -> compile-check)"
python3 cp_harness/convert.py --dataset "$DATASET"

echo ""
echo ">>> [3/3] Evaluate (run Lean vs Python on test cases)"
EVAL_ARGS=(--dataset "$DATASET")
if [ "$MAX_TESTS" != "0" ]; then
  EVAL_ARGS+=(--max-tests "$MAX_TESTS")
fi
python3 cp_harness/evaluate.py "${EVAL_ARGS[@]}"

echo ""
echo "Done. See $DATASET/eval_report.json for the full breakdown."
