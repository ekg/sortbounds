#!/bin/sh
# run.sh -- reproduce results.json, the generated tables, and then re-verify them.
#
#   sh run.sh              sweep (~2 min) + check (~30 s); exits non-zero on failure
#   sh run.sh --no-doc     same, but tolerate a note whose numbers have drifted
#   sh run.sh --quick      sweep + the fast subset of the checks (no DFS re-proofs)
#
# Stage 1 measures 117 texts with tools/attractor's certified bracket and writes
# results.json plus table/verdicts/trends/rates/summary .md files into this directory.
# Stage 2 (check.py) re-derives every bracket endpoint from the text alone and refuses to
# pass unless the tables in docs/research/gamma-delta-table.md are those files verbatim.
#
# Every stage is under `timeout`: this sweep has hung before (a 30-minute lane was lost to
# it), so a hang is a bug, never an invitation to wait.
set -e
cd "$(dirname "$0")"

ALLOW_DOC_DRIFT=""
CHECK_ARGS=""
for arg in "$@"; do
    case "$arg" in
        --no-doc) ALLOW_DOC_DRIFT="--allow-doc-drift" ;;
        --quick)  CHECK_ARGS="--quick" ;;
        *) echo "run.sh: unknown option $arg" >&2; exit 2 ;;
    esac
done

echo "== stage 1: measure the families =="
timeout 3600 python3 run_families.py --base-budget 6 > /dev/null
echo "== stage 2: re-verify every bracket =="
# shellcheck disable=SC2086
timeout 1800 python3 check.py $ALLOW_DOC_DRIFT $CHECK_ARGS
