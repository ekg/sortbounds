#!/usr/bin/env bash
# Trust audit. Fails loudly if the audit itself breaks, if any listed theorem
# depends on sorryAx / native_decide, or if the library sources contain an axiom
# declaration or native_decide.
set -euo pipefail
cd "$(dirname "$0")/.."

tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

if ! lake env lean scripts/axioms.lean >"$tmp" 2>&1; then
  echo "FAIL: the axiom audit did not elaborate:" >&2
  grep -m5 -E "error" "$tmp" >&2 || true
  exit 1
fi

if grep -qE "sorryAx|Lean\.ofReduceBool" "$tmp"; then
  echo "FAIL: a listed theorem depends on sorryAx or native_decide:" >&2
  grep -E "sorryAx|Lean\.ofReduceBool" "$tmp" >&2
  exit 1
fi

if grep -rn --include='*.lean' -E "^[[:space:]]*(private[[:space:]]+)?axiom[[:space:]]|native_decide" SortBounds/; then
  echo "FAIL: axiom declaration or native_decide in SortBounds/" >&2
  exit 1
fi

if [ "${1:-}" = "--verbose" ]; then cat "$tmp"; fi
printf 'axiom audit clean: %s theorems, all on propext/Classical.choice/Quot.sound\n' \
  "$(grep -c 'depends on axioms' "$tmp")"
