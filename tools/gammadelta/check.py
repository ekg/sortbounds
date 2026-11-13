#!/usr/bin/env python3
"""check.py -- re-derive every reported number from the text, without tools/attractor.

`scan.py` stands on `tools/attractor` (`Instance.delta`, `Instance.witness`,
`Instance.packing_bound`, `anytime.search`).  This file shares none of that code: it
enumerates the distinct factors by brute force over every window, builds the
crossing-position set `C(f)` of each factor from the windows themselves, and then

  * recomputes `delta = max_k d_k / k` exactly (the *same* number, a different route);
  * re-checks the reported attractor: every distinct factor must have an occurrence
    interval that contains a reported position (the definition, for every factor);
  * re-checks the reported lower bound: the packing factors must have pairwise disjoint
    `C`-sets, so each one forces its own attractor position;
  * recomputes `gamma` by an independent branch and bound over the set-cover instance
    whose universe is *all distinct factors* (not the suffix-tree nodes), for lengths
    where that finishes inside `--node-cap`.

So a row is confirmed when `lb == ub` and (attractor checks, packing checks, delta
agrees) -- and then `gamma` follows from the two sides without trusting the search.  The
independent branch and bound is a bonus cross-check where it terminates.

  python3 check.py --all                       # every stored row
  python3 check.py --text 01011110110111011100 # one text, full brute force
"""

import argparse
import json
import os
import sys
from fractions import Fraction
from math import ceil

_HERE = os.path.dirname(os.path.abspath(__file__))


# --------------------------------------------------------------------------
# the brute-force model: distinct factors, C-sets, delta, gamma
# --------------------------------------------------------------------------


def factor_table(sym):
    """{factor tuple: set of occurrence starts} for every distinct factor of the text."""
    n = len(sym)
    table = {}
    for i in range(n):
        for j in range(i + 1, n + 1):
            table.setdefault(tuple(sym[i:j]), set()).add(i)
    return table


def delta_bruteforce(table):
    """max_k d_k / k, exactly, from the factor table."""
    dk = {}
    for f in table:
        dk[len(f)] = dk.get(len(f), 0) + 1
    best = Fraction(0)
    for k, d in dk.items():
        v = Fraction(d, k)
        if v > best:
            best = v
    return best, dk


def cover_set(f, starts):
    """C(f) = every position crossed by some occurrence of f (definition, no shortcuts)."""
    out = set()
    L = len(f)
    for i in starts:
        out.update(range(i, i + L))
    return out


def is_attractor(sym, positions):
    """True iff every distinct factor of `sym` has an occurrence crossing a position."""
    table = factor_table(sym)
    pts = sorted(set(positions))
    bad = None
    for f, starts in table.items():
        hit = False
        for i in starts:
            for p in pts:
                if i <= p < i + len(f):
                    hit = True
                    break
            if hit:
                break
        if not hit:
            bad = f
            break
    return bad is None, bad


def check_packing(table, factors):
    """The packing certificate: every factor occurs, and the C-sets are pairwise disjoint."""
    sets = []
    for f in factors:
        key = tuple(int(c) for c in f)
        if key not in table:
            return False, "factor %r does not occur in the text" % (key,)
        sets.append(cover_set(key, table[key]))
    for a in range(len(sets)):
        for b in range(a + 1, len(sets)):
            if sets[a] & sets[b]:
                return False, ("factors %r and %r share crossing position %d"
                               % (factors[a], factors[b], min(sets[a] & sets[b])))
    return True, [sorted(s) for s in sets]


def gamma_bruteforce(sym, node_cap=2000000, k_max=None):
    """Smallest attractor size by DFS over *all distinct factors*, or (None, status).

    The branching rule: an uncovered factor f must be crossed by some position of the
    answer, so branching over C(f) is complete.  The factor with the fewest covering
    positions is chosen first; states (uncovered set, slots) are memoized.
    """
    table = factor_table(sym)
    n = len(sym)
    elems = list(table)
    covers = {f: cover_set(f, table[f]) for f in elems}
    by_pos = {p: set() for p in range(n)}
    for f in elems:
        for p in covers[f]:
            by_pos[p].add(f)
    visited = [0]

    def feasible(k):
        memo = set()

        def rec(uncovered, slots):
            if not uncovered:
                return []
            if slots == 0:
                return None
            visited[0] += 1
            if visited[0] > node_cap:
                raise RuntimeError("node cap")
            key = (frozenset(uncovered), slots)
            if key in memo:
                return None
            pick = min(uncovered, key=lambda f: len(covers[f]))
            for p in sorted(covers[pick]):
                nxt = [f for f in uncovered if p not in covers[f]]
                sub = rec(nxt, slots - 1)
                if sub is not None:
                    memo.add(key)
                    return [p] + sub
            memo.add(key)
            return None

        try:
            return rec(elems, k)
        except RuntimeError:
            return "node cap"

    top = n if k_max is None else min(n, k_max)
    for k in range(1, top + 1):
        sol = feasible(k)
        if sol == "node cap":
            return None, "node cap at k=%d (%d stimuli)" % (k, visited[0])
        if sol is not None:
            return sol, "exhaustive DFS"
    return None, "no attractor up to %d" % top


# --------------------------------------------------------------------------
# one row
# --------------------------------------------------------------------------


def check_row(row, gamma_upto=64):
    """Confirm one scan.py row from the text alone.  Returns (ok, list of notes)."""
    notes = []
    sym = [int(c) for c in row["text"]]
    n = len(sym)
    ok = True
    if n != row["n"]:
        return False, ["n mismatch: text is %d, row says %d" % (n, row["n"])]
    table = factor_table(sym)
    delta, dk = delta_bruteforce(table)
    if delta != Fraction(row["delta_num"], row["delta_den"]):
        ok = False
        notes.append("DELTA DISAGREES: brute force %s vs row %s"
                     % (delta, row["delta"]))
    else:
        notes.append("delta = %s (brute force over %d distinct factors)" % (delta, len(table)))
    if int(ceil(delta)) != row["delta_ceil"]:
        ok = False
        notes.append("ceil(delta) disagrees: %d vs %d" % (int(ceil(delta)), row["delta_ceil"]))

    good, bad = is_attractor(sym, row["attractor"])
    if not good:
        ok = False
        notes.append("ATTRACTOR FAILS: factor %r is crossed by no reported position"
                     % (bad,))
    elif len(set(row["attractor"])) != row["ub"]:
        ok = False
        notes.append("attractor size %d != ub %d" % (len(set(row["attractor"])), row["ub"]))
    else:
        notes.append("attractor of size %d verified against every distinct factor"
                     % row["ub"])

    good, detail = check_packing(table, row["packing_factors"])
    if not good:
        ok = False
        notes.append("PACKING FAILS: %s" % (detail,))
    else:
        k = len(row["packing_factors"])
        notes.append("packing of %d pairwise-disjoint C-sets verified, so gamma >= %d"
                     % (k, k))
        if k < row["lb"]:
            ok = False
            notes.append("PACKING WEAKER THAN lb: %d < %d (lb must come from the DFS)"
                         % (k, row["lb"]))
    lb = max(int(ceil(delta)), len(row["packing_factors"]), 1)
    if row["lb"] > max(lb, 1) and "exact tail" not in str(row.get("lb_source", "")):
        ok = False
        notes.append("LB UNSUPPORTED: lb %d > max(ceil delta, packing) = %d"
                     % (row["lb"], lb))

    if n <= gamma_upto and row["lb"] == row["ub"]:
        sol, how = gamma_bruteforce(sym, k_max=row["ub"])
        if sol is None:
            notes.append("independent B&B inconclusive (%s)" % (how,))
        elif len(sol) == row["ub"]:
            notes.append("independent B&B over all distinct factors: gamma = %d" % len(sol))
        else:
            ok = False
            notes.append("INDEPENDENT B&B FOUND SMALLER: gamma <= %d, row says %d"
                         % (len(sol), row["ub"]))
    return ok, notes


def main(argv=None):
    ap = argparse.ArgumentParser(description="re-derive every reported number from the text")
    ap.add_argument("--json", default=os.path.join(_HERE, "results.json"))
    ap.add_argument("--json2", action="append", default=[],
                    help="more state files to check (e.g. results-exhaustive.json)")
    ap.add_argument("--text", help="check a single text (full brute force)")
    ap.add_argument("--gamma-upto", type=int, default=64,
                    help="largest n for the independent branch and bound")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    if args.text:
        sym = [int(c) for c in args.text]
        table = factor_table(sym)
        delta, dk = delta_bruteforce(table)
        print("n      : %d" % len(sym))
        print("factors: %d distinct" % len(table))
        print("d_k    : %s" % dict(sorted(dk.items())))
        print("delta  : %s  (ceil %d)" % (delta, ceil(delta)))
        sol, how = gamma_bruteforce(sym)
        print("gamma  : %s  (%s)" % (None if sol is None else len(sol), how))
        if sol:
            print("        : %s" % (sorted(sol),))
        return 0

    rows = []
    for path in [args.json] + args.json2:
        if not os.path.exists(path):
            print("missing %s" % path)
            continue
        state = json.load(open(path))
        rows.extend(state.get("rows", []))
    seen = set()
    uniq = []
    for row in rows:
        if row["text"] not in seen:
            seen.add(row["text"])
            uniq.append(row)
    print("checking %d distinct texts" % len(uniq))
    bad = 0
    for row in sorted(uniq, key=lambda r: (r["n"], -r["gap_lo"])):
        ok, notes = check_row(row, gamma_upto=args.gamma_upto)
        if not ok:
            bad += 1
        if not args.quiet or not ok:
            print("\n%s n=%d %s delta=%s lb=%d ub=%d gap=%s text=%s"
                  % ("OK  " if ok else "FAIL", row["n"], row["family"], row["delta"],
                     row["lb"], row["ub"],
                     row["gap_lo"] if row["closed"]
                     else "[%d,%d]" % (row["gap_lo"], row["gap_hi"]),
                     row["text"][:60]))
            for note in notes:
                print("      %s" % note)
    print("\n%d/%d rows confirmed independently, %d failed" % (len(uniq) - bad, len(uniq), bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
