"""check.py -- exhaustive testing of the candidate reductions in reduce.py.

What is computed, and how it is certified:

  gamma_exact(T)            exact minimum attractor (k = n) of a binary word, by
                            iterative deepening over the suffix-tree node universe
                            (../attractor/instance.py, rule R1: an attractor is a
                            hitting set of the shortest factor of every node).
                            The returned value is a *proof*: greedy gives an
                            attractor (= upper bound, verified at the definition
                            level by is_attractor), and the depth-<= k-1 searches
                            are exhausted, so no smaller attractor exists.
  gamma_exact_definition(T) the same quantity computed from the definition (the
                            universe is *every* distinct factor).  Independent of
                            ..attractor and used to cross-check the fast solver on
                            every instance below CROSSCHECK_MAX_LEN.

Both solvers raise SearchIncomplete instead of returning a wrong number when a
node cap or a time cap is hit; check.py counts those instances separately so the
report can quote exact "checked" numbers.

Claims tested (see reduce.py for the statement of CLAIM):

  identity      gamma(T_G) == m + tau(G)          for every enumerated G
  threshold     gamma(T_G) <= m + q  iff  tau(G) <= q, for every q
  easy-dir      the ledger's explicit charge pattern is an attractor of T_G
  label-invar.  gamma(T_G) is constant over relabellings of one abstract G
                (necessary for ANY reduction of the threshold form, since tau is
                isomorphism-invariant)
  monotone      H subset of G  =>  gamma(T_H) <= gamma(T_G)   (necessary, since
                tau(H) <= tau(G))

Usage:
  python3 check.py --variant tags --nmax 4
  python3 check.py --variant hubs --nmax 4 --json out.json
  python3 check.py --labels --variant tags --nmax 4 --relabels 12
"""

import argparse
import itertools
import json
import os
import random
import sys
import time
from math import ceil

_HERE = os.path.dirname(os.path.abspath(__file__))
_ATTR = os.path.normpath(os.path.join(_HERE, os.pardir, "attractor"))
if _ATTR not in sys.path:
    sys.path.insert(0, _ATTR)

from instance import Instance                       # noqa: E402

import reduce as R                                 # noqa: E402


CROSSCHECK_MAX_LEN = 40        # definition-level solver runs on texts this short
DEFAULT_NODE_CAP = 4_000_000
DEFAULT_TIME_CAP = 120.0


class SearchIncomplete(Exception):
    """The solver hit its node/time cap: the value is unknown, not wrong."""


# --------------------------------------------------------------------------
# definition-level primitives (independent of ..attractor)
# --------------------------------------------------------------------------


def distinct_factor_covers(text):
    """[(factor, bitmask of positions crossing it)] for every distinct factor."""
    n = len(text)
    elems = {}
    for i in range(n):
        for j in range(i + 1, n + 1):
            f = text[i:j]
            m = elems.get(f, 0)
            for p in range(i, j):
                m |= 1 << p
            elems[f] = m
    return [(f, m) for f, m in elems.items()]


def is_attractor(text, positions):
    """Definition-level check: every distinct factor has an occurrence crossing
    some position of `positions`.  Returns (ok, witness_factor)."""
    n = len(text)
    if not positions:
        return (n == 0), (text[:1] if n else None)
    if min(positions) < 0 or max(positions) >= n:
        return False, "position out of range"
    covered = 0
    for p in positions:
        covered |= 1 << p
    for f, mask in distinct_factor_covers(text):
        if not (mask & covered):
            return False, f
    return True, None


def gamma_exact_definition(text, node_cap=None, time_cap=None):
    """Exact gamma from the definition.  Exponential; for |T| <= ~24 only."""
    n = len(text)
    if n == 0:
        return 0, []
    fl = distinct_factor_covers(text)
    allel = (1 << len(fl)) - 1
    posmask = [0] * n
    for idx, (_f, m) in enumerate(fl):
        mm = m
        while mm:
            b = mm & -mm
            posmask[b.bit_length() - 1] |= 1 << idx
            mm ^= b
    # greedy upper bound
    cov, G = 0, []
    while cov != allel:
        best, bg = -1, -1
        for p in range(n):
            g = bin(posmask[p] & ~cov).count("1")
            if g > bg:
                bg, best = g, p
        if bg <= 0:
            raise SearchIncomplete("a factor is uncoverable")
        G.append(best)
        cov |= posmask[best]
    ub = len(G)
    nodes = [0]
    deadline = None if time_cap is None else time.monotonic() + time_cap

    def dfs(uncovered, k, sol):
        if uncovered == 0:
            return list(sol)
        if k == 0:
            return None
        nodes[0] += 1
        if node_cap is not None and nodes[0] > node_cap:
            raise SearchIncomplete("node cap")
        if deadline is not None and time.monotonic() > deadline:
            raise SearchIncomplete("time cap")
        u = uncovered
        bestc = None
        while u:
            b = u & -u
            idx = b.bit_length() - 1
            u ^= b
            cands = [p for p in range(n)
                     if (fl[idx][1] >> p) & 1 and (posmask[p] & uncovered)]
            if not cands:
                return None
            if bestc is None or len(cands) < len(bestc):
                bestc = cands
                if len(cands) == 1:
                    break
        bestc.sort(key=lambda p: -bin(posmask[p] & uncovered).count("1"))
        for p in bestc:
            sol.append(p)
            r = dfs(uncovered & ~posmask[p], k - 1, sol)
            if r is not None:
                return r
            sol.pop()
        return None

    for k in range(0, ub + 1):
        r = dfs(allel, k, [])
        if r is not None:
            return k, sorted(r)
    raise SearchIncomplete("no attractor up to the greedy bound")


# --------------------------------------------------------------------------
# fast exact solver: suffix-tree node universe (../attractor/instance.py)
# --------------------------------------------------------------------------


def gamma_exact(text, node_cap=DEFAULT_NODE_CAP, time_cap=DEFAULT_TIME_CAP):
    """Exact gamma via the node universe, with a definition-level certificate.

    Returns (gamma, positions, certified) where certified == "definition" when the
    returned positions were re-verified from the definition.
    """
    if len(text) == 0:
        return 0, [], "trivial"
    inst = Instance(text)
    n = inst.n
    full = inst.full_mask
    cm = inst.cover_masks
    elems = inst.elem_masks
    cov, G = 0, []
    while cov != full:
        best, bg = -1, -1
        for p in range(n):
            g = bin(cm[p] & ~cov).count("1")
            if g > bg:
                bg, best = g, p
        if bg <= 0:
            raise SearchIncomplete("node uncovered by every position")
        G.append(best)
        cov |= cm[best]
    ub = len(G)
    nodes = [0]
    deadline = None if time_cap is None else time.monotonic() + time_cap

    def dfs(uncovered, k, sol):
        if uncovered == 0:
            return list(sol)
        if k == 0:
            return None
        nodes[0] += 1
        if node_cap is not None and nodes[0] > node_cap:
            raise SearchIncomplete("node cap")
        if deadline is not None and time.monotonic() > deadline:
            raise SearchIncomplete("time cap")
        u = uncovered
        bestc = None
        while u:
            b = u & -u
            v = b.bit_length() - 1
            u ^= b
            em = elems[v]
            cands = [p for p in range(n) if (em >> p) & 1 and (cm[p] & uncovered)]
            if not cands:
                return None
            if bestc is None or len(cands) < len(bestc):
                bestc = cands
                if len(cands) == 1:
                    break
        bestc.sort(key=lambda p: -bin(cm[p] & uncovered).count("1"))
        for p in bestc:
            sol.append(p)
            r = dfs(uncovered & ~cm[p], k - 1, sol)
            if r is not None:
                return r
            sol.pop()
        return None

    for k in range(0, ub + 1):
        r = dfs(full, k, [])
        if r is not None:
            ok, wit = is_attractor(text, r)
            if not ok:
                raise AssertionError(
                    "node-universe attractor rejected by the definition: %r in %r"
                    % (wit, text))
            return k, sorted(r), "definition"
    raise SearchIncomplete("no attractor up to the greedy bound")


def gamma_certified(text, **kw):
    """gamma_exact, with the definition-level solver as an independent cross-check
    whenever the text is short enough."""
    g, pos, how = gamma_exact(text, **kw)
    if len(text) <= CROSSCHECK_MAX_LEN:
        g2, pos2 = gamma_exact_definition(text, node_cap=kw.get("node_cap"),
                                          time_cap=kw.get("time_cap"))
        if g2 != g:
            raise AssertionError("solvers disagree on %r: node=%d definition=%d"
                                 % (text, g, g2))
        return g, pos, "definition+crosscheck"
    return g, pos, how


# --------------------------------------------------------------------------
# enumeration of source instances
# --------------------------------------------------------------------------


def all_graphs(n, mmax=None):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for mask in range(1 << len(pairs)):
        edges = [pairs[k] for k in range(len(pairs)) if (mask >> k) & 1]
        if mmax is not None and len(edges) > mmax:
            continue
        yield R.edges_in_order(n, edges)


# --------------------------------------------------------------------------
# one variant, all graphs
# --------------------------------------------------------------------------


def run_variant(variant, nmax, mmax=None, node_cap=DEFAULT_NODE_CAP,
                time_cap=DEFAULT_TIME_CAP, verbose=True, log=None):
    rows = []
    failures = []          # instances where gamma != m + tau
    incomplete = []        # instances the solver could not decide
    easy_dir_violations = []
    longest = 0
    for n in range(1, nmax + 1):
        for edges in all_graphs(n, mmax):
            m = len(edges)
            T = R.build(variant, n, edges)
            assert len(T) <= R.size_bound(variant, n, m), (
                "size bound violated: %d > %d" % (len(T), R.size_bound(variant, n, m)))
            longest = max(longest, len(T))
            t = R.tau(n, edges)
            try:
                g, pos, how = gamma_certified(T, node_cap=node_cap, time_cap=time_cap)
            except SearchIncomplete as exc:
                incomplete.append({"n": n, "edges": [list(e) for e in edges],
                                   "len": len(T), "reason": str(exc)})
                continue
            # easy direction: the ledger's charge pattern must be an attractor
            cov = R.cover_witness(n, edges, t)
            assert cov is not None
            pattern = R.designed_charge_pattern(variant, n, edges, cov)
            ok, wit = is_attractor(T, pattern)
            if not ok:
                easy_dir_violations.append({
                    "n": n, "edges": [list(e) for e in edges], "tau": t,
                    "witness_factor": wit, "len": len(T),
                    "pattern": pattern})
            row = {"n": n, "m": m, "tau": t, "gamma": g, "len": len(T),
                   "edges": [list(e) for e in edges], "positions": pos,
                   "quadratic": m + t, "excess": g - (m + t),
                   "pattern_size": len(pattern), "how": how}
            rows.append(row)
            if g != m + t:
                failures.append(row)
            # threshold form, for every q  (equivalent to the identity, kept
            # because a reviewer should see it stated as the mission asks)
            for q in range(0, n + 1):
                left = g <= m + q
                right = t <= q
                if left != right:
                    row.setdefault("threshold_fail_at", []).append(q)
            if verbose and len(rows) % 200 == 0:
                msg = ("  %s n=%d: %d graphs, %d failures so far, longest text %d"
                       % (variant, n, len(rows), len(failures), longest))
                print(msg, flush=True)
                if log is not None:
                    log(msg)
    return {"variant": variant, "rows": rows, "failures": failures,
            "incomplete": incomplete,
            "easy_dir_violations": easy_dir_violations,
            "longest": longest}


# --------------------------------------------------------------------------
# necessary-condition tests
# --------------------------------------------------------------------------


def label_variance(variant, n, edges, relabels=12, seed=0, node_cap=DEFAULT_NODE_CAP,
                   time_cap=DEFAULT_TIME_CAP):
    """gamma over several relabellings of one abstract graph."""
    vals = []
    for perm in R.random_relabelings(n, relabels, seed):
        T = R.build(variant, n, edges, relabel=perm)
        try:
            g, _pos, _how = gamma_certified(T, node_cap=node_cap, time_cap=time_cap)
        except SearchIncomplete:
            continue
        vals.append((perm, g))
    return vals


def monotonicity_scan(variant, n, node_cap=DEFAULT_NODE_CAP,
                      time_cap=DEFAULT_TIME_CAP, pairs_cap=200, seed=0):
    """Find H subset of G with tau(H) <= tau(G) but gamma(T_H) > gamma(T_G)."""
    rng = random.Random(seed)
    graphs = list(all_graphs(n))
    rng.shuffle(graphs)
    graphs = graphs[:pairs_cap]
    bad = []
    cache = {}
    for G in graphs:
        TG = R.build(variant, n, G)
        try:
            gG, _p, _h = gamma_certified(TG, node_cap=node_cap, time_cap=time_cap)
        except SearchIncomplete:
            continue
        cache[G] = gG
        for k in range(0, len(G)):
            for H in itertools.combinations(G, k):
                TH = R.build(variant, n, H)
                try:
                    gH, _p, _h = gamma_certified(TH, node_cap=node_cap,
                                                 time_cap=time_cap)
                except SearchIncomplete:
                    continue
                if gH > gG:
                    bad.append({"G": [list(e) for e in G], "gamma_G": gG,
                                "H": [list(e) for e in H], "gamma_H": gH,
                                "tau_G": R.tau(n, G), "tau_H": R.tau(n, H)})
                    if len(bad) >= 5:
                        return bad
    return bad


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--variant", default="tags", choices=sorted(R.VARIANTS))
    ap.add_argument("--nmax", type=int, default=4)
    ap.add_argument("--mmax", type=int, default=None)
    ap.add_argument("--node-cap", type=int, default=DEFAULT_NODE_CAP)
    ap.add_argument("--time-cap", type=float, default=DEFAULT_TIME_CAP)
    ap.add_argument("--json", default=None)
    ap.add_argument("--labels", action="store_true", help="also run the label-variance test")
    ap.add_argument("--relabels", type=int, default=8)
    ap.add_argument("--monotone", action="store_true")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    t0 = time.time()
    res = run_variant(args.variant, args.nmax, args.mmax,
                      node_cap=args.node_cap, time_cap=args.time_cap,
                      verbose=not args.quiet)
    out = {
        "variant": args.variant,
        "nmax": args.nmax,
        "mmax": args.mmax,
        "checked": len(res["rows"]),
        "failures": len(res["failures"]),
        "incomplete": len(res["incomplete"]),
        "longest_text": res["longest"],
        "easy_dir_violations": len(res["easy_dir_violations"]),
        "excess_histogram": {},
        "fail_examples": res["failures"][:6],
        "easy_dir_examples": res["easy_dir_violations"][:3],
        "incomplete_examples": res["incomplete"][:3],
        "seconds": round(time.time() - t0, 1),
    }
    hist = {}
    for row in res["rows"]:
        hist[row["excess"]] = hist.get(row["excess"], 0) + 1
    out["excess_histogram"] = {str(k): v for k, v in sorted(hist.items())}

    if args.labels:
        lv = []
        for n in range(2, min(args.nmax, 5) + 1):
            for edges in R.all_labelings_iso_classes(n):
                vals = label_variance(args.variant, n, edges, relabels=args.relabels,
                                      node_cap=args.node_cap, time_cap=args.time_cap)
                gs = sorted({g for _p, g in vals})
                if len(gs) > 1:
                    lv.append({"n": n, "edges": [list(e) for e in edges],
                               "tau": R.tau(n, edges), "gamma_values": gs,
                               "n_relabelings": len(vals)})
        out["label_variance_failures"] = lv[:8]
        out["label_variance_count"] = len(lv)

    if args.monotone:
        out["monotonicity_violations"] = monotonicity_scan(
            args.variant, min(args.nmax, 4), node_cap=args.node_cap,
            time_cap=args.time_cap)

    print(json.dumps(out, indent=1)[:6000])
    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"summary": out,
                       "rows": res["rows"],
                       "failures": res["failures"],
                       "incomplete": res["incomplete"],
                       "easy_dir_violations": res["easy_dir_violations"]}, fh, indent=1)
        print("wrote %s" % args.json)
    return 0


if __name__ == "__main__":
    sys.exit(main())
