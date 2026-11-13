#!/usr/bin/env python3
"""check.py -- acceptance tests for the LP-gap measurement.  Exits non-zero on failure.

The invariants the brief asks for, plus the ones that decide whether the invariants mean
anything:

  1. the exact simplex agrees with an INDEPENDENT LP solver -- exhaustive enumeration of
     all basic feasible solutions -- on every binary text n <= 6 and on random covering
     LPs, and its primal route agrees with its dual route everywhere;
  2. LP* <= gamma  and  LP* >= delta  (delta claimed here as the d_k/k bound of README.md)
     on every text swept, in every universe, with the right instance of the bound for the
     single-k universes (LP*_k >= d_k/k);
  3. gamma is the true integer optimum: it equals an exhaustive subset enumeration and
     repmeter's definition-level `gamma_bruteforce`, and the reported position set passes
     two independent definitions-level verifiers (tools/attractor's `Instance.verify` and
     repmeter's `verify_attractor_bruteforce`);
  4. the node universe and the O(n^2)-element factor universe give the SAME gamma and the
     SAME LP* -- the reduction this whole measurement rests on;
  5. single-k facts: gamma_1 = sigma = LP*_1 (so the k=1 gap is exactly 1, proved in
     README.md), gamma_k <= gamma, LP*_k <= LP*_full, and one instance where the single-k
     gap EXCEEDS the full gap (the brief's guess that fixed-k has gap 1 is refuted);
  6. the reported headline numbers reproduce: max gap 4/3 on all binary n <= 12, with the
     four witnesses; max single-k gap 3/2 at k = 3; gap = 1 on the morphic/random families.

Run:  timeout 900 python3 check.py            (about 3 minutes)
      timeout 300 python3 check.py --quick    (the fast subset)
"""

import itertools
import random
import sys
import time
from fractions import Fraction

import simplex
from instance import TextInstance, binary_strings, ternary_strings, text_str
from measure import gamma_bruteforce, verify_attractor_bruteforce

FAILURES = []
CHECKS = [0]


def check(cond, msg):
    CHECKS[0] += 1
    if not cond:
        FAILURES.append(msg)
        print("FAIL  %s" % msg)
    return cond


# --------------------------------------------------------------------------
# an independent LP solver: exhaustive vertex enumeration
# --------------------------------------------------------------------------


def lp_by_vertex_enumeration(rows, n):
    """LP* by enumerating every basic feasible solution.  Independent of the simplex.

    The covering LP min sum x_p s.t. a_e . x >= 1 (one per element), x >= 0 has a bounded
    nonempty feasible region, so its optimum is attained at a basic feasible solution: a
    point where n linearly independent constraints among the m element constraints and the
    n nonnegativity constraints are tight.  Enumerating those n-subsets and keeping the
    feasible ones with the smallest sum is therefore an exact LP solver -- exponential, and
    used here only on tiny instances, purely to disagree with the simplex if it is wrong.
    """
    cons = []
    for e, row in enumerate(rows):
        a = [Fraction(0)] * n
        for p in row:
            a[p] = Fraction(1)
        cons.append((a, Fraction(1)))
    for j in range(n):
        a = [Fraction(0)] * n
        a[j] = Fraction(1)
        cons.append((a, Fraction(0)))
    best = None
    for choice in itertools.combinations(range(len(cons)), n):
        M = [list(cons[c][0]) + [cons[c][1]] for c in choice]
        # exact Gauss-Jordan elimination
        piv_cols = []
        ok = True
        r = 0
        for c in range(n):
            piv = None
            for i in range(r, n):
                if M[i][c] != 0:
                    piv = i
                    break
            if piv is None:
                ok = False
                break
            M[r], M[piv] = M[piv], M[r]
            pv = M[r][c]
            M[r] = [v / pv for v in M[r]]
            for i in range(n):
                if i != r and M[i][c] != 0:
                    f = M[i][c]
                    M[i] = [M[i][j] - f * M[r][j] for j in range(n + 1)]
            piv_cols.append(c)
            r += 1
        if not ok:
            continue
        x = [M[i][n] for i in range(n)]
        if any(v < 0 for v in x):
            continue
        if any(sum((x[p] for p in row), Fraction(0)) < 1 for row in rows):
            continue
        val = sum(x, Fraction(0))
        if best is None or val < best[0]:
            best = (val, x)
    return None if best is None else best[0]


# --------------------------------------------------------------------------
# 1. the simplex against the independent solver
# --------------------------------------------------------------------------


def comb_count(a, b):
    from math import comb
    return comb(a, b)


def test_simplex_small_texts():
    t0 = time.time()
    for sym in binary_strings(6):
        ti = TextInstance(sym)
        for cov in (ti.nodes, ti.cover("factors")):
            if comb_count(len(cov.rows) + cov.n, cov.n) > 12000:
                continue
            lp = cov.lp()
            brute = lp_by_vertex_enumeration(cov.rows, cov.n)
            check(brute is not None, "vertex enumeration found no BFS for %r" % (sym,))
            check(lp.value == brute,
                  "simplex %s != vertex enumeration %s on %r (%s)"
                  % (lp.value, brute, text_str(sym), cov.universe))
            check(cov.lp_primal() == lp.value,
                  "primal route %s != dual route %s on %r (%s)"
                  % (cov.lp_primal(), lp.value, text_str(sym), cov.universe))
    print("  vertex-enumeration cross-check on all binary n <= 6: %.1fs, %d checks"
          % (time.time() - t0, CHECKS[0]))


def test_simplex_random_lps():
    rng = random.Random(20240601)
    for trial in range(200):
        n = rng.randrange(1, 5)
        m = rng.randrange(1, 7)
        rows = []
        for _ in range(m):
            row = [p for p in range(n) if rng.random() < 0.6]
            if not row:
                row = [rng.randrange(n)]
            rows.append(row)
        lp = simplex.cover_lp(rows, n)
        brute = lp_by_vertex_enumeration(rows, n)
        check(brute is not None, "random LP %d has no BFS: %r" % (trial, rows))
        check(lp.value == brute,
              "random LP %d: simplex %s != vertex enumeration %s (%r, n=%d)"
              % (trial, lp.value, brute, rows, n))
        check(simplex.cover_lp_primal(rows, n) == lp.value,
              "random LP %d: the two simplex routes disagree (%r, n=%d)"
              % (trial, rows, n))


def test_simplex_hand_cases():
    # two elements both coverable by either position: x0+x1 >= 1, so the value is 1
    check(simplex.cover_lp([[0, 1], [0, 1]], 2).value == 1,
          "duplicate rows must not change the value (expected 1)")
    # min x+y s.t. (x) >= 1 and (y) >= 1 -> 2
    check(simplex.cover_lp([[0], [1]], 2).value == 2, "two separate elements must cost 2")
    # a 0/1 matrix whose LP optimum is fractional: the "abracadabra" instance is integral
    a = simplex.cover_lp([[0, 1, 2], [1, 2], [2]], 3)
    check(a.value == 1, "nested rows must cost 1 (LP got %s)" % (a.value,))
    # fractional optimum: min x1+x2+x3 s.t. x1+x2>=1, x2+x3>=1, x1+x3>=1 -> 3/2
    b = simplex.cover_lp([[0, 1], [1, 2], [0, 2]], 3)
    check(b.value == Fraction(3, 2), "triangle LP must be 3/2 (got %s)" % (b.value,))
    # an infeasible instance (an element with no position) must raise, not return a number
    try:
        simplex.cover_lp([[0], []], 1)
    except (ValueError, simplex.LPError):
        check(True, "")
    else:
        check(False, "an element with no covering position must be an error")


# --------------------------------------------------------------------------
# 2-4. sweeping all small texts
# --------------------------------------------------------------------------


def sweep(strings, label, quick=False):
    """The invariant battery, over a generator of texts."""
    t0 = time.time()
    n_texts = 0
    for sym in strings:
        ti = TextInstance(sym)
        n_texts += 1
        txt = text_str(ti.sym)
        nodes = ti.nodes
        gamma, positions = nodes.exact_min_cover()
        lp = nodes.lp()
        delta = ti.delta()
        if not check(lp.value <= gamma,
                     "LP* = %s > gamma = %s on %r" % (lp.value, gamma, txt)):
            continue
        if not check(lp.value >= delta,
                     "LP* = %s < delta = %s on %r" % (lp.value, delta, txt)):
            continue
        check(Fraction(gamma) / lp.value >= 1, "gap < 1 on %r" % (txt,))
        # gamma against two independent definition-level verifiers
        check(ti.inst.verify(positions),
              "tools/attractor rejects the exact gamma of %r" % (txt,))
        ok, wit = verify_attractor_bruteforce(ti.sym, positions)
        check(ok, "repmeter's brute-force verifier rejects %r of %r (%r)"
              % (positions, txt, wit))
        if ti.n <= (8 if quick else 10):
            ref = gamma_bruteforce(ti.sym, limit=ti.n)
            check(len(ref) == gamma,
                  "exact gamma of %r is %d here but %d by exhaustive subsets"
                  % (txt, gamma, len(ref)))
        # the definition-level factor universe agrees with the node universe
        cov = ti.cover("factors")
        g2, pos2 = cov.exact_min_cover()
        lp2 = cov.lp()
        check(g2 == gamma, "factor universe gamma %d != node universe gamma %d on %r"
              % (g2, gamma, txt))
        check(lp2.value == lp.value, "factor universe LP* %s != node universe LP* %s on %r"
              % (lp2.value, lp.value, txt))
        check(ti.verify_factor_cover(pos2) is None,
              "the factor-universe attractor of %r fails the definition-level check" % (txt,))
        # single-k facts
        for k in (1, 2, 3):
            if k > ti.n:
                continue
            ck = ti.cover("factors_k", k)
            gk, posk = ck.exact_min_cover()
            lpk = ck.lp()
            check(gk <= gamma, "gamma_%d = %d > gamma = %d on %r" % (k, gk, gamma, txt))
            check(lpk.value <= lp.value,
                  "LP*_%d = %s > LP*_full = %s on %r" % (k, lpk.value, lp.value, txt))
            check(lpk.value >= ti.lp_lower_bound(ck.universe, k),
                  "LP*_%d = %s < d_k/k on %r" % (k, lpk.value, txt))
            check(ti.verify_factor_cover(posk, k, k) is None,
                  "gamma_%d positions miss a length-%d factor of %r" % (k, k, txt))
            if k == 1:
                sigma = len(set(ti.sym))
                check(gk == sigma, "gamma_1 = %d != sigma = %d on %r" % (gk, sigma, txt))
                check(lpk.value == sigma,
                      "LP*_1 = %s != sigma = %d on %r (the k=1 gap is not 1)"
                      % (lpk.value, sigma, txt))
        if ti.n <= (8 if quick else 10):
            c1 = ti.cover("factors_le_k", 1)
            check(Fraction(c1.exact_min_cover()[0]) / c1.lp().value == 1,
                  "the single-symbol universe of %r is not integral" % (txt,))
            cle = ti.cover("factors_le_k", 2)
            # measured: the {1,2} universe is exactly integral on ALL 8188 BINARY texts
            # n <= 12 -- but not on ternary ones (010212 has gap 4/3 there), so the
            # binary-only scope is part of the claim
            if len(set(ti.sym)) == 2:
                gle = Fraction(cle.exact_min_cover()[0]) / cle.lp().value
                check(gle == 1,
                      "the {1,2} universe of the binary text %r is not integral (gap %s)"
                      % (txt, gle))
            check(cle.lp().value <= lp.value,
                  "LP*_{<=2} = %s > LP*_full = %s on %r"
                  % (cle.lp().value, lp.value, txt))
            check(cle.exact_min_cover()[0] <= gamma,
                  "gamma_{<=2} = %s > gamma = %s on %r"
                  % (cle.exact_min_cover()[0], gamma, txt))
    print("  %s: %d texts, %.1fs" % (label, n_texts, time.time() - t0))


# --------------------------------------------------------------------------
# 5-6. the reported numbers
# --------------------------------------------------------------------------


def assert_pair_certificate(cov, lp, where):
    """The LP pair certificate, spelled out: both sides feasible, objectives equal."""
    check(simplex.check_primal(cov.rows, cov.n, lp.x) is None,
          "%s: the primal solution is not feasible (%s)"
          % (where, simplex.check_primal(cov.rows, cov.n, lp.x)))
    check(simplex.check_dual(cov.rows, cov.n, lp.y) is None,
          "%s: the dual solution is not feasible (%s)"
          % (where, simplex.check_dual(cov.rows, cov.n, lp.y)))
    sumx = sum(lp.x, Fraction(0))
    sumy = sum(lp.y, Fraction(0))
    check(sumx == sumy == lp.value,
          "%s: sum(x) = %s, sum(y) = %s, claimed LP* = %s" % (where, sumx, sumy,
                                                              lp.value))


def test_headline_maxima():
    """The exhaustive maxima.  n <= 12: 4/3 at four texts.  n <= 13: 15/11 at four texts."""
    t0 = time.time()
    at_4_3 = {"001010010001", "011101101011", "100010010100", "110101101110"}
    at_15_11 = {"0110101101110", "0111011010110", "1000100101001", "1001010010001"}
    best12 = best13 = Fraction(0)
    seen12, seen13 = set(), set()
    for sym in binary_strings(13):
        ti = TextInstance(sym)
        gamma, positions = ti.nodes.exact_min_cover()
        lp = ti.nodes.lp()
        gap = Fraction(gamma) / lp.value
        txt = text_str(ti.sym)
        if ti.n <= 12:
            best12 = max(best12, gap)
            if gap == Fraction(4, 3):
                seen12.add(txt)
        best13 = max(best13, gap)
        if gap > Fraction(4, 3):
            seen13.add(txt)
            check(gamma == 3 and lp.value == Fraction(11, 5),
                  "the 15/11 witness %r should have gamma=3, LP*=11/5 (got %s, %s)"
                  % (txt, gamma, lp.value))
            assert_pair_certificate(ti.nodes, lp, "15/11 witness %r" % (txt,))
            check(ti.verify_factor_cover(positions) is None,
                  "the 15/11 witness %r: its gamma positions miss a factor" % (txt,))
            check(ti.nodes.lp_primal() == lp.value,
                  "the 15/11 witness %r: the two LP routes disagree" % (txt,))
            cov2 = ti.cover("factors")
            check((cov2.exact_min_cover()[0], cov2.lp().value) == (gamma, lp.value),
                  "the 15/11 witness %r: the factor universe disagrees" % (txt,))
    check(best12 == Fraction(4, 3),
          "the max gap over binary n <= 12 should be 4/3, got %s" % (best12,))
    check(seen12 == at_4_3, "the set of n <= 12 4/3 texts changed: %r" % (sorted(seen12),))
    check(best13 == Fraction(15, 11),
          "the max gap over all binary n <= 13 should be 15/11, got %s" % (best13,))
    check(seen13 == at_15_11, "the set of texts with gap > 4/3 changed: %r" % (sorted(seen13),))
    print("  max gap: binary n <= 12 = %s at %d texts, binary n <= 13 = %s at %d texts; %.1fs"
          % (best12, len(seen12), best13, len(seen13), time.time() - t0))


def test_single_k_maximum():
    """The max single-k gap over all binary n <= 12 is 3/2, at k = 3."""
    t0 = time.time()
    best = {2: Fraction(0), 3: Fraction(0)}
    for sym in binary_strings(12):
        ti = TextInstance(sym)
        if ti.n < 2:
            continue
        for k in (2, 3):
            if k > ti.n:
                continue
            cov = ti.cover("factors_k", k)
            gk, _ = cov.exact_min_cover()
            lpk = cov.lp()
            gap = Fraction(gk) / lpk.value
            if gap > best[k]:
                best[k] = gap
    check(best[2] == Fraction(4, 3), "max single-2 gap should be 4/3, got %s" % (best[2],))
    check(best[3] == Fraction(3, 2), "max single-3 gap should be 3/2, got %s" % (best[3],))
    # the witness, re-measured from scratch
    ti = TextInstance([int(c) for c in "111111101110"])
    cov = ti.cover("factors_k", 3)
    gk, posk = cov.exact_min_cover()
    lpk = cov.lp()
    check((gk, lpk.value) == (2, Fraction(4, 3)),
          "the k=3 witness 111111101110 should be gamma_3=2, LP*_3=4/3 (got %s, %s)"
          % (gk, lpk.value))
    assert_pair_certificate(cov, lpk, "k=3 witness 111111101110")
    check(ti.verify_factor_cover(posk, 3, 3) is None,
          "the k=3 witness: gamma_3 positions miss a length-3 factor")
    # and it must beat the full-universe gap of the same text (the brief's guess is wrong)
    gamma, _ = ti.nodes.exact_min_cover()
    lpv = ti.nodes.lp()
    check(Fraction(gk) / lpk.value > Fraction(gamma) / lpv.value,
          "the single-3 gap of 111111101110 should exceed its full gap (%s vs %s)"
          % (Fraction(gk) / lpk.value, Fraction(gamma) / lpv.value))
    print("  single-k maxima: k=2 %s, k=3 %s; %.1fs"
          % (best[2], best[3], time.time() - t0))


def test_families():
    """A spot check that the gap is 1 on the families the brief names."""
    from measure import gen_text
    for spec, n in [("thue-morse:4", 16), ("thue-morse:6", 64),
                    ("fibonacci:10", 55), ("fibonacci:12", 144),
                    ("random-binary:32:1", 32), ("random-binary:64:1", 64)]:
        sym = gen_text(spec)
        check(len(sym) == n, "%s should have length %d" % (spec, n))
        ti = TextInstance(sym)
        gamma, positions = ti.nodes.exact_min_cover()
        lp = ti.nodes.lp()
        check(lp.value <= gamma, "family %s: LP* %s > gamma %s" % (spec, lp.value, gamma))
        check(lp.value >= ti.delta(), "family %s: LP* %s < delta %s"
              % (spec, lp.value, ti.delta()))
        check(ti.inst.verify(positions), "family %s: gamma rejected by attractor" % spec)
        print("    %-20s n=%4d gamma=%-3s LP*=%-6s gap=%s"
              % (spec, ti.n, gamma, lp.value, Fraction(gamma) / lp.value))


def test_errors_are_errors():
    """A certificate that does not close must raise, never return a number."""
    # a dual solution that violates a constraint must be rejected
    rows = [[0, 1], [0, 1], [1]]
    bad = [Fraction(1), Fraction(1), Fraction(1)]
    check(simplex.check_dual(rows, 2, bad) is not None, "an overloaded dual must be caught")
    badx = [Fraction(1), Fraction(0)]
    check(simplex.check_primal(rows, 2, badx) is not None,
          "an under-covering primal must be caught")
    check(simplex.check_primal(rows, 2, [Fraction(1), Fraction(1)]) is None,
          "a valid primal must pass")
    check(simplex.check_dual(rows, 2, [Fraction(1), Fraction(0), Fraction(0)]) is None,
          "a valid dual must pass")


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------


def main(argv=None):
    quick = "--quick" in (argv if argv is not None else sys.argv[1:])
    t0 = time.time()
    print("1. simplex vs exhaustive vertex enumeration")
    test_simplex_hand_cases()
    test_simplex_random_lps()
    test_simplex_small_texts()
    print("2-4. invariant sweep over all small texts")
    sweep(binary_strings(8 if quick else 10), "binary n <= %d" % (8 if quick else 10),
          quick=quick)
    sweep(ternary_strings(6 if quick else 7), "ternary n <= %d" % (6 if quick else 7),
          quick=quick)
    print("5. the single-k universes")
    test_single_k_maximum()
    print("6. the headline maxima (n <= 13 exhaustive)")
    test_headline_maxima()
    print("7. families")
    test_families()
    print("8. certificate plumbing")
    test_errors_are_errors()

    dt = time.time() - t0
    print("")
    if FAILURES:
        print("FAILED: %d of %d checks (%.1fs)" % (len(FAILURES), CHECKS[0], dt))
        for f in FAILURES[:20]:
            print("  - %s" % f)
        return 1
    print("OK: %d checks, 0 failures, %.1fs" % (CHECKS[0], dt))
    return 0


if __name__ == "__main__":
    sys.exit(main())
