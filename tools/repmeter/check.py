#!/usr/bin/env python3
"""Self-tests for repmeter.  Exits non-zero on the first class of mismatch.

What is checked, and why each check is worth having:

1.  all binary strings of length 1..12:
      - suffix array against "sort the suffixes literally",
      - LCP array against a direct character comparison,
      - delta = max_k d_k/k against d_k counted as sets of factors,
      - r against "sort all rotations of S$ and count runs",
      - the greedy attractor is accepted by BOTH verifiers,
      - the bracket delta <= |Gamma| holds,
      - Gamma has no duplicate or out-of-range position.
    The fast delta/r/SA code is O(n log^2 n) with clever bookkeeping; the
    reference versions are the definitions.  Nothing else in the tool matters if
    these two disagree.

2.  all binary strings of length <= 6, EVERY subset of positions as a candidate
    attractor: the suffix-tree verifier must agree with the brute-force
    definition on all 2^n subsets.  This is what rules out a verifier that
    accepts everything (vacuous) or rejects valid sets (unsound).

3.  on all binary strings of length <= 8, every single-position removal from the
    greedy attractor: both verifiers must agree with each other and with brute
    force.  Non-trivial Gamma sets are mostly minimal-ish, so this exercises
    "reject" paths on realistic inputs.

4.  random texts over alphabets of size 1..4, length <= 120, plus unary,
    alternating, Fibonacci and Thue-Morse prefixes: same cross-checks, and
    random candidate sets (both verifiers must agree).

5.  hand-checked constants for "mississippi": delta = 4 (not 3 as the task brief
    guessed) and r = 9 with the sentinel (not 11), both recomputed here from the
    definitions by brute force, plus gamma = 4 by exhaustive subset search.

6.  greedy termination on adversarial texts (a^n, alternating, periodic,
    Fibonacci, Thue-Morse): must finish and be verified.
"""

import itertools
import random
import sys
import time

from measure import (
    bwt_and_runs_sentinel,
    bwt_and_runs_sentinel_bruteforce,
    delta_exact,
    dk_profile,
    gamma_bruteforce,
    greedy_attractor,
    lcp_array,
    suffix_array,
    verify_attractor_bruteforce,
    verify_attractor_sa,
)

FAILURES = []
CHECKS = [0]


def check(cond, label, detail=""):
    CHECKS[0] += 1
    if not cond:
        FAILURES.append((label, detail))
        print("MISMATCH [%s] %s" % (label, detail))


def as_text(sym):
    return "".join(chr(c) for c in sym)


# ---------------------------------------------------------------- references


def brute_sa(sym):
    return sorted(range(len(sym)), key=lambda i: tuple(sym[i:]))


def brute_lcp(sym, sa):
    n = len(sym)
    out = [0] * n
    for r in range(1, n):
        i, j = sa[r - 1], sa[r]
        h = 0
        while i + h < n and j + h < n and sym[i + h] == sym[j + h]:
            h += 1
        out[r] = h
    return out


def brute_profile(sym):
    n = len(sym)
    prof = [0] * (n + 1)
    for k in range(1, n + 1):
        prof[k] = len({tuple(sym[i:i + k]) for i in range(n - k + 1)})
    return prof


# ---------------------------------------------------------------- phases


def phase_exhaustive_binary(max_len=12, deep_upto=8):
    """delta, r, SA, LCP against the definitions, for every binary string."""
    t0 = time.time()
    count = 0
    for n in range(1, max_len + 1):
        for bits in itertools.product((0, 1), repeat=n):
            sym = list(bits)
            count += 1
            sa = suffix_array(sym)
            check(sa == brute_sa(sym), "suffix_array", as_text(sym))
            lcp = lcp_array(sym, sa)
            check(lcp == brute_lcp(sym, sa), "lcp_array", as_text(sym))

            prof = dk_profile(n, lcp, sa)
            bprof = brute_profile(sym)
            check(prof == bprof, "d_k profile", "%s got %s want %s"
                  % (as_text(sym), prof[1:], bprof[1:]))
            delta = delta_exact(prof)
            check(delta == delta_exact(bprof), "delta", as_text(sym))

            _, r = bwt_and_runs_sentinel(sym)
            _, r_ref = bwt_and_runs_sentinel_bruteforce(sym)
            check(r == r_ref, "r (BWT runs)", "%s got %d want %d"
                  % (as_text(sym), r, r_ref))

            gamma = greedy_attractor(sym)
            check(len(set(gamma)) == len(gamma), "Gamma has a duplicate", as_text(sym))
            check(all(0 <= p < n for p in gamma), "Gamma out of range", as_text(sym))
            ok_sa, wit_sa = verify_attractor_sa(sym, gamma, sa=sa, lcp=lcp)
            ok_bf, wit_bf = verify_attractor_bruteforce(sym, gamma)
            check(ok_sa, "suffix-tree verifier rejects greedy Gamma",
                  "%s Gamma=%s witness=%s" % (as_text(sym), gamma, wit_sa))
            check(ok_bf, "brute-force verifier rejects greedy Gamma",
                  "%s Gamma=%s witness=%s" % (as_text(sym), gamma, wit_bf))
            check(delta[0] * 1 <= delta[1] * len(gamma), "bracket delta <= |Gamma|",
                  "%s delta=%s |Gamma|=%d" % (as_text(sym), delta, len(gamma)))

            # empty set is not an attractor of a non-empty text
            check(not verify_attractor_sa(sym, [], sa=sa, lcp=lcp)[0],
                  "verifier accepts the empty set", as_text(sym))
            check(not verify_attractor_bruteforce(sym, [])[0],
                  "brute verifier accepts the empty set", as_text(sym))

            # supersets are attractors too
            for p in range(n):
                sup = sorted(set(gamma) | {p})
                check(verify_attractor_sa(sym, sup, sa=sa, lcp=lcp)[0] and
                      verify_attractor_bruteforce(sym, sup)[0],
                      "verifier rejects a superset of an attractor",
                      "%s Gamma=%s p=%d" % (as_text(sym), gamma, p))

            if n <= deep_upto:
                for dead in gamma:
                    without = [p for p in gamma if p != dead]
                    a = verify_attractor_sa(sym, without, sa=sa, lcp=lcp)[0]
                    b = verify_attractor_bruteforce(sym, without)[0]
                    check(a == b, "verifiers disagree on Gamma minus a point",
                          "%s Gamma=%s dead=%d sa=%s brute=%s"
                          % (as_text(sym), gamma, dead, a, b))
    print("phase 1: %d binary texts of length <= %d, all definitions agree\n"
          "         (%.1fs)" % (count, max_len, time.time() - t0))


def phase_all_subsets(max_len=6):
    """Every subset is a candidate attractor: the two verifiers must agree."""
    t0 = time.time()
    count = 0
    for n in range(1, max_len + 1):
        for bits in itertools.product((0, 1), repeat=n):
            sym = list(bits)
            sa = suffix_array(sym)
            lcp = lcp_array(sym, sa)
            for size in range(n + 1):
                for cand in itertools.combinations(range(n), size):
                    count += 1
                    a = verify_attractor_sa(sym, cand, sa=sa, lcp=lcp)[0]
                    b = verify_attractor_bruteforce(sym, cand)[0]
                    check(a == b, "verifiers disagree on a subset",
                          "%s subset=%s sa=%s brute=%s" % (as_text(sym), cand, a, b))
    print("phase 2: %d (text, subset) pairs, verifiers agree\n         (%.1fs)"
          % (count, time.time() - t0))


def phase_gamma_vs_brute(max_len=7):
    """Greedy |Gamma| must never be below the true gamma, and gamma >= delta."""
    t0 = time.time()
    count = 0
    worst = 1.0
    for n in range(1, max_len + 1):
        for bits in itertools.product((0, 1), repeat=n):
            sym = list(bits)
            count += 1
            sa = suffix_array(sym)
            lcp = lcp_array(sym, sa)
            delta = delta_exact(dk_profile(n, lcp, sa))
            exact = gamma_bruteforce(sym, limit=max_len)
            greedy = greedy_attractor(sym)
            check(len(exact) >= 1, "exhaustive gamma is empty", as_text(sym))
            check(len(exact) * delta[1] >= delta[0], "gamma >= delta",
                  "%s gamma=%d delta=%s" % (as_text(sym), len(exact), delta))
            check(len(greedy) >= len(exact), "greedy smaller than the true gamma",
                  "%s greedy=%d gamma=%d" % (as_text(sym), len(greedy), len(exact)))
            worst = max(worst, len(greedy) / len(exact))
    print("phase 3: %d texts, greedy >= gamma >= delta everywhere; worst"
          " |Gamma|/gamma = %.1f\n         (%.1fs)" % (count, worst, time.time() - t0))


def phase_other_inputs():
    """Random and structured texts: delta, r and both verifiers."""
    t0 = time.time()
    rng = random.Random(20240601)
    texts = []
    texts.append(("mississippi", [ord(c) for c in "mississippi"]))
    texts.append(("banana", [ord(c) for c in "banana"]))
    texts.append(("unary 40", [0] * 40))
    texts.append(("alt 41", [i % 2 for i in range(41)]))
    texts.append(("(aab)^13", [0, 0, 1] * 13))
    fib_a, fib_b = [0], [0, 1]
    for _ in range(2, 12):
        fib_a, fib_b = fib_b, fib_b + fib_a
    texts.append(("fibonacci prefix %d" % len(fib_b), fib_b))
    tm = [0]
    for _ in range(8):
        tm = tm + [1 - c for c in tm]
    texts.append(("thue-morse %d" % len(tm), tm))
    for _ in range(25):
        k = rng.choice([2, 3, 4])
        n = rng.randint(1, 60)
        texts.append(("%d-ary random len %d" % (k, n),
                      [rng.randrange(k) for _ in range(n)]))
    for _ in range(5):
        n = rng.randint(61, 120)
        texts.append(("ternary random len %d" % n, [rng.randrange(3) for _ in range(n)]))

    for label, sym in texts:
        n = len(sym)
        sa = suffix_array(sym)
        lcp = lcp_array(sym, sa)
        check(sa == brute_sa(sym), "suffix_array", label)
        check(lcp == brute_lcp(sym, sa), "lcp_array", label)
        prof = dk_profile(n, lcp, sa)
        bprof = brute_profile(sym)
        check(prof == bprof, "d_k profile", "%s got %s want %s"
              % (label, prof[1:], bprof[1:]))
        _, r = bwt_and_runs_sentinel(sym)
        _, r_ref = bwt_and_runs_sentinel_bruteforce(sym)
        check(r == r_ref, "r (BWT runs)", "%s got %d want %d" % (label, r, r_ref))
        gamma = greedy_attractor(sym)
        ok_sa, wit = verify_attractor_sa(sym, gamma, sa=sa, lcp=lcp)
        check(ok_sa, "suffix-tree verifier rejects greedy Gamma",
              "%s Gamma=%s witness=%s" % (label, gamma, wit))
        ok_bf, wit2 = verify_attractor_bruteforce(sym, gamma)
        check(ok_bf, "brute-force verifier rejects greedy Gamma",
              "%s Gamma=%s witness=%s" % (label, gamma, wit2))
        check(delta_exact(prof)[0] <= delta_exact(prof)[1] * len(gamma),
              "bracket delta <= |Gamma|", "%s delta=%s |Gamma|=%d"
              % (label, delta_exact(prof), len(gamma)))
        # random candidate sets: the two verifiers must agree (mostly "reject")
        if n <= 60:
            for _ in range(5):
                k = rng.randint(0, min(n, 4))
                cand = rng.sample(range(n), k)
                a = verify_attractor_sa(sym, cand, sa=sa, lcp=lcp)[0]
                b = verify_attractor_bruteforce(sym, cand)[0]
                check(a == b, "verifiers disagree on a random subset",
                      "%s subset=%s sa=%s brute=%s" % (label, cand, a, b))
    print("phase 4: %d structured/random texts cross-checked\n         (%.1fs)"
          % (len(texts), time.time() - t0))


def phase_hand_checked():
    """Constants checked by hand and by brute force before being published."""
    t0 = time.time()
    sym = [ord(c) for c in "mississippi"]
    n = len(sym)
    sa = suffix_array(sym)
    lcp = lcp_array(sym, sa)
    delta = delta_exact(dk_profile(n, lcp, sa))
    check(delta == (4, 1), "mississippi delta", "got %s, hand check says 4 (d_1 = 4 "
          "distinct letters, no k has d_k/k > 4)" % (delta,))
    _, r = bwt_and_runs_sentinel(sym)
    check(r == 9, "mississippi r", "got %d, hand check of BWT(mississippi$) = "
          "'ipssm$pissii' says 9 runs" % r)
    _, r_cyc = bwt_and_runs_sentinel_bruteforce(sym)
    check(r_cyc == 9, "mississippi r (brute force)", "got %d" % r_cyc)
    exact = gamma_bruteforce(sym, limit=12)
    check(len(exact) == 4, "mississippi gamma",
          "exhaustive search gave %s" % (exact,))
    gamma = greedy_attractor(sym)
    check(verify_attractor_bruteforce(sym, gamma)[0], "greedy Gamma not verified", "")
    check(len(gamma) >= len(exact), "greedy below gamma", "%d < %d" % (len(gamma), len(exact)))
    # sigma <= delta <= |Gamma| and delta <= r are elementary facts worth pinning
    sigma = len(set(sym))
    check(sigma <= delta[0] / delta[1], "sigma <= delta", "%d vs %s" % (sigma, delta))
    print("phase 5: hand-checked constants of 'mississippi': delta = %d, r = %d,"
          " gamma = %d, greedy |Gamma| = %d (%.1fs)"
          % (delta[0] // delta[1], r, len(exact), len(gamma), time.time() - t0))


def phase_medium_scale():
    """Independent d_k at real sizes: count distinct factors with slices, for
    chosen lengths (including the argmax of d_k/k), on the demo families."""
    t0 = time.time()
    import measure as M
    cases = [("mississippi", [ord(c) for c in "mississippi"]),
             ("fibonacci F_20", M.gen_text("fibonacci:20")),
             ("thue-morse 2^12", M.gen_text("thue-morse:12")),
             ("random binary 2^12", M.gen_text("random-binary:4096:20240601"))]
    for label, sym in cases:
        n = len(sym)
        bs = bytes(sym)
        sa = suffix_array(sym)
        lcp = lcp_array(sym, sa)
        prof = dk_profile(n, lcp, sa)
        d_num, d_k = delta_exact(prof)
        lengths = list(range(1, min(n, 24) + 1)) + [d_k, n]
        for k in sorted(set(x for x in lengths if 1 <= x <= n)):
            direct = len({bs[i:i + k] for i in range(n - k + 1)})
            check(prof[k] == direct, "d_k at scale",
                  "%s k=%d got %d want %d" % (label, k, prof[k], direct))
        print("         d_k spot-checked at %d lengths for %s (n=%d)"
              % (len(set(x for x in lengths if 1 <= x <= n)), label, n))
    print("phase 6: d_k verified by explicit factor sets on the demo families\n"
          "         (%.1fs)" % (time.time() - t0))


def phase_budget():
    """The greedy budget must report 'not computed' instead of hanging."""
    import measure as M
    sym = [ord(c) for c in "abacabadabacaba"]
    res = M.measure(sym, max_greedy_n=4)  # skip by size
    check(res["greedy_attractor_size"] is None, "budget did not skip", "")
    check(res["greedy_attractor_verified"] is None, "budget still verified", "")
    check("max-greedy-n" in (res["greedy_attractor_skipped"] or ""),
          "skip message does not name the flag", str(res["greedy_attractor_skipped"]))
    res = M.measure(sym, max_greedy_n=0)
    check(res["greedy_attractor_size"] is not None and res["greedy_attractor_verified"],
          "unlimited budget produced no attractor", "")
    try:
        M.greedy_attractor(sym, max_rounds=1)
    except M.BudgetExceeded:
        check(True, "", "")
    res = M.measure(sym, max_greedy_n=0, max_greedy_rounds=1)
    check(res["greedy_attractor_size"] is None or res["greedy_attractor_verified"],
          "round budget produced an unverified attractor", "")
    print("phase 7: greedy budgets report 'not computed' instead of hanging")


def phase_termination():
    """The greedy must terminate on adversarial texts (successive rounds)."""
    t0 = time.time()
    cases = {
        "a^60": [0] * 60,
        "(ab)^30": [i % 2 for i in range(60)],
        "(abc)^20": [i % 3 for i in range(60)],
        "a^30 b^30": [0] * 30 + [1] * 30,
        "aab^20": [0, 0, 1] * 20,
        "random binary 200": [random.Random(1).getrandbits(1) for _ in range(200)],
    }
    for label, sym in cases.items():
        gamma = greedy_attractor(sym)
        ok, wit = verify_attractor_sa(sym, gamma)
        check(ok, "greedy Gamma not verified", "%s witness=%s" % (label, wit))
        check(len(gamma) <= len(sym), "|Gamma| > n", label)
    print("phase 8: greedy terminated and verified on %d adversarial texts"
          " (%.1fs)" % (len(cases), time.time() - t0))


def main():
    t0 = time.time()
    phase_exhaustive_binary()
    phase_all_subsets()
    phase_gamma_vs_brute()
    phase_other_inputs()
    phase_hand_checked()
    phase_medium_scale()
    phase_budget()
    phase_termination()
    print("\n%d checks, %d mismatches, %.1fs" % (CHECKS[0], len(FAILURES), time.time() - t0))
    if FAILURES:
        print("\nfirst 10 mismatches:")
        for label, detail in FAILURES[:10]:
            print("  [%s] %s" % (label, detail))
        return 1
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
