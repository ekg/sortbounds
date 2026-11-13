#!/usr/bin/env python3
"""check.py -- acceptance tests for the attractor search.  Exits non-zero on failure.

The four tests the contract asks for:

  1. every binary string of length <= 12: `verify` accepts the greedy attractor, and
     the exact gamma (exhaustive) is bracketed by [lb, ub];
  2. "mississippi": exact gamma = 4 and the search reaches 4 within budget;
  3. Thue--Morse: the packing bound must exceed delta at some length (reported
     honestly if it never does);
  4. `search` never yields a larger gamma than a previous yield, and never yields
     an unverified one.

plus the checks that make 1-4 mean something:

  * the suffix-tree node universe has exactly as many elements as S has distinct
    factors (otherwise the set-cover instance is not the problem we claim);
  * `Instance.verify` agrees with a raw, window-enumerating reading of the
    definition on every position set (n <= 8) and on random ones above that;
  * `Instance.verify` agrees with repmeter's independent brute-force verifier;
  * `uncovered(gamma) == 0` exactly when `verify(gamma)`, for random gamma;
  * the exact tail's decision procedure agrees with two independent exhaustive
    searches (subset enumeration here, and the deepening in anytime.exact_gamma);
  * every packing bound really is a family of factors with pairwise disjoint
    crossing-position sets (recomputed from the text, not from the masks).

Run:  python3 check.py            (about a minute)
"""

import faulthandler
import itertools
import random
import sys
import time

import anytime
import instance as instmod
from instance import Instance, factor_str

sys.path.insert(0, instmod._REPMETER)
from measure import (                      # noqa: E402
    gamma_bruteforce,
    verify_attractor_bruteforce,
    verify_attractor_sa,
)

FAILURES = []
CHECKS = [0]


def check(cond, msg):
    CHECKS[0] += 1
    if not cond:
        FAILURES.append(msg)
        print("FAIL  %s" % msg)
    return cond


def binary_strings(max_len, min_len=0):
    for length in range(min_len, max_len + 1):
        for bits in itertools.product((0, 1), repeat=length):
            yield list(bits)


# --------------------------------------------------------------------------
# raw definition: every distinct factor, every occurrence, no structure at all
# --------------------------------------------------------------------------


def verify_raw(sym, gamma):
    """The definition with no shared machinery: enumerate windows as tuples."""
    pts = sorted(set(gamma))
    n = len(sym)
    seen = {}
    for k in range(1, n + 1):
        for i in range(n - k + 1):
            key = tuple(sym[i:i + k])
            if seen.get(key) is True:
                continue
            covered = any(p in pts for p in range(i, i + k))
            if covered:
                seen[key] = True
            else:
                seen.setdefault(key, False)
    return all(seen.values())


def raw_uncovered_count(sym, gamma):
    """How many distinct factors the definition says are uncovered."""
    pts = sorted(set(gamma))
    n = len(sym)
    seen = {}
    for k in range(1, n + 1):
        for i in range(n - k + 1):
            key = tuple(sym[i:i + k])
            if seen.get(key) is True:
                continue
            if any(p in pts for p in range(i, i + k)):
                seen[key] = True
            else:
                seen.setdefault(key, False)
    return sum(1 for ok in seen.values() if not ok)


def distinct_factors(sym):
    n = len(sym)
    return {tuple(sym[i:i + k]) for k in range(1, n + 1) for i in range(n - k + 1)}


# --------------------------------------------------------------------------
# 1: the node universe is the distinct-factor universe, and verify is definition
# --------------------------------------------------------------------------


def test_universe_and_verify():
    print("[1] universe == distinct factors, verify == raw definition (n <= 8, all Gamma)")
    t0 = time.time()
    for sym in binary_strings(8, 1):
        inst = Instance(sym)
        factors = distinct_factors(sym)
        owned = sum(v.nfactors for v in inst.nodes)
        check(owned == len(factors),
              "universe size %d != %d distinct factors for %r" % (owned, len(factors), sym))
        # the (node, length) pairs must be a *bijection* with the distinct factors:
        # each node owns the lengths parent_depth+1..depth, all occurring exactly at
        # its SA interval.  Count equality alone would not catch a double count, so
        # compare the realised strings as sets.
        owned = set()
        for v in inst.nodes:
            i = inst.sa[v.lo]
            for length in range(v.min_len, v.depth + 1):
                owned.add(tuple(sym[i:i + length]))
        check(owned == factors,
              "node/length pairs are not the distinct factors of %r (%d vs %d, %d extra)"
              % (sym, len(owned), len(factors), len(owned - factors)))
        check(sum(v.nfactors for v in inst.nodes) == len(owned),
              "a node owns the same factor twice in %r" % (sym,))
        n = len(sym)
        for mask in range(1 << n):
            gamma = [p for p in range(n) if (mask >> p) & 1]
            want = verify_raw(sym, gamma)
            got = inst.verify(gamma)
            check(got == want, "verify(%r) of %r said %s, raw definition says %s"
                  % (sym, gamma, got, want))
            u = inst.uncovered(gamma)
            raw = raw_uncovered_count(sym, gamma)
            check(u == raw, "uncovered(%r) of %r is %d, the definition counts %d"
                  % (sym, gamma, u, raw))
    print("    %d checks, %.1fs" % (CHECKS[0], time.time() - t0))


def test_verify_large_texts():
    print("[1b] verify vs raw definition and vs repmeter brute force, random Gamma")
    t0 = time.time()
    rng = random.Random(7)
    texts = [
        list(b"mississippi"),
        list(b"abracadabra"),
        [0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1],
        [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0],
    ]
    for sym in texts:
        inst = Instance(sym)
        n = inst.n
        for _ in range(40):
            size = rng.randrange(0, min(n, 6) + 1)
            gamma = sorted(rng.sample(range(n), size)) if size else []
            want = verify_raw(sym, gamma)
            check(inst.verify(gamma) == want,
                  "verify disagrees with the raw definition on %r / %r" % (sym, gamma))
            ok_rep, _ = verify_attractor_bruteforce(sym, gamma)
            check(inst.verify(gamma) == ok_rep,
                  "verify disagrees with repmeter's brute force on %r / %r" % (sym, gamma))
    print("    %d checks, %.1fs" % (CHECKS[0], time.time() - t0))


# --------------------------------------------------------------------------
# exhaustive gamma, three ways
# --------------------------------------------------------------------------


def gamma_exhaustive_subsets(sym, limit=12):
    """Smallest attractor by enumerating position subsets by increasing size."""
    n = len(sym)
    if n > limit:
        raise ValueError("too long for subset enumeration")
    inst = Instance(sym)
    if inst.full_mask == 0:
        return []
    for size in range(0, n + 1):
        for comb in itertools.combinations(range(n), size):
            if inst.verify(comb):
                return list(comb)
    return list(range(n))


def lower_bounds(inst):
    delta_int = int(-(-inst.delta().numerator // inst.delta().denominator))
    pack_k, pack_w = inst.packing_bound(seed=0)
    return max(delta_int, pack_k), pack_k, delta_int, pack_w


def test_gamma_bracket_all_short_strings():
    print("[1c] every binary string n <= 12: gamma exact, bracketed, greedy verified")
    t0 = time.time()
    count = 0
    for sym in binary_strings(12):
        if not sym:
            continue
        inst = Instance(sym)
        g = anytime.greedy(inst)
        count += 1
        if not check(inst.verify(g), "greedy attractor of %r fails verify" % (sym,)):
            continue
        g = anytime.prune(inst, g)
        check(inst.verify(g), "pruned greedy of %r fails verify" % (sym,))
        lb, pack_k, delta_int, pack_w = lower_bounds(inst)
        # exhaustive gamma two ways: my complete DFS and subset enumeration
        exact, _ = anytime.exact_gamma(inst, node_cap=10 ** 9, lb=lb)
        check(exact is not None, "exact_gamma gave up on %r" % (sym,))
        if exact is None:
            continue
        if len(sym) <= 12:
            brute = gamma_exhaustive_subsets(sym)
            check(len(brute) == len(exact),
                  "DFS gamma %d != subset-enumeration gamma %d for %r"
                  % (len(exact), len(brute), sym))
            ok_rep, _ = verify_attractor_bruteforce(sym, exact)
            check(ok_rep, "exhaustive gamma of %r rejected by repmeter" % (sym,))
        check(lb <= len(exact), "lower bound %d > gamma %d for %r" % (lb, len(exact), sym))
        check(len(exact) <= len(g), "gamma %d > greedy %d for %r"
              % (len(exact), len(g), sym))
        check(pack_k <= len(exact), "packing %d > gamma %d for %r"
              % (pack_k, len(exact), sym))
        ok_pack, _ = inst.certify_packing(pack_w)
        check(ok_pack, "packing certificate of %r does not re-check" % (sym,))
    print("    %d strings, %d checks, %.1fs" % (count, CHECKS[0], time.time() - t0))


def test_gamma_bruteforce_agreement():
    print("[1d] exact_gamma == repmeter gamma_bruteforce on binary strings n <= 10")
    t0 = time.time()
    for sym in binary_strings(10):
        if not sym:
            continue
        inst = Instance(sym)
        lb, _, _, _ = lower_bounds(inst)
        exact, _ = anytime.exact_gamma(inst, node_cap=10 ** 9, lb=lb)
        ref = gamma_bruteforce(sym)
        check(len(exact) == len(ref), "exact_gamma %d != gamma_bruteforce %d for %r"
              % (len(exact), len(ref), sym))
    print("    %d checks, %.1fs" % (CHECKS[0], time.time() - t0))


# --------------------------------------------------------------------------
# 2: mississippi
# --------------------------------------------------------------------------


def test_mississippi():
    print("[2] mississippi: exact gamma 4, search reaches 4 within budget")
    sym = list(b"mississippi")
    inst = Instance(sym)
    exact = gamma_bruteforce(sym)
    check(len(exact) == 4, "expected gamma = 4 for mississippi, got %d" % len(exact))
    steps = list(anytime.search(inst, budget_s=5.0))
    final = steps[-1]
    check(final["ub"] == 4, "search reached ub = %d, expected 4" % final["ub"])
    check(final["lb"] == 4, "search's lower bound is %d, expected 4" % final["lb"])
    check(final["certified_exact"], "mississippi bracket not closed")
    check(inst.verify(final["gamma"]), "search's final gamma fails verify")
    print("    ub=%d lb=%d gamma=%s" % (final["ub"], final["lb"], final["gamma"]))


# --------------------------------------------------------------------------
# 3: packing vs delta on Thue--Morse
# --------------------------------------------------------------------------


def test_packing_beats_delta():
    print("[3] Thue-Morse: does the packing bound ever exceed delta?")
    rows = []
    for k in range(2, 11):
        sym = _thue_morse(k)
        inst = Instance(sym)
        pack_k, pack_w = inst.packing_bound(seed=0)
        ok, _ = inst.certify_packing(pack_w)
        check(ok, "packing certificate for Thue-Morse 2^%d does not re-check" % k)
        d = inst.delta()
        rows.append((k, inst.n, d, pack_k))
        print("    n=%5d delta=%-8s packing=%d %s"
              % (inst.n, str(d), pack_k, "PACKING > DELTA" if pack_k > d else ""))
    beaten = [r for r in rows if r[3] > r[2]]
    check(bool(beaten), "the packing bound never exceeded delta on Thue-Morse")
    print("    packing > delta at n = %s" % [r[1] for r in beaten])


def _thue_morse(k):
    t = [0]
    for _ in range(k):
        t = t + [1 - c for c in t]
    return t


# --------------------------------------------------------------------------
# 4: monotonicity and verifiedness of every yield
# --------------------------------------------------------------------------


def test_search_monotone():
    print("[4] search yields only verified, strictly shrinking attractors")
    t0 = time.time()
    texts = {
        "mississippi": list(b"mississippi"),
        "abracadabra": list(b"abracadabra"),
        "random-64": _random_binary(64, 3),
        "random-200": _random_binary(200, 4),
        "TM-128": _thue_morse(7),
        "fib-89": _fibonacci(11),
    }
    for name, sym in texts.items():
        inst = Instance(sym)
        prev = None
        n_steps = 0
        for step in anytime.search(inst, budget_s=2.0, seed=1):
            n_steps += 1
            check(set(step) >= {"t", "gamma", "ub", "lb"}, "%s: yield lacks keys" % name)
            check(step["ub"] == len(step["gamma"]), "%s: ub != len(gamma)" % name)
            check(inst.verify(step["gamma"]), "%s: yielded an unverified gamma" % name)
            check(step["lb"] <= step["ub"], "%s: lb > ub" % name)
            if prev is not None:
                check(step["ub"] <= prev["ub"], "%s: ub grew from %d to %d"
                      % (name, prev["ub"], step["ub"]))
            prev = step
        check(n_steps >= 2, "%s: search yielded only the final record" % name)
        check(prev["done"], "%s: last record is not the final one" % name)
        print("    %-12s %d yields, final ub=%d lb=%d (%.2fs)"
              % (name, n_steps, prev["ub"], prev["lb"], time.time() - t0))


def _random_binary(n, seed):
    rng = random.Random(seed)
    return [rng.getrandbits(1) for _ in range(n)]


def _fibonacci(k):
    """The Fibonacci word of length F_k (w_1 = 0, w_2 = 01, w_{j+1} = w_j w_{j-1})."""
    f_prev, f_cur = 1, 1
    for _ in range(2, k):
        f_prev, f_cur = f_cur, f_prev + f_cur
    target = f_cur
    a, b = [0], [0, 1]
    while len(b) < target:
        a, b = b, b + a
    return b


# --------------------------------------------------------------------------
# the search improves on the greedy (claims in README must be backed)
# --------------------------------------------------------------------------


def test_search_improves_on_greedy():
    print("[5] the search beats its own greedy somewhere, and repmeter's greedy too")
    t0 = time.time()
    cases = [("mississippi", list(b"mississippi")),
             ("random-256", _random_binary(256, 1))]
    improved = 0
    for name, sym in cases:
        inst = Instance(sym)
        g = len(anytime.prune(inst, anytime.greedy(inst)))
        final = list(anytime.search(inst, budget_s=10.0))[-1]
        print("    %-12s greedy+prune=%d  search ub=%d  lb=%d"
              % (name, g, final["ub"], final["lb"]))
        check(final["ub"] <= g, "%s: search is worse than its own greedy" % name)
        improved += 1 if final["ub"] < g else 0
    check(improved > 0, "the search never improved on the greedy")
    print("    %d checks, %.1fs" % (CHECKS[0], time.time() - t0))


# --------------------------------------------------------------------------
# the numbers README.md claims, asserted so they cannot rot
# --------------------------------------------------------------------------


def test_headline_claims():
    print("[6] headline claims: gamma = 4 for Thue-Morse, gamma = 2 for Fibonacci")
    for name, sym, want in (("thue-morse 2^8", _thue_morse(8), 4),
                            ("thue-morse 2^10", _thue_morse(10), 4),
                            ("fibonacci F_14", _fibonacci(14), 2)):
        inst = Instance(sym)
        final = list(anytime.search(inst, budget_s=30.0))[-1]
        check(final["lb"] >= want, "%s: lb %d < %d" % (name, final["lb"], want))
        check(final["ub"] <= want, "%s: ub %d > %d" % (name, final["ub"], want))
        check(inst.verify(final["gamma"]), "%s: final gamma fails verify" % name)
        # repmeter's independent suffix-tree verifier must accept it as well
        ok_sa, wit = verify_attractor_sa(sym, final["gamma"])
        check(ok_sa, "%s: repmeter's verifier rejected %r (%r)"
              % (name, final["gamma"], wit))
        print("    %-16s n=%5d gamma=%d=%d verified twice" % (name, inst.n,
                                                              final["lb"], final["ub"]))


# --------------------------------------------------------------------------
# the lazy greedy is the exhaustive-scan greedy
# --------------------------------------------------------------------------


def test_greedy_lazy_matches_exhaustive():
    print("[7] lazy (CELF) greedy == exhaustive-scan greedy, all binary n <= 12")
    t0 = time.time()
    for sym in binary_strings(12, 1):
        inst = Instance(sym)
        full, cm = inst.full_mask, inst.cover_masks
        covered = 0
        slow = []
        while covered != full:
            best_gain, best_p = 0, None
            for p in range(inst.n):
                gain = bin(cm[p] & ~covered).count("1")
                if gain > best_gain:
                    best_gain, best_p = gain, p
            check(best_gain > 0, "exhaustive greedy stalled on %r" % (sym,))
            slow.append(best_p)
            covered |= cm[best_p]
        fast = anytime.greedy(inst)
        check(fast == slow, "lazy greedy %r != exhaustive greedy %r for %r"
              % (fast, slow, sym))
    print("    %d checks, %.1fs" % (CHECKS[0], time.time() - t0))


def main():
    faulthandler.dump_traceback_later(1800, exit=True)   # never hang
    t0 = time.time()
    test_universe_and_verify()
    test_verify_large_texts()
    test_mississippi()
    test_packing_beats_delta()
    test_search_monotone()
    test_search_improves_on_greedy()
    test_headline_claims()
    test_greedy_lazy_matches_exhaustive()
    test_gamma_bruteforce_agreement()
    test_gamma_bracket_all_short_strings()
    print("\n%d checks, %d failures, %.1fs" % (CHECKS[0], len(FAILURES), time.time() - t0))
    if FAILURES:
        print("FAILED")
        for f in FAILURES[:20]:
            print("  %s" % f)
        return 1
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
