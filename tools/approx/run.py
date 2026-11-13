#!/usr/bin/env python3
"""run.py -- the results table for the LZ77 -> attractor construction.

For every text: n, z (phrase count), delta (exact fraction), |Gamma_LZ|, the two
ratios, and the exact gamma where n <= EXACT_GAMMA_LIMIT.  Every Gamma_LZ is
verified before its size is printed: with the definition-level checker when
n <= DEFINITION_LIMIT and with the O(n log n) node checker on every row (the two
must agree whenever both run).  A row whose construction fails verification or
whose size exceeds z aborts the table -- there is no code path that prints a
ratio for an unverified Gamma.

Texts: "ababa", "mississippi", Fibonacci words F_10 .. F_18, Thue-Morse words of
length 2^12 and 2^16, a^100, a^1000, and a random binary text of length 4096.

Two conventions, both stated on the row so the numbers are checkable:
  * F_1 = "a", F_2 = "ab", F_{k} = F_{k-1} F_{k-2}, so |F_k| = Fib_k with
    Fib_1 = Fib_2 = 1 (the convention of tools/attractor and tools/repmeter).
  * the random text is `random.Random(SEED).getrandbits(1)` for SEED = 1, the
    seed used in the tools/attractor results table.

Usage:  timeout 120 python3 run.py
"""

import random
import sys
import time
from fractions import Fraction

import lz
import verify
from attractor_from_lz import attractor_for_text

DEFINITION_LIMIT = 400      # rows up to this size also get the literal definition check
EXACT_GAMMA_LIMIT = 14      # exact gamma is only computed here (see exact_gamma)


# --------------------------------------------------------------------------
# texts
# --------------------------------------------------------------------------

def fibonacci_word(k):
    """F_1 = a, F_2 = ab, F_{j+1} = F_j F_{j-1}; |F_k| = Fib_k (Fib_1 = Fib_2 = 1)."""
    if k < 1:
        raise ValueError("k >= 1")
    f_prev, f_cur = 1, 1
    for _ in range(2, k):
        f_prev, f_cur = f_cur, f_prev + f_cur
    target = f_cur
    a, b = b"\x00", b"\x00\x01"
    if k == 1:
        return a
    while len(b) < target:
        a, b = b, b + a
        assert len(a) < len(b)               # progress: the words strictly grow
    assert len(b) == target, (len(b), target)
    return b


def thue_morse_word(k):
    """The Thue-Morse word of length 2^k."""
    t = b"\x00"
    for j in range(k):
        t = t + bytes(1 - c for c in t)
        assert len(t) == 1 << (j + 1)         # progress: the length doubles
    assert len(t) == 1 << k
    return t


def random_binary(n, seed):
    rng = random.Random(seed)
    return bytes(rng.getrandbits(1) for _ in range(n))


# --------------------------------------------------------------------------
# exact gamma, by exhaustive hitting set (small n only)
# --------------------------------------------------------------------------

def gamma_bracket(sym, ub, sa, lcp):
    """(lb, ub, exact, witness) for the minimum attractor size of `sym`.

    Both ends are certified, never estimated:
      lb = ceil(delta)   because delta <= gamma holds for every string
                         (KNP23 Lemma II.4) and gamma is an integer;
      ub = |Gamma_LZ|    because that set was verified to be an attractor.
    The bracket is closed, i.e. gamma is known exactly, when lb == ub.  One more
    case can be settled cheaply: if lb == 1, M in at most 1 element means M = {p},
    so trying every singleton decides gamma = 1 or gamma >= 2 (and if a singleton
    is found, exact_gamma's argument is unnecessary: the witness is the attractor).
    Everything else is reported as an open bracket.
    """
    n = len(sym)
    d_num, d_den = verify.delta_pair(sym)
    lb = -((-d_num) // d_den)                 # ceil(delta)
    assert lb >= 1 or n == 0
    if lb >= ub:
        assert lb == ub, "delta > |Gamma_LZ| would contradict KNP23 Lemma II.4"
        return (lb, ub, lb, None)
    if lb == 1:
        for p in range(n):
            assert 0 <= p < n
            if verify.verify_suffix_array(sym, [p], sa, lcp):
                return (1, 1, 1, (p,))
        lb = 2                                # no singleton is an attractor
    return (lb, ub, None, None)


def exact_gamma(sym, limit=EXACT_GAMMA_LIMIT):
    """(gamma, witness positions) -- the minimum attractor size, proved exhaustively.

    Minimum attractor is minimum set cover: the universe is the distinct factors
    and the set of position p covers the factors having an occurrence crossing p.
    Instead of the sets of factors we keep the FACETS: for each distinct factor
    f, facet(f) = the set of positions that cross some occurrence of f.  Gamma is
    an attractor iff it hits every facet(f), so gamma is the minimum hitting set
    of the facets.

    Only the inclusion-minimal facets are kept (hitting a smaller facet hits every
    superset of it), and the minimum is found by iterative deepening: try k = 1,
    2, ... and branch on the positions of one unhit facet.  Exponential, so this
    is only called for n <= limit; nothing else in the tool uses it.
    """
    n = len(sym)
    if n > limit:
        raise ValueError("exact_gamma is exhaustive: n = %d > %d" % (n, limit))
    if n == 0:
        return (0, ())
    facets = set()
    for k in range(1, n + 1):
        groups = {}
        for i in range(n - k + 1):
            groups.setdefault(sym[i:i + k], []).append(i)
        for starts in groups.values():
            cov = set()
            for j in starts:
                cov.update(range(j, j + k))
            facets.add(frozenset(cov))
    minimal = []
    for f in sorted(facets, key=len):
        if not any(g <= f for g in minimal):
            minimal.append(f)
    assert all(f for f in minimal)           # every factor has a covering position
    minimal = [tuple(sorted(f)) for f in minimal]

    def hit(chosen, budget):
        unhit = None
        for f in minimal:
            if not any(p in chosen for p in f):
                unhit = f
                break
        if unhit is None:
            return chosen
        if budget == 0:
            return None
        for p in unhit:
            assert 0 <= p < n
            got = hit(chosen | {p}, budget - 1)
            if got is not None:
                return got
        return None

    for k in range(1, n + 1):
        got = hit(frozenset(), k)
        if got is not None:
            assert len(got) <= k
            return (len(got), tuple(sorted(got)))
    raise AssertionError("unreachable: the full position set hits every facet")


# --------------------------------------------------------------------------
# the table
# --------------------------------------------------------------------------

def measure(label, text):
    """One row: compute, verify, and return a dict of the numbers."""
    t0 = time.time()
    sym = lz.to_bytes(text)
    n = len(sym)
    gamma_lz, phrases = attractor_for_text(sym)
    z = lz.phrase_count(phrases)
    t_lz = time.time() - t0

    t0 = time.time()
    sa = verify.suffix_array(sym) if n else []
    lcp = verify.lcp_array(sym, sa) if n else []
    d_num, d_den = verify.delta_pair(sym)
    dlt = Fraction(d_num, d_den)
    t_delta = time.time() - t0

    # --- verification, before anything is printed -------------------------
    t0 = time.time()
    wit_sa = verify.find_uncovered_factor_suffix_array(sym, gamma_lz, sa, lcp)
    if wit_sa is not None:
        raise SystemExit("FAIL %s: Gamma_LZ is NOT an attractor: factor %r at %d is "
                         "uncovered" % (label, verify.factor_to_text(wit_sa[0]), wit_sa[1]))
    method = "suffix-array"
    if n <= DEFINITION_LIMIT:
        wit_def = verify.find_uncovered_factor_definition(sym, gamma_lz)
        if wit_def != wit_sa:
            raise SystemExit("FAIL %s: the two verifiers disagree (%r vs %r)"
                             % (label, wit_def, wit_sa))
        method = "definition + suffix-array"
    t_verify = time.time() - t0

    if len(gamma_lz) != z:
        raise SystemExit("FAIL %s: |Gamma_LZ| = %d != z = %d" % (label, len(gamma_lz), z))
    if not dlt <= len(gamma_lz):
        raise SystemExit("FAIL %s: delta = %s > |Gamma_LZ| = %d -- this contradicts "
                         "KNP23 Lemma II.4 and must not be reported as a result"
                         % (label, dlt, len(gamma_lz)))

    # gamma: exhaustive when tiny, otherwise a certified bracket (never a guess)
    if n <= EXACT_GAMMA_LIMIT:
        gam, gam_wit = exact_gamma(sym)
        if not verify.verify_definition(sym, gam_wit):
            raise SystemExit("FAIL %s: exact gamma witness %r is not an attractor"
                             % (label, (gam_wit,)))
        if gam > len(gamma_lz):
            raise SystemExit("FAIL %s: exact gamma %d > |Gamma_LZ| = %d"
                             % (label, gam, len(gamma_lz)))
        gamma_text = "γ = %d [exhaustive]" % gam
    else:
        lb, ub, closed, wit = gamma_bracket(sym, len(gamma_lz), sa, lcp)
        gam = closed
        if closed is not None:
            gamma_text = (("γ = %d [closed: ceil(delta) = "
                           "\\|Gamma_LZ\\|]" % closed) if wit is None
                          else "γ = %d [singleton %r verified]" % (closed, list(wit)))
        else:
            gamma_text = ("γ ∈ [%d, %d] [delta ≤ γ ≤ "
                          "\\|Gamma_LZ\\|]" % (lb, ub))

    return {
        "label": label, "n": n, "z": z, "delta": dlt,
        "gamma_lz": len(gamma_lz), "gamma": gam, "gamma_text": gamma_text,
        "ratio_z": Fraction(len(gamma_lz), z) if z else None,
        "ratio_delta": Fraction(len(gamma_lz)) / dlt if dlt else None,
        "verify": method, "t_lz": t_lz, "t_delta": t_delta, "t_verify": t_verify,
        "gamma_lz_positions": gamma_lz, "phrases": phrases,
    }


def fmt_frac(f):
    """An exact fraction with a 4-decimal approximation when it is not an integer."""
    if f is None:
        return "n/a"
    if f.denominator == 1:
        return str(f.numerator)
    return "%d/%d = %.4f" % (f.numerator, f.denominator, float(f))


def rows():
    out = []
    out.append(measure('"ababa"', b"ababa"))
    out.append(measure('"mississippi"', b"mississippi"))
    for k in range(10, 19):
        out.append(measure("Fibonacci F_%d" % k, fibonacci_word(k)))
    out.append(measure("Thue-Morse 2^12", thue_morse_word(12)))
    out.append(measure("Thue-Morse 2^16", thue_morse_word(16)))
    out.append(measure("a^100", b"a" * 100))
    out.append(measure("a^1000", b"a" * 1000))
    out.append(measure("random binary 4096", random_binary(4096, 1)))
    return out


def main(argv=None):
    t_start = time.time()
    print("| text | n | z | delta | \\|Gamma_LZ\\| | \\|Gamma_LZ\\|/z | "
          "\\|Gamma_LZ\\|/delta | gamma |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    table = rows()
    for r in table:
        print("| %s | %d | %d | %s | %d | %s | %s | %s |"
              % (r["label"], r["n"], r["z"], fmt_frac(r["delta"]),
                 r["gamma_lz"], fmt_frac(r["ratio_z"]), fmt_frac(r["ratio_delta"]),
                 r["gamma_text"]))

    print()
    print("every Gamma_LZ verified before printing; |Gamma_LZ| == z on every row "
          "(KP18 Lemma 3.7 gives <=, the construction gives ==); "
          "delta <= |Gamma_LZ| on every row.  gamma is exact only where the row says "
          "so: exhaustively for n <= %d, otherwise the certified bracket "
          "[ceil(delta), |Gamma_LZ|]." % EXACT_GAMMA_LIMIT)
    print()
    print("| text | verification | t_parse | t_delta | t_verify |")
    print("| --- | --- | --- | --- | --- |")
    for r in table:
        print("| %s | %s | %.2fs | %.2fs | %.2fs |"
              % (r["label"], r["verify"], r["t_lz"], r["t_delta"], r["t_verify"]))

    # the two published anchors (docs/research/attractor-approx.md §4, C1)
    print()
    print("anchors from the theory note (C1):")
    tm = [r for r in table if r["label"].startswith("Thue-Morse")]
    ok = all(r["z"] == 2 * (r["n"].bit_length() - 1) for r in tm)
    print("  z(Thue-Morse word t_n) = 2n for n = %s: %s   (KTMSIT20)  %s"
          % ("/".join(str(r["n"].bit_length() - 1) for r in tm),
             "/".join(str(r["z"]) for r in tm), "OK" if ok else "MISMATCH"))
    fib = [r for r in table if r["label"].startswith("Fibonacci")]
    ok = all(r["z"] == int(r["label"].split("_")[1]) - 1 for r in fib)
    print("  z(F_m) = m-1 for m = %s with |F_m| = Fib_m: %s   (W25 Thm 10 states m"
          % ("/".join(r["label"].split("_")[1] for r in fib),
             "/".join(str(r["z"]) for r in fib)))
    print("    positions on the m-th word; with |F_m| = Theta(phi^m) that is z ="
          " log_phi|F_m| up to the")
    print("    indexing offset, which is what these numbers show:  z = m for the word"
          " of length Fib_{m+1}.)  %s" % ("OK" if ok else "MISMATCH"))

    worst = max((r["ratio_delta"], r["label"]) for r in table if r["ratio_delta"])
    print()
    print("worst |Gamma_LZ|/delta in this table: %s (%s)" % (fmt_frac(worst[0]), worst[1]))
    print("total %.2fs" % (time.time() - t_start))
    return 0


if __name__ == "__main__":
    sys.exit(main())
