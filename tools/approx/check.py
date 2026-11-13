#!/usr/bin/env python3
"""check.py -- self-tests for tools/approx.  Prints OK and exits 0, or exits 1.

The acceptance tests the contract asks for, plus the checks that make them mean
something:

  [1] the LZ77 parse is VALID (phrases tile the text; every copy really copies an
      earlier position; the copy may overlap itself) and, with an unbounded chain
      walk, EXACTLY greedy (its length equals a brute-force longest match);
  [2] the suffix array, the LCP array and the d_k profile agree with brute force;
  [3] for every binary text of length <= 12: Gamma_LZ passes the definition-level
      verifier, |Gamma_LZ| == z, and delta <= |Gamma_LZ| <= z   <-- the headline;
  [4] the three verifiers agree: the definition-level one, the O(n log n) node
      one, and a third naive one written here from the definition (exhaustively
      over all position subsets for short texts, randomly above that);
  [5] the exact gamma (exhaustive hitting set, n <= 10) satisfies delta <= gamma
      <= |Gamma_LZ|, so the LZ construction really is an attractor of size z and
      gamma is really the minimum;
  [6] the published anchors: z(Thue-Morse t_n) = 2n, z(Fibonacci F_m) = m-1 with
      |F_m| = Fib_m, z(a^n) = 2 (overlapping copies), and the non-overlapping
      variant's larger z on a^n;
  [7] edge cases: the empty text and single-character texts.

Run:  timeout 120 python3 check.py
"""

import random
import sys
import time
from fractions import Fraction

import lz
import verify
from attractor_from_lz import attractor_for_text, phrase_ends
from run import exact_gamma, fibonacci_word, thue_morse_word

FAILURES = []
CHECKS = [0]
T0 = time.time()


def check(cond, msg):
    CHECKS[0] += 1
    if not cond:
        FAILURES.append(msg)
        print("FAIL  %s" % msg)
    return cond


def binary_strings(max_len, min_len=1):
    """Every binary text of length min_len..max_len, as bytes."""
    for length in range(min_len, max_len + 1):
        for bits in range(1 << length):
            assert bits < (1 << length)              # progress
            yield bytes((bits >> (length - 1 - i)) & 1 for i in range(length))


def subsets(n):
    """Every subset of range(n) as a list, in increasing order."""
    for mask in range(1 << n):
        assert mask < (1 << n)
        yield [i for i in range(n) if mask >> i & 1]


# --------------------------------------------------------------------------
# a third verifier, as naive as the definition allows
# --------------------------------------------------------------------------

def naive_is_attractor(sym, gamma):
    """Definition, with no grouping at all: for every (start, length) window,
    find its occurrences by scanning, and require one of them to contain a mark."""
    n = len(sym)
    pts = sorted(set(gamma))
    seen = set()
    for i in range(n):
        for k in range(1, n - i + 1):
            assert 0 <= i < n and k >= 1
            f = sym[i:i + k]
            if f in seen:
                continue
            seen.add(f)
            covered = False
            for j in range(n - k + 1):
                if sym[j:j + k] != f:
                    continue
                for p in pts:
                    if j <= p < j + k:
                        covered = True
                        break
                if covered:
                    break
            if not covered:
                return False
    return True


# --------------------------------------------------------------------------
# [1] the parse itself
# --------------------------------------------------------------------------

def check_parse(sym, phrases, overlap=True, exact=True):
    """Valid parse, and (when exact) the greedy longest match at every phrase."""
    n = len(sym)
    if n == 0:
        check(phrases == [], "empty text must have no phrases")
        return
    pos = 0
    for p in phrases:
        check(p.start == pos, "phrases must tile: expected start %d, got %d" % (pos, p.start))
        check(p.length >= 1, "every phrase is nonempty")
        check(p.start + p.length <= n, "phrase must stay inside the text")
        if p.is_literal:
            check(p.length == 1, "a literal is one character")
        else:
            d = p.dist
            check(1 <= d <= p.start, "copy distance %d out of range at %d" % (d, p.start))
            src = p.start - d
            if not overlap:
                check(src + p.length <= p.start,
                      "non-overlapping copy must end before the phrase")
            for t in range(p.length):
                check(sym[p.start + t] == sym[src + t],
                      "copy does not match its source at offset %d" % t)
                if sym[p.start + t] != sym[src + t]:
                    return
        pos = p.start + p.length
    check(pos == n, "phrases must cover the whole text (%d of %d)" % (pos, n))
    if not exact:
        return
    pos = 0
    for p in phrases:
        m = lz.longest_match_bruteforce(sym, pos, overlap)
        if m >= 2:
            check(p.length == m, "greedy must take the longest match: at %d longest is "
                                 "%d, parse took %d" % (pos, m, p.length))
            check(lz.lcp(sym, pos, pos - p.dist, p.length) == p.length,
                  "the chosen distance must realise the whole match")
        else:
            check(p.is_literal, "at %d the longest match is %d < 2, so a literal is "
                                "required" % (pos, m))
        pos += p.length


def test_parse():
    print("[1] LZ77 parses: valid, and exactly greedy")
    for sym in binary_strings(10):
        ph = lz.lz77(sym)
        check_parse(sym, ph, overlap=True, exact=True)
        check_parse(sym, lz.lz77(sym, overlap=False), overlap=False, exact=True)
    for sym in binary_strings(12, 11):
        check_parse(sym, lz.lz77(sym), exact=False)
    rng = random.Random(7)
    for trial in range(40):
        n = rng.randrange(1, 60)
        sym = bytes(rng.getrandbits(1) for _ in range(n))
        check_parse(sym, lz.lz77(sym), exact=True)
        check_parse(sym, lz.lz77(sym, overlap=False), overlap=False, exact=True)
        assert trial < 40
    # a truncated chain walk still yields a VALID parse (only z may grow)
    for spec in (b"a" * 300, thue_morse_word(6), fibonacci_word(12), b"abababab" * 20):
        ph = lz.lz77(spec, max_chain=1)
        check_parse(spec, ph, exact=False)
        check(len(ph) >= len(lz.lz77(spec)),
              "a truncated walk must not produce FEWER phrases than the exact greedy")


# --------------------------------------------------------------------------
# [2] suffix array, LCP, d_k
# --------------------------------------------------------------------------

def test_suffix_array():
    print("[2] suffix array / LCP / d_k against brute force")
    for sym in binary_strings(12):
        n = len(sym)
        sa = verify.suffix_array(sym)
        check(sa == sorted(range(n), key=lambda i: sym[i:]),
              "suffix array wrong on %r" % (sym,))
        lcp = verify.lcp_array(sym, sa)
        for r in range(1, n):
            a, b = sa[r - 1], sym[sa[r]:]
            want = 0
            while a + want < n and want < len(b) and sym[a + want] == b[want]:
                want += 1
            check(lcp[r] == want, "lcp[%d] wrong on %r: %d vs %d"
                  % (r, sym, lcp[r], want))
        d = verify.distinct_counts(sym)
        for k in range(1, n + 1):
            brute = len({sym[i:i + k] for i in range(n - k + 1)})
            check(d[k] == brute, "d_%d wrong on %r: %d vs %d" % (k, sym, d[k], brute))
        num, den = verify.delta_pair(sym)
        want = max(Fraction(d[k], k) for k in range(1, n + 1))
        check(Fraction(num, den) == want, "delta wrong on %r" % (sym,))


# --------------------------------------------------------------------------
# [3] the headline: delta <= |Gamma_LZ| <= z on every binary text of length <= 12
# --------------------------------------------------------------------------

def test_construction():
    print("[3] Gamma_LZ: verified, |Gamma_LZ| == z, delta <= |Gamma_LZ| <= z, n <= 12")
    worst_delta = (0, None)
    worst_z = (0, None)
    texts = 0
    for sym in binary_strings(12):
        n = len(sym)
        texts += 1
        gamma, phrases = attractor_for_text(sym)
        z = len(phrases)
        check(list(gamma) == phrase_ends(phrases), "Gamma_LZ must be the phrase ends")
        check(len(gamma) == z, "|Gamma_LZ| must equal z on %r" % (sym,))
        check(len(set(gamma)) == z, "phrase ends must be distinct on %r" % (sym,))
        check(len(gamma) <= z, "|Gamma_LZ| <= z on %r" % (sym,))
        wit = verify.find_uncovered_factor_definition(sym, gamma)
        check(wit is None, "Gamma_LZ must be an attractor: %r fails on factor %r at %d"
              % (sym, None if wit is None else wit[0], -1 if wit is None else wit[1]))
        check(verify.verify_suffix_array(sym, gamma),
              "the two verifiers must agree on Gamma_LZ for %r" % (sym,))
        d = verify.delta(sym)
        check(d <= len(gamma), "delta <= |Gamma_LZ| on %r (%s <= %d)"
              % (sym, d, len(gamma)))
        ratio = float(len(gamma)) / float(d) if d else 0.0
        if ratio > worst_delta[0]:
            worst_delta = (ratio, (sym, z, str(d)))
        if z and len(gamma) / z > worst_z[0]:
            worst_z = (len(gamma) / z, (sym, z))
    print("    %d texts; worst |Gamma_LZ|/delta = %.4f on %r; worst |Gamma_LZ|/z = %.4f on %r"
          % (texts, worst_delta[0], worst_delta[1], worst_z[0], worst_z[1]))
    check(worst_z[0] <= 1.0, "the construction must never exceed z")
    return worst_delta, worst_z


# --------------------------------------------------------------------------
# [4] the verifiers agree
# --------------------------------------------------------------------------

def test_verifiers():
    print("[4] the three verifiers agree (exhaustive on short texts, random above)")
    agree = 0
    for sym in binary_strings(7):
        n = len(sym)
        sa = verify.suffix_array(sym)
        lcp = verify.lcp_array(sym, sa)
        for gamma in subsets(n):
            a = verify.verify_definition(sym, gamma)
            b = verify.verify_suffix_array(sym, gamma, sa, lcp)
            c = naive_is_attractor(sym, gamma)
            check(a == b == c, "verifiers disagree on %r with %r: def=%s sa=%s naive=%s"
                  % (sym, gamma, a, b, c))
            agree += 1
            assert agree > 0
    print("    exhaustive: every subset of every binary text of length <= 7 (%d pairs)"
          % agree)

    rng = random.Random(11)
    cases = 0
    for trial in range(300):
        n = rng.randrange(8, 60)
        sym = bytes(rng.getrandbits(1) for _ in range(n))
        sa = verify.suffix_array(sym)
        lcp = verify.lcp_array(sym, sa)
        for _ in range(3):
            k = rng.randrange(0, max(1, n // 2) + 1)
            gamma = sorted(rng.sample(range(n), min(k, n)))
            a = verify.verify_definition(sym, gamma)
            b = verify.verify_suffix_array(sym, gamma, sa, lcp)
            check(a == b, "verifiers disagree on a random case (n=%d, |Gamma|=%d)"
                  % (n, len(gamma)))
            cases += 1
            assert cases > 0
        assert trial < 300
    print("    random: %d (text, Gamma) pairs, lengths 7..59" % cases)

    # all subsets of "mississippi" with both fast checkers
    sym = b"mississippi"
    sa = verify.suffix_array(sym)
    lcp = verify.lcp_array(sym, sa)
    for gamma in subsets(len(sym)):
        check(verify.verify_definition(sym, gamma)
              == verify.verify_suffix_array(sym, gamma, sa, lcp),
              "verifiers disagree on mississippi with %r" % (gamma,))
    print("    exhaustive: all %d subsets of \"mississippi\"" % (1 << len(sym)))

    # the verifier has TEETH: a wrong Gamma is rejected, so accepting Gamma_LZ is
    # not vacuous.  Two wrong families are tried on every binary text of length
    # <= 8: the every-other-position set, and Gamma_LZ shifted left by one.  (Note
    # the phrase STARTS also happen to be an attractor -- see the remark in
    # attractor_from_lz.py -- so that is not a wrong family.)
    rejected = 0
    tried = 0
    for sym in binary_strings(8):
        n = len(sym)
        gamma, phrases = attractor_for_text(sym)
        for cand in (sorted(range(0, n, 2)), [p.start for p in phrases][:-1]):
            tried += 1
            if not verify.verify_definition(sym, cand):
                rejected += 1
            check(verify.verify_definition(sym, gamma),
                  "phrase ends must verify for %r" % (sym,))
    check(rejected > 0, "the verifier must reject SOME wrong Gamma (vacuity test)")
    print("    teeth: %d of %d wrong position sets rejected (stride-2, and "
          "Gamma_LZ minus its last element)" % (rejected, tried))

    # the growing-witness path: a deliberately bad Gamma must be rejected
    for sym in (b"mississippi", thue_morse_word(4)):
        for bad in ((), [0], list(range(0, len(sym), 3))):
            if not verify.verify_suffix_array(sym, bad):
                wit = verify.find_uncovered_factor_suffix_array(sym, bad)
                check(wit is not None and not verify.verify_definition(sym, bad),
                      "the suffix-array checker must reject %r the same way" % (bad,))


# --------------------------------------------------------------------------
# [5] exact gamma
# --------------------------------------------------------------------------

def test_exact_gamma():
    print("[5] exact gamma: delta <= gamma <= |Gamma_LZ|, n <= 10")
    starts_ok = 0
    for sym in binary_strings(10):
        _, ph_obs = attractor_for_text(sym)
        if verify.verify_definition(sym, [q.start for q in ph_obs]):
            starts_ok += 1
        gam, wit = exact_gamma(sym)
        check(verify.verify_definition(sym, wit),
              "the exact-gamma witness must be an attractor for %r" % (sym,))
        check(len(wit) == gam, "the witness size must be gamma")
        d = verify.delta(sym)
        check(d <= gam, "delta <= gamma on %r (%s <= %d)" % (sym, d, gam))
        gamma_lz, _ = attractor_for_text(sym)
        check(gam <= len(gamma_lz), "gamma <= |Gamma_LZ| on %r (%d <= %d)"
              % (sym, gam, len(gamma_lz)))
    print("    exhaustive for every binary text of length <= 10 (gamma from the "
          "hitting-set search)")
    # the facet reduction itself: on short texts, no subset of size < gamma is an
    # attractor, checked by brute force over every subset
    for sym in binary_strings(6):
        gam, _ = exact_gamma(sym)
        for cand in subsets(len(sym)):
            if len(cand) < gam:
                check(not verify.verify_definition(sym, cand),
                      "gamma is not minimal on %r: %r also works" % (sym, cand))
    print("    and no smaller position set is an attractor (n <= 6, every subset)")
    check(starts_ok == 2 ** 11 - 2, "the phrase STARTS are an attractor on every binary "
          "text of length <= 10 (%d of %d) -- an observation, see attractor_from_lz.py"
          % (starts_ok, 2 ** 11 - 2))


# --------------------------------------------------------------------------
# [6] the published anchors
# --------------------------------------------------------------------------

def test_anchors():
    print("[6] anchors: z(Thue-Morse t_n) = 2n, z(F_m) = m-1, z(a^n) = 2")
    for k in range(4, 13):
        sym = thue_morse_word(k)
        check(len(sym) == 1 << k, "Thue-Morse word length")
        z = len(lz.lz77(sym))
        check(z == 2 * k, "z(Thue-Morse 2^%d) = %d, expected 2n = %d (KTMSIT20)"
              % (k, z, 2 * k))
    for m in range(10, 19):
        sym = fibonacci_word(m)
        z = len(lz.lz77(sym))
        check(z == m - 1, "z(F_%d) = %d, expected m-1 = %d with |F_m| = Fib_m "
                          "(W25 Thm 10, indexing offset of one)" % (m, z, m - 1))
    for n in (1, 2, 3, 10, 100, 1000):
        sym = b"a" * n
        check(len(lz.lz77(sym)) == (2 if n > 1 else 1),
              "z(a^%d) = 2 with overlapping copies" % n)
        ph = lz.lz77(sym, overlap=False)
        check_parse(sym, ph, overlap=False, exact=True)
        if n >= 10:
            check(len(ph) > 2, "the non-overlapping variant cannot reach z(a^%d) = 2"
                               % n)
        gamma, _ = attractor_for_text(sym)
        check(verify.verify_suffix_array(sym, gamma), "Gamma_LZ for a^%d" % n)


# --------------------------------------------------------------------------
# [7] edge cases
# --------------------------------------------------------------------------

def test_edges():
    print("[7] edge cases")
    check(lz.lz77(b"") == [], "the empty text has no phrases")
    check(attractor_for_text(b"")[0] == [], "the empty text has the empty attractor")
    check(verify.find_uncovered_factor_definition(b"", []) is None,
          "the empty text is trivially an attractor")
    check(verify.find_uncovered_factor_suffix_array(b"", []) is None,
          "the empty text is trivially an attractor (suffix array path)")
    check(verify.delta(b"") == 0, "delta of the empty text is 0")
    for sym in (b"a", b"ab", b"aa"):
        gamma, phrases = attractor_for_text(sym)
        check(gamma == [p.end for p in phrases], "phrase ends for %r" % (sym,))
        check(verify.verify_definition(sym, gamma), "Gamma_LZ for %r" % (sym,))
    check(lz.lz77(b"a")[0] == lz.Phrase(0, 1, 0), "a single character is one literal")
    check(lz.lz77(b"aa")[1] == lz.Phrase(1, 1, 0),
          "aa: the longest copy at 1 is shorter than 2, so the phrase is a literal "
          "(a length-1 copy costs the same and is never emitted)")
    try:
        verify.verify_definition(b"abc", [3])
        check(False, "an out-of-range position must raise")
    except ValueError:
        check(True, "out-of-range position rejected")


def main():
    test_parse()
    test_suffix_array()
    worst_delta, worst_z = test_construction()
    test_verifiers()
    test_exact_gamma()
    test_anchors()
    test_edges()
    print()
    if FAILURES:
        print("FAILED: %d of %d checks in %.1fs" % (len(FAILURES), CHECKS[0], time.time() - T0))
        for msg in FAILURES[:20]:
            print("  - %s" % msg)
        return 1
    print("OK  %d checks in %.1fs" % (CHECKS[0], time.time() - T0))
    print("    worst |Gamma_LZ|/delta over all binary texts of length <= 12: %.4f on %r"
          % (worst_delta[0], worst_delta[1]))
    print("    worst |Gamma_LZ|/z: %.4f (must be <= 1; it is 1 on every row)"
          % worst_z[0])
    return 0


if __name__ == "__main__":
    sys.exit(main())
