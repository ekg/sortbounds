#!/usr/bin/env python3
"""verify.py -- independent verification of an attractor, and delta.

WHAT "ATTRACTOR" MEANS HERE (the definition, from tools/attractor/README.md; S is
the text, n = |S|, positions are 0-based and a position p is a single INDEX, not
an interval):

    factor      a nonempty substring S[i .. i+k), k >= 1;
    crosses     the occurrence S[i .. i+k) crosses p  <=>  i <= p < i+k;
    attractor   a set Gamma of positions such that EVERY DISTINCT FACTOR of S has
                at least one occurrence crossing some position of Gamma.

Nothing in this file knows anything about LZ77, phrases, or how Gamma was built:
the input is a text and a set of positions.  That is the point -- the
construction in attractor_from_lz.py is checked against the definition, not
against its own bookkeeping.

THREE IMPLEMENTATIONS, ON PURPOSE.

  1. find_uncovered_factor_definition -- the definition, literally, in Theta(n^2)
     factors with an explicit interval test per occurrence.  It is the primary
     checker and the one every small text uses.  Cost Theta(n^2) slices, so it is
     practical up to n ~ a few hundred (run.py uses it for every row with
     n <= DEFINITION_LIMIT and the suffix-array check on all rows, and asserts
     the two agree wherever both run).
  2. find_uncovered_factor_suffix_array -- the same decision in O(n log n), for
     n up to 2^16 and beyond.  It uses a lemma, so the lemma is written out
     below and the code is cross-checked against (1) in check.py: for every
     binary text of length <= 12 and every subset of its positions, and for
     random texts and random position sets up to n = 256.
  3. check.py additionally contains a THIRD, deliberately naive checker written
     from the definition without any grouping, and compares it with (1).

This module also carries the suffix array, the LCP array and delta, because the
suffix-array verifier needs them and delta = max_k d_k/k is computed from the same
LCP array in one pass.  delta is a lower bound on gamma, not a verification
quantity: KNP23 Lemma II.4 (delta <= gamma), machine-checked in this repository as
`substringComplexity_le_card_attractor`.

THE LEMMA BEHIND THE SUFFIX-ARRAY CHECK (R1 of tools/attractor/README.md, proved
here so the file is self-contained).

  Let nxt[j] = the smallest p in Gamma with p >= j (n if none), and
  K[j] = nxt[j] - j + 1 (n+1 if nxt[j] = n).  An occurrence S[j .. j+k) crosses a
  position of Gamma iff nxt[j] < j + k iff k >= K[j].  So for a factor f whose
  occurrence starts are the set occ(f),

      f is covered  <=>  min { K[j] : j in occ(f) } <= |f|.                      (*)

  The occurrence starts of a factor f of length k are the SA ranks r with
  lcp[r] >= k and lcp[r+1] >= k (r's maximal interval where both neighbouring
  LCPs reach k).  Group the distinct factors by SUFFIX-TREE NODE: node v owns the
  factors of length pd(v)+1 .. depth(v), all of them with the SAME occurrence set
  sa[lo(v) .. hi(v)].  By (*) all of v's factors are covered iff
  min { K[sa[r]] : lo(v) <= r <= hi(v) } <= pd(v)+1, because the lengths covered by
  v are exactly {pd+1, ..., depth} and min over occ does not depend on the length
  while the right-hand side is smallest at the shortest length.  Hence

      Gamma is an attractor  <=>  for every node v:  RMQ_K(lo(v), hi(v)) <= pd(v)+1.

  Soundness rests on the nodes partitioning the distinct factors, which the code
  asserts directly (sum of (depth - pd) over all nodes == sum_k d_k, the total
  number of distinct factors) instead of trusting the sweep.
"""

import sys
from fractions import Fraction
from math import gcd

# --------------------------------------------------------------------------
# suffix array, LCP array, delta
# --------------------------------------------------------------------------

def suffix_array(sym):
    """The suffix array of `sym` (a bytes/str sequence), prefix doubling, O(n log^2 n)."""
    n = len(sym)
    if n == 0:
        return []
    sa = list(range(n))
    rank = list(sym)
    # compress the alphabet so ranks are 0..sigma-1 (needed for the max-rank test)
    order = sorted(set(rank))
    remap = {c: i for i, c in enumerate(order)}
    rank = [remap[c] for c in rank]
    tmp = [0] * n
    k = 1
    while True:
        sa.sort(key=lambda i: (rank[i], rank[i + k] if i + k < n else -1))
        tmp[sa[0]] = 0
        prev_max = rank[sa[-1]]
        for idx in range(1, n):
            a, b = sa[idx - 1], sa[idx]
            ka = (rank[a], rank[a + k] if a + k < n else -1)
            kb = (rank[b], rank[b + k] if b + k < n else -1)
            assert ka <= kb, "suffix array not sorted"
            tmp[b] = tmp[a] + (1 if ka < kb else 0)
        rank, tmp = tmp, rank
        if rank[sa[-1]] == n - 1:
            return sa
        assert rank[sa[-1]] > prev_max, "doubling must refine the ranks"
        k <<= 1


def lcp_array(sym, sa):
    """lcp[r] = lcp of sa[r-1] and sa[r] (lcp[0] = 0), Kasai, O(n)."""
    n = len(sym)
    rank = [0] * n
    for r, i in enumerate(sa):
        rank[i] = r
    lcp = [0] * n
    h = 0
    for i in range(n):
        r = rank[i]
        if r == 0:
            h = 0
            continue
        j = sa[r - 1]
        while i + h < n and j + h < n and sym[i + h] == sym[j + h]:
            h += 1                           # progress: h strictly grows
        lcp[r] = h
        if h:
            h -= 1
        assert 0 <= lcp[r] <= n - max(i, j)
    return lcp


def suffix_tree_nodes(n, sa, lcp):
    """(lo, hi, depth, parent_depth) for every suffix-tree node of S.

    A node owns the factors of length parent_depth+1 .. depth, all occurring at
    the starts sa[lo..hi].  Internal nodes come from the LCP-interval stack;
    leaves own the lengths above the deeper of their two neighbour LCPs (a leaf
    that is a prefix of a neighbour owns nothing and is omitted).
    """
    if n == 0:
        return []
    nodes = []
    stack = [(0, 0)]                         # (depth, lo) of the open intervals
    for i in range(1, n + 1):
        cur = lcp[i] if i < n else 0
        lo = i - 1
        while stack[-1][0] > cur:
            depth, ilo = stack.pop()
            parent_depth = stack[-1][0] if stack[-1][0] > cur else cur
            assert 0 <= parent_depth < depth
            nodes.append((ilo, i - 1, depth, parent_depth))
            lo = ilo
        if i < n and stack[-1][0] < cur:
            stack.append((cur, lo))
    for r in range(n):
        own = n - sa[r]
        left = lcp[r]
        right = lcp[r + 1] if r + 1 < n else 0
        parent_depth = left if left > right else right
        if parent_depth < own:
            nodes.append((r, r, own, parent_depth))
    return nodes


def distinct_counts(sym, sa=None, lcp=None):
    """d[k] = number of distinct factors of length k, for k = 0..n (d[0] = 1).

    Rank r is the first (leftmost) SA rank of its maximal lcp-interval for length
    k iff lcp[r] < k, and it has a factor of length k iff k <= n - sa[r].  So r
    contributes 1 to d[k] exactly for k in (lcp[r], n - sa[r]], which is a
    difference-array update: O(n) for the whole profile.
    """
    n = len(sym)
    if n == 0:
        return [1]
    if sa is None:
        sa = suffix_array(sym)
    if lcp is None:
        lcp = lcp_array(sym, sa)
    diff = [0] * (n + 2)
    for r in range(n):
        lo = lcp[r] + 1
        hi = n - sa[r]
        if lo <= hi:
            diff[lo] += 1
            diff[hi + 1] -= 1
        assert 0 <= lo <= n + 1
    d = [0] * (n + 1)
    cur = 0
    for k in range(1, n + 1):
        cur += diff[k]
        d[k] = cur
        assert d[k] >= 0
    d[0] = 1
    return d


def delta_pair(sym):
    """(num, den): delta = max_k d_k / k as a reduced fraction, exactly."""
    d = distinct_counts(sym)
    best_num, best_den = 0, 1
    for k in range(1, len(d)):
        if d[k] * best_den > best_num * k:
            best_num, best_den = d[k], k
    if best_num == 0:
        return (0, 1)
    g = gcd(best_num, best_den)
    return (best_num // g, best_den // g)


def delta(sym):
    """delta as a Fraction (KNP23: delta <= gamma).  0 for the empty text."""
    num, den = delta_pair(sym)
    return Fraction(num, den)


# --------------------------------------------------------------------------
# 1. the definition, literally
# --------------------------------------------------------------------------

def _validated_points(gamma, n):
    pts = sorted(set(int(p) for p in gamma))
    for p in pts:
        if not 0 <= p < n:
            raise ValueError("attractor position %r outside 0..%d" % (p, n - 1))
    return pts


def _next_marks(pts, n):
    """nxt[i] = smallest p in pts with p >= i, or n if there is none."""
    marked = bytearray(n + 1)
    for p in pts:
        marked[p] = 1
    nxt = [n] * (n + 1)
    cur = n
    for i in range(n - 1, -1, -1):
        if marked[i]:
            cur = i
        nxt[i] = cur
    nxt[n] = n
    return nxt


def find_uncovered_factor_definition(sym, gamma):
    """None if Gamma is an attractor, else (factor_as_bytes, some_occurrence_start).

    The definition, with no structure used: for every length k, bucket the starts
    by the actual k-character factor, then a factor is covered iff one of its
    occurrence starts j satisfies j <= p < j+k for some p in Gamma, which is the
    integer test nxt[j] < j + k.  Theta(n^2) factor slices, so Theta(n^3) bytes
    copied: use it for n up to a few hundred, and for the self-tests.
    """
    n = len(sym)
    if n == 0:
        return None
    pts = _validated_points(gamma, n)
    nxt = _next_marks(pts, n)
    for k in range(1, n + 1):
        groups = {}
        for i in range(n - k + 1):
            groups.setdefault(sym[i:i + k], []).append(i)
        assert sum(len(v) for v in groups.values()) == n - k + 1   # progress: every start
        for factor, starts in groups.items():
            assert len(factor) == k
            for j in starts:
                if nxt[j] < j + k:
                    break
            else:
                return (factor, starts[0])
    return None


def verify_definition(sym, gamma):
    """True iff Gamma is an attractor, by the definition-level check above."""
    return find_uncovered_factor_definition(sym, gamma) is None


# --------------------------------------------------------------------------
# 2. the same decision in O(n log n)
# --------------------------------------------------------------------------

class _SparseMin:
    """Range minimum over an array, O(n log n) build, O(1) query."""

    __slots__ = ("table", "log")

    def __init__(self, arr):
        n = len(arr)
        self.log = [0] * (n + 1)
        for i in range(2, n + 1):
            self.log[i] = self.log[i >> 1] + 1
        table = [list(arr)] if n else [[]]
        j = 1
        while (1 << j) <= n:
            prev = table[-1]
            half = 1 << (j - 1)
            span = 1 << j
            row = [min(prev[i], prev[i + half]) for i in range(n - span + 1)]
            assert len(row) == n - span + 1
            table.append(row)
            j += 1
        self.table = table

    def query(self, lo, hi):
        assert 0 <= lo <= hi < len(self.table[0])
        j = self.log[hi - lo + 1]
        row = self.table[j]
        span = 1 << j
        a = row[lo]
        b = row[hi - span + 1]
        return a if a < b else b


def find_uncovered_factor_suffix_array(sym, gamma, sa=None, lcp=None):
    """None if Gamma is an attractor, else (factor_as_bytes, occurrence_start).

    Uses the node criterion proved in this file's docstring; O(n log n) time and
    memory.  `sa`/`lcp` may be supplied (they are recomputed otherwise).  The
    factor/node partition is asserted to be complete, so a bug in the interval
    sweep cannot silently pass a bad Gamma.
    """
    n = len(sym)
    if n == 0:
        return None
    pts = _validated_points(gamma, n)
    if sa is None:
        sa = suffix_array(sym)
    if lcp is None:
        lcp = lcp_array(sym, sa)
    nodes = suffix_tree_nodes(n, sa, lcp)
    owned = sum(depth - pd for (_, _, depth, pd) in nodes)
    total = sum(distinct_counts(sym, sa, lcp)[1:])
    assert owned == total, (
        "node partition is incomplete: %d factors owned vs %d distinct" % (owned, total))

    nxt = _next_marks(pts, n)
    karr = [n + 1] * n                        # K[j] = shortest covered factor at j
    for j in range(n):
        if nxt[j] < n:
            karr[j] = nxt[j] - j + 1
    rmq = _SparseMin([karr[j] for j in sa])
    for (lo, hi, depth, pd) in nodes:
        assert 0 <= lo <= hi < n and pd + 1 <= depth
        if rmq.query(lo, hi) > pd + 1:        # the node's shortest factor is uncovered
            start = sa[lo]
            return (sym[start:start + pd + 1], start)
    return None


def verify_suffix_array(sym, gamma, sa=None, lcp=None):
    """True iff Gamma is an attractor, by the O(n log n) node criterion."""
    return find_uncovered_factor_suffix_array(sym, gamma, sa, lcp) is None


def factor_to_text(factor):
    """bytes -> printable text, for witness reporting."""
    try:
        return factor.decode("latin-1")
    except Exception:                         # pragma: no cover
        return repr(factor)


def main(argv=None):
    """CLI: python3 verify.py --text ababa --gamma 0,1,4  (exit 1 if not an attractor)."""
    import argparse
    ap = argparse.ArgumentParser(description="independent attractor verification")
    ap.add_argument("--text", required=True)
    ap.add_argument("--gamma", required=True, help="comma separated 0-based positions")
    ap.add_argument("--definition", action="store_true", help="force the slow check")
    args = ap.parse_args(argv)
    sym = args.text.encode("latin-1")
    gamma = [int(t) for t in args.gamma.split(",") if t.strip() != ""]
    wit = (find_uncovered_factor_definition(sym, gamma) if args.definition
           else find_uncovered_factor_suffix_array(sym, gamma))
    print("n = %d, |Gamma| = %d, delta = %s" % (len(sym), len(set(gamma)), delta(sym)))
    if wit is None:
        print("ATTRACTOR: every distinct factor crosses a position of Gamma")
        return 0
    print("NOT an attractor: factor %r at %d is uncovered" % (factor_to_text(wit[0]), wit[1]))
    return 1


if __name__ == "__main__":
    sys.exit(main())
