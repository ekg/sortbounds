"""features.py -- exact structural features of a binary word, and its exact gamma.

Every feature here is *exact* (no search, no heuristic) except `gamma` and
`packing`, and those two carry brackets:

  gamma        the minimum attractor size.  Computed by `gamma_certified`, which
               runs ../attractor/anytime.py's iterative-deepening search from a
               lower bound and REFUSES to return a number unless the bracket is
               closed (an explicit verified attractor of size k, plus an
               exhausted search over every position set of size < k).  An
               unclosed run raises `NotClosed`; it is never silently reported.
  packing      a certified lower bound (../attractor/instance.py packing_bound);
               packing <= gamma always, so it is a feature and a partial
               certificate at once.

Definitions (S is the word, positions 0..n-1, sigma = 2):

  factor       contiguous substring S[i:i+L], L >= 1
  k-attractor  a position set Gamma such that every DISTINCT factor w of length
               <= k has SOME occurrence [i, i+|w|) crossed by Gamma
               (exists p in Gamma with i <= p < i+|w|).  This is the definition
               ../attractor/instance.py implements (its rule R1) and the one
               Kempa--Prezza use; note that it quantifies over distinct factors,
               not over all occurrences, so a 1-attractor has size exactly sigma
               and not n.
  gamma_k      the minimum size of a k-attractor; gamma_k is non-decreasing in k
               and gamma_n = gamma.

Feature dictionary returned by `features`:

  n             |S|
  profile       tuple (d_1, ..., d_n): d_L = number of distinct factors of
                length L  (this is the d_k profile; delta is its max of d_L/L)
  nfactors      sum of profile
  delta         Fraction, max_L d_L / L   (exact)
  delta_ceil    ceil(delta)
  gamma1        gamma_1 = sigma for n >= 1 (all single characters must be
                covered by distinct positions -- computed, not assumed)
  gamma2        gamma_2, exact, by `gamma_k` (binary: the factor universe is
                {a, b, aa, ab, ba, bb} restricted to those present)
  gammak        tuple (gamma_1, ..., gamma_K) for K = min(kmax, n)
  n_runs        number of maximal runs of equal characters
  max_run       length of the longest run
  period        shortest p >= 1 with S[i] == S[i+p] for every i < n-p   (n if
                S is not a power of a shorter word, i.e. the trivial period)
  rare_gap      shortest distance between two consecutive occurrences of the
                least frequent symbol, if that symbol occurs at least twice;
                n if the least frequent symbol occurs once; ties broken towards
                the smaller gap over all least-frequent symbols
  packing       certified lower bound from ../attractor/instance.py
  nodes         number of suffix-tree nodes = number of distinct
                occurrence-classes of factors (the set-cover universe size)
  minlen_max    max over nodes of the node's shortest-factor length (the longest
                "shortest factor" -- gamma_k = gamma once k reaches it, trivially,
                because then every node's own representative is covered)
  unary_max     max over nodes with a unique occurrence of that node's shortest
                factor length (a factor occurring once must be crossed by its own
                position; this is the "unique factor" mass)

`gamma_k(s, k)` is an independent, definition-level exact solver (it knows
nothing about suffix trees).  It agrees with `gamma_certified` at k = n, which is
checked in check.py's `validate` command -- two different solvers, one universe
derived from the suffix tree, one built from scratch.
"""

import os
import sys
import time
from fractions import Fraction
from math import ceil

_HERE = os.path.dirname(os.path.abspath(__file__))
_ATTRACTOR = os.path.normpath(os.path.join(_HERE, os.pardir, "attractor"))
if _ATTRACTOR not in sys.path:
    sys.path.insert(0, _ATTRACTOR)

from instance import Instance                        # noqa: E402
import anytime                                       # noqa: E402

KMAX_DEFAULT = 6


class NotClosed(Exception):
    """The exact search could not close the bracket; gamma is unknown."""


# ---------------------------------------------------------------------------
# cheap exact features
# ---------------------------------------------------------------------------


def n_runs_and_max_run(s):
    """(number of maximal equal-character runs, longest run)."""
    if not s:
        return 0, 0
    runs, cur, best = 1, 1, 1
    for i in range(1, len(s)):
        if s[i] == s[i - 1]:
            cur += 1
            if cur > best:
                best = cur
        else:
            runs += 1
            cur = 1
    return runs, best


def shortest_period(s):
    """Shortest p >= 1 with s[i] == s[i+p] for all i < n-p (n if none shorter)."""
    n = len(s)
    for p in range(1, n + 1):
        ok = True
        for i in range(n - p):
            if s[i] != s[i + p]:
                ok = False
                break
        if ok:
            return p
    return n


def rare_gap(s):
    """Gap between two consecutive occurrences of the least frequent symbol.

    Least frequent means fewest occurrences; on a tie both tied symbols are
    considered and the smaller gap is taken.  If the least frequent symbol
    occurs once there is no gap and n is returned (a sentinel, not a gap: it is
    larger than every real gap, which is the conservative direction for any test
    that treats rare_gap as an upper bound on spacing).
    """
    n = len(s)
    if n <= 1:
        return n
    cnt = {}
    pos = {}
    for i, c in enumerate(s):
        cnt[c] = cnt.get(c, 0) + 1
        pos.setdefault(c, []).append(i)
    least = min(cnt.values())
    best = None
    for c, k in cnt.items():
        if k != least or k < 2:
            continue
        pl = pos[c]
        gap = min(pl[j + 1] - pl[j] for j in range(len(pl) - 1))
        if best is None or gap < best:
            best = gap
    return n if best is None else best


def factor_profile(s, kmax=None):
    """(d_1, ..., d_L) with d_L = number of distinct factors of length L.

    kmax=None means all lengths 1..n.
    """
    n = len(s)
    top = n if kmax is None else min(kmax, n)
    return tuple(len({s[i:i + L] for i in range(n - L + 1)}) for L in range(1, top + 1))


def delta_from_profile(profile):
    """max_L d_L / L exactly, and the argmax (numerator, denominator)."""
    best, best_num, best_den = Fraction(0), 0, 1
    for L, d in enumerate(profile, start=1):
        f = Fraction(d, L)
        if f > best:
            best, best_num, best_den = f, d, L
    return best, (best_num, best_den)


# ---------------------------------------------------------------------------
# exact k-attractor, definition level, independent of the suffix tree
# ---------------------------------------------------------------------------


def _cover_masks(s, factors):
    """cover[p] = bit mask over `factors` of the factors crossed by position p."""
    n = len(s)
    cov = [0] * n
    for idx, w in enumerate(factors):
        bit = 1 << idx
        L = len(w)
        start = s.find(w)
        while start != -1:
            for p in range(start, start + L):
                cov[p] |= bit
            start = s.find(w, start + 1)
    return cov


def gamma_k(s, k, node_cap=5_000_000):
    """Exact minimum k-attractor size, definition level.

    Universe = the distinct factors of length <= k.  Returns (size, gamma_set).
    Iterative deepening: for t = 0, 1, 2, ... decide whether t positions suffice;
    the first t that works is gamma_k, and the returned set is re-verified.
    Raises NotClosed if the DFS budget runs out (never returns a guess).

    The DFS branches on the uncovered factor with the fewest covering positions,
    which is exact: some position must cover that factor, so branching over its
    covering positions loses no solution.
    """
    n = len(s)
    if n == 0:
        return 0, []
    top = min(k, n)
    factors = sorted({s[i:i + L] for L in range(1, top + 1) for i in range(n - L + 1)})
    cov = _cover_masks(s, factors)
    full = (1 << len(factors)) - 1
    coverers = [[] for _ in factors]
    for p in range(n):
        m = cov[p]
        while m:
            b = m & -m
            coverers[b.bit_length() - 1].append(p)
            m ^= b
    budget = [node_cap]

    def decision(t):
        """Is there a set of <= t positions covering every factor?"""
        sol = []

        def dfs(unc, slots):
            if unc == 0:
                return True
            if slots == 0:
                return False
            budget[0] -= 1
            if budget[0] < 0:
                raise NotClosed("node cap exhausted at n=%d k=%d" % (n, k))
            # rarest uncovered factor still coverable
            best, best_n = -1, None
            m = unc
            while m:
                b = m & -m
                f = b.bit_length() - 1
                m ^= b
                c = 0
                for p in coverers[f]:
                    if cov[p] & unc:
                        c += 1
                        if best_n is not None and c >= best_n:
                            break
                if best_n is None or c < best_n:
                    best, best_n = f, c
                    if c <= 1:
                        break
            if best < 0:
                return False
            for p in coverers[best]:
                gain = cov[p] & unc
                if not gain:
                    continue
                sol.append(p)
                if dfs(unc & ~gain, slots - 1):
                    return True
                sol.pop()
            return False

        if dfs(full, t):
            return list(sol)
        return None

    for t in range(0, n + 1):
        sol = decision(t)
        if sol is not None:
            # re-verify from the definition, independently of the DFS bookkeeping
            got = 0
            for p in sol:
                got |= cov[p]
            if got != full:
                raise AssertionError("gamma_k produced a non-cover for %r k=%d" % (s, k))
            return len(sol), sorted(sol)
    raise AssertionError("gamma_k: t loop never found n positions for %r" % (s,))


# ---------------------------------------------------------------------------
# gamma from ../attractor/anytime.py, bracket closed or nothing
# ---------------------------------------------------------------------------


def gamma_certified(s, inst=None, node_cap=400_000, time_cap=5.0):
    """(gamma, lb, solution) with lb == gamma, or raise NotClosed.

    anytime.exact_gamma runs iterative deepening from a lower bound: a returned
    solution at k means every position set of size < k was refuted by an
    exhausted DFS, so ub = lb = k.  We additionally require
      * Instance.witness(solution) is None   (definition-level re-check), and
      * k >= ceil(delta)                       (the independent lower bound).
    The search is capped by both a node budget and a wall-clock deadline of
    time_cap seconds; either one running out raises NotClosed, so a value is
    never reported from an open bracket.
    """
    inst = Instance(s) if inst is None else inst
    lb0 = max(1, int(ceil(inst.delta())))
    deadline = None if time_cap is None else time.monotonic() + time_cap
    sol, lb = anytime.exact_gamma(inst, deadline=deadline, node_cap=node_cap, lb=lb0)
    if sol is None:
        raise NotClosed("anytime.exact_gamma left the bracket open for %r (lb=%d)"
                        % (s, lb))
    gamma = len(sol)
    if lb != gamma:
        raise NotClosed("bracket not closed for %r: lb=%d ub=%d" % (s, lb, gamma))
    if inst.witness(sol) is not None:
        raise AssertionError("anytime returned a non-attractor for %r" % (s,))
    dceil = int(ceil(inst.delta()))
    if gamma < dceil:
        raise AssertionError("gamma < ceil(delta) for %r: %d < %d" % (s, gamma, dceil))
    return gamma, lb, sorted(sol)


# ---------------------------------------------------------------------------
# the feature bundle
# ---------------------------------------------------------------------------


def node_stats(inst):
    """(number of suffix-tree nodes, max shortest-factor length, unary mass).

    nodes         the set-cover universe size (one node per occurrence class)
    minlen_max    max over nodes of the node's shortest factor length; covering
                  length <= k factors forces every node with min_len <= k, so
                  gamma_k = gamma once k >= minlen_max (only classes whose
                  shortest representative is longer can still differ)
    unary_max     max length of a node's shortest factor among nodes whose
                  factor occurs exactly once (a unique factor forces the
                  attractor to touch it)
    """
    nodes = inst.nodes
    if not nodes:
        return 0, 0, 0
    minlen_max = max(nd.min_len for nd in nodes)
    unary_max = max((nd.min_len for nd in nodes if nd.hi == nd.lo), default=0)
    return len(nodes), minlen_max, unary_max


def features(s, inst=None, kmax=KMAX_DEFAULT, want_packing=True):
    """All exact features of `s`.  Raises NotClosed if gamma cannot be certified."""
    inst = Instance(s) if inst is None else inst
    n = len(s)
    profile = tuple(inst.d_profile[1:])
    delta, _ = delta_from_profile(profile)
    gamma, lb, _sol = gamma_certified(s, inst=inst)
    kk = min(kmax, n)
    gammak = tuple(gamma_k(s, k)[0] for k in range(1, kk + 1))
    runs, max_run = n_runs_and_max_run(s)
    n_nodes, minlen_max, unary_max = node_stats(inst)
    if want_packing:
        packing, _w = inst.packing_bound(seed=0, restarts=24)
    else:
        packing = 0
    return {
        "n": n,
        "s": s,
        "profile": profile,
        "nfactors": sum(profile),
        "delta": delta,
        "delta_ceil": int(ceil(delta)),
        "gamma1": gammak[0] if gammak else 0,
        "gamma2": gammak[1] if len(gammak) > 1 else (gammak[0] if gammak else 0),
        "gammak": gammak,
        "n_runs": runs,
        "max_run": max_run,
        "period": shortest_period(s),
        "rare_gap": rare_gap(s),
        "packing": packing,
        "nodes": n_nodes,
        "minlen_max": minlen_max,
        "unary_max": unary_max,
        "gamma": gamma,
        "lb": lb,
    }
