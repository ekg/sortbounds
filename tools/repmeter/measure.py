#!/usr/bin/env python3
"""repmeter — exact measurements of the parameters that decide compressed-index size.

Python 3 standard library only (no numpy, no third-party packages), so the
numbers in README.md can be reproduced on a clean machine.

For a text S of length n over an alphabet of size sigma it computes

  n, sigma          -- exact
  r                 -- exact: number of equal-letter runs in the BWT of S$
  delta             -- exact rational: max_k d_k / k, d_k = #distinct length-k factors
  Gamma             -- a greedy string attractor (positions of S), |Gamma| exact
  delta <= gamma <= |Gamma|   -- certified bracket, since gamma is NP-hard
  index-size predictions in words  -- asymptotic, constants dropped

Every value is either exact or explicitly labelled as an approximation; nothing
is guessed.  See README.md for the meaning of each column and for the list of
things this tool deliberately does not do.

Conventions (stated once, used everywhere):
  * text symbols are non-negative ints; a file is read as raw bytes, so symbol
    i is byte i, and "--text ..." is encoded to UTF-8 first;
  * r is measured on S$ where $ is a new smallest symbol (the convention of the
    r-index); the no-sentinel value is also reported for reference;
  * delta is measured on S itself (no sentinel), over k = 1..n;
  * an attractor is a set of positions of S (0..n-1), and it is an attractor
    when every factor of S has an occurrence containing one of the positions.
"""

import argparse
import json
import math
import sys
import time

# --------------------------------------------------------------------------
# suffix array (prefix doubling) and LCP (Kasai)
# --------------------------------------------------------------------------


def suffix_array(sym, cyclic=False):
    """Suffix array (or cyclic-rotation array) by prefix doubling.

    O(n log^2 n) time, O(n) memory.  Not the fastest construction known
    (SA-IS / DC3 are linear); this one is short enough to audit.
    """
    n = len(sym)
    if n <= 1:
        return list(range(n))
    sa = sorted(range(n), key=sym.__getitem__)
    rank = [0] * n
    classes = 0
    prev = sym[sa[0]]
    for r in range(1, n):
        cur = sym[sa[r]]
        if cur != prev:
            classes += 1
            prev = cur
        rank[sa[r]] = classes
    k = 1
    while classes < n - 1 and k < n:
        if cyclic:
            def key(i, k=k, rank=rank):
                return (rank[i], rank[(i + k) % n])
        else:
            def key(i, k=k, rank=rank, n=n):
                j = i + k
                return (rank[i], rank[j] if j < n else -1)
        sa.sort(key=key)
        newrank = [0] * n
        classes = 0
        prevkey = key(sa[0])
        for r in range(1, n):
            curkey = key(sa[r])
            if curkey != prevkey:
                classes += 1
                prevkey = curkey
            newrank[sa[r]] = classes
        rank = newrank
        k <<= 1
    return sa


def lcp_array(sym, sa):
    """lcp[i] = LCP of the suffixes sa[i-1] and sa[i] (lcp[0] = 0), Kasai O(n)."""
    n = len(sym)
    rank = [0] * n
    for r, p in enumerate(sa):
        rank[p] = r
    lcp = [0] * n
    h = 0
    for i in range(n):
        r = rank[i]
        if r == 0:
            h = 0
            continue
        j = sa[r - 1]
        while i + h < n and j + h < n and sym[i + h] == sym[j + h]:
            h += 1
        lcp[r] = h
        if h:
            h -= 1
    return lcp


# --------------------------------------------------------------------------
# r: equal-letter runs in the BWT
# --------------------------------------------------------------------------


def bwt_and_runs_sentinel(sym):
    """BWT of S$ and its number of equal-letter runs.

    S$ has a unique smallest last symbol, so sorting the rotations of S$ is the
    same as sorting the suffixes of S$.
    """
    n = len(sym)
    if n == 0:
        return [], 0
    t = [c + 1 for c in sym] + [0]
    big_n = n + 1
    sa = suffix_array(t)
    bwt = [t[(p - 1) % big_n] for p in sa]
    runs = 1 + sum(1 for i in range(1, big_n) if bwt[i] != bwt[i - 1])
    return bwt, runs


def bwt_and_runs_cyclic(sym):
    """BWT of S taken as a cyclic string (no sentinel) and its run count.

    Only reported for reference: when n is not a multiple of the period the
    order of equal rotations is not unique, so this number is convention
    dependent.  Use the sentinel value for anything load-bearing.
    """
    n = len(sym)
    if n == 0:
        return [], 0
    sa = suffix_array(sym, cyclic=True)
    bwt = [sym[(p - 1) % n] for p in sa]
    runs = 1 + sum(1 for i in range(1, n) if bwt[i] != bwt[i - 1])
    return bwt, runs


# --------------------------------------------------------------------------
# delta: substring complexity
# --------------------------------------------------------------------------


def dk_profile(n, lcp, sa):
    """d_k = number of distinct factors of length k, for k = 0..n.  O(n) time/memory.

    Every distinct factor is owned by exactly one suffix: its first one in SA
    order.  Suffix i (SA index i) owns the lengths lcp[i]+1 .. n-sa[i], so

        d_k = #{ i : lcp[i] < k <= n - sa[i] },

    the number of intervals (lcp[i], n-sa[i]] containing k, which is a prefix sum
    of a difference array.  No factor is counted twice and none is missed.
    """
    prof = [0] * (n + 1)
    diff = [0] * (n + 2)
    for i in range(n):
        diff[lcp[i] + 1] += 1
        diff[n - sa[i] + 1] -= 1
    d = 0
    for k in range(1, n + 1):
        d += diff[k]
        prof[k] = d
    return prof


def delta_exact(prof):
    """argmax_k d_k / k as an unreduced fraction (d, k).  Exact integer comparison."""
    best_d, best_k = 0, 1
    for k in range(1, len(prof)):
        d = prof[k]
        if d * best_k > best_d * k:
            best_d, best_k = d, k
    return best_d, best_k


# --------------------------------------------------------------------------
# suffix automaton (used to *build* the greedy attractor)
# --------------------------------------------------------------------------


def build_sam(sym):
    """Suffix automaton: (maxlen, link, state_of_end) with state_of_end[e] the
    state whose endpos set contains e (e = 0..n-1, end positions of prefixes).

    A state's factor lengths are minlen..maxlen with minlen = maxlen(link)+1, and
    all factors of one state share one endpos set.
    """
    maxlen = [0]
    link = [-1]
    trans = [{}]
    state_of_end = [0] * len(sym)
    last = 0
    for idx, c in enumerate(sym):
        cur = len(maxlen)
        maxlen.append(maxlen[last] + 1)
        link.append(0)
        trans.append({})
        p = last
        while p != -1 and c not in trans[p]:
            trans[p][c] = cur
            p = link[p]
        if p == -1:
            link[cur] = 0
        else:
            q = trans[p][c]
            if maxlen[p] + 1 == maxlen[q]:
                link[cur] = q
            else:
                clone = len(maxlen)
                maxlen.append(maxlen[p] + 1)
                link.append(link[q])
                trans.append(dict(trans[q]))
                while p != -1 and trans[p].get(c) == q:
                    trans[p][c] = clone
                    p = link[p]
                link[q] = clone
                link[cur] = clone
        last = cur
        state_of_end[idx] = cur
    return maxlen, link, state_of_end


class BudgetExceeded(Exception):
    """Raised when a bounded run hits its budget instead of hanging."""


def greedy_attractor(sym, max_rounds=None, progress=None, budget_seconds=None):
    """Greedy attractor: repeatedly cover the currently longest uncovered factor.

    "Covered" is decided exactly, through the suffix automaton.  For a set Gamma
    and an end position e let last[e] = max{p in Gamma : p <= e}.  A factor of
    length k ending at e is covered iff k >= e - last[e] + 1, and a state v with
    endpos set E_v and lengths minlen(v)..maxlen(v) is fully covered iff
    min_{e in E_v} (e - last[e] + 1) <= minlen(v) -- within one state the endpos
    set is fixed, so longer factors are always the easier ones and the shortest
    length is the only one that can fail.  The min over E_v comes from one pass
    up the suffix-link tree.

    One round = O(n + #states).  Each round takes the longest uncovered factor,
    looks at an occurrence whose window [e-k+1, e] is uncovered (the one attaining
    the state's minimum), and places a position in the middle of that window: a
    point at p covers exactly the factors having an occurrence that straddles p,
    so the middle covers about twice as many as an end (placing at an end makes
    the greedy crawl one position per round).  The round count is |Gamma|, so the
    total cost is O(|Gamma| * n).

    Progress is the number of uncovered *distinct* factors,
        sum over states of max(0, min(maxlen, c-1) - minlen + 1),
    which is asserted to decrease every round and is capped at n+1 rounds (or at
    max_rounds, raising BudgetExceeded).  Note the cost is O(n * |Gamma|), and on
    incompressible text |Gamma| is Theta(n), so on long random text this is the
    expensive part of the tool; budget_seconds stops it with an exception rather
    than running for hours.  A budget changes only whether |Gamma| is computed,
    never its value.

    This is a heuristic: no optimality is claimed (gamma is NP-hard), and the
    result is checked by an independent verifier before it is reported.
    """
    n = len(sym)
    if n == 0:
        return []
    maxlen, link, state_of_end = build_sam(sym)
    ns = len(maxlen)
    minlen = [0] * ns
    for v in range(1, ns):
        minlen[v] = maxlen[link[v]] + 1
    order = sorted(range(ns), key=lambda v: -maxlen[v])   # suffix-link tree order

    inf = n + 2
    # last[e] = max Gamma-point <= e, or -1 when there is none; then
    # w = e - last[e] + 1 is the smallest covered length at e, and no factor of
    # length < w ending at e is covered.
    last = [-1] * n
    gamma = []
    uncovered_prev = None
    cap = n + 1 if max_rounds is None else min(n + 1, max_rounds)
    deadline = None if not budget_seconds else time.monotonic() + budget_seconds
    for _ in range(cap):
        if deadline is not None and len(gamma) % 64 == 0 and time.monotonic() > deadline:
            raise BudgetExceeded(
                "greedy attractor stopped by --greedy-budget-seconds after %d rounds "
                "(|Gamma| would be at least %d and there are still uncovered factors);"
                " pass --greedy-budget-seconds 0 to run it to the end"
                % (len(gamma), len(gamma)))
        c = [inf] * ns
        arg = [-1] * ns
        for e in range(n):
            w = e - last[e] + 1
            v = state_of_end[e]
            if w < c[v]:
                c[v] = w
                arg[v] = e
        best_unc = 0
        best_v = -1
        uncovered = 0
        for v in order:
            if v:                      # the root owns no factor (minlen = maxlen = 0)
                cv = c[v] - 1
                mv = minlen[v]
                if cv >= mv:
                    unc = maxlen[v] if maxlen[v] <= cv else cv
                    uncovered += unc - mv + 1
                    if unc > best_unc:
                        best_unc = unc
                        best_v = v
            p = link[v]
            if p >= 0 and c[v] < c[p]:
                c[p] = c[v]
                arg[p] = arg[v]
        if best_v < 0:
            assert uncovered == 0
            return gamma
        if uncovered_prev is not None and uncovered >= uncovered_prev:
            raise RuntimeError("greedy attractor made no progress: %d uncovered "
                               "factors before and after placing a position"
                               % uncovered)
        uncovered_prev = uncovered
        e_star = arg[best_v]                     # end of an uncovered occurrence
        lo = e_star - best_unc + 1               # start of that occurrence
        pos = (lo + e_star + 1) // 2             # middle of the window
        gamma.append(pos)
        if progress is not None and len(gamma) % progress == 0:
            sys.stderr.write("  greedy: %d rounds, %d uncovered factors so far\n"
                             % (len(gamma), uncovered))
            sys.stderr.flush()
        q = pos
        while q < n and last[q] < pos:
            last[q] = pos
            q += 1
    raise BudgetExceeded("greedy attractor stopped by --max-greedy-rounds = %d "
                         "(n = %d); raise it to run to the end" % (cap, n))


# --------------------------------------------------------------------------
# verifiers: is Gamma an attractor?  (two independent implementations)
# --------------------------------------------------------------------------


class RangeMin:
    """Sparse-table range minimum (O(n log n) build, O(1) query)."""

    def __init__(self, arr):
        n = len(arr)
        self.log = [0] * (n + 1)
        for i in range(2, n + 1):
            self.log[i] = self.log[i >> 1] + 1
        table = [arr]
        k = 1
        while (1 << k) <= n:
            prev = table[-1]
            half = 1 << (k - 1)
            table.append([min(prev[i], prev[i + half])
                          for i in range(n - (1 << k) + 1)])
            k += 1
        self.table = table

    def query(self, lo, hi):
        k = self.log[hi - lo + 1]
        row = self.table[k]
        return min(row[lo], row[hi - (1 << k) + 1])


def verify_attractor_sa(sym, gamma, sa=None, lcp=None):
    """Exact check of the definition, O(n log n) worst case.  Independent of the
    greedy: it works from the suffix tree (LCP intervals) over start positions,
    while the greedy works from the suffix automaton over end positions.

    For a position j let w[j] = (next Gamma point at or after j) - j + 1, plus
    infinity when there is none, so that a factor starting at j of length k is
    covered iff w[j] <= k.  Every distinct factor is represented exactly once by
    a node of the suffix tree: an explicit node with SA interval [lo, hi] and
    parent depth pd owns the factor lengths pd+1..depth, all with occurrence set
    [lo, hi]; a leaf owns the lengths pd+1..n-sa[r].  Inside one node coverage
    only gets easier as k grows, so the node is fully covered iff its shortest
    factor is, i.e. iff min_{j in [lo,hi]} w[sa[j]] <= pd+1.

    Returns (ok, witness) where witness = (start, length) of an uncovered factor.
    """
    n = len(sym)
    gammaset = set(gamma)
    if any(p < 0 or p >= n for p in gammaset):
        raise ValueError("attractor position out of range")
    if n == 0:
        return True, None
    if sa is None:
        sa = suffix_array(sym)
    if lcp is None:
        lcp = lcp_array(sym, sa)
    inf = n + 2
    nxt = [inf] * n
    cur = inf
    for j in range(n - 1, -1, -1):
        if j in gammaset:
            cur = j
        nxt[j] = cur
    w = [inf if nxt[j] == inf else nxt[j] - j + 1 for j in range(n)]
    arr = [w[p] for p in sa]
    rmq = RangeMin(arr)

    def witness_in(lo, hi, shortest):
        for r in range(lo, hi + 1):
            if arr[r] > shortest:
                return (sa[r], shortest)
        raise AssertionError("range min disagrees with linear scan")

    # A suffix is a leaf of the suffix tree; it owns the lengths
    # max(lcp[r], lcp[r+1])+1 .. n-sa[r], and owns none when its parent depth is
    # already its own length (the suffix is then a prefix of a neighbour, and its
    # factors belong to the explicit node above it).
    for r in range(n):
        own = n - sa[r]
        pd = lcp[r] if lcp[r] > (lcp[r + 1] if r + 1 < n else 0) else (lcp[r + 1] if r + 1 < n else 0)
        if pd >= own:
            continue
        shortest = pd + 1
        if arr[r] > shortest:
            return False, (sa[r], shortest)

    # Explicit internal nodes: the LCP intervals, depth = their lcp value.
    # Bottom-up walk with the standard stack; an interval [lo, hi] of depth d owns
    # the lengths (parent depth)+1 .. d, and for those lengths the occurrence set
    # is exactly [lo, hi] (that is what makes an LCP interval a suffix-tree node).
    #
    # The interval enclosing a closed one has depth max(cur, depth of the stack top
    # after the pop): `cur` when the parent is only delimited later (its depth is
    # the LCP value that closes the child), the stack top when several intervals
    # close at once at the end of the text.
    stack = [(0, 0)]                      # (depth, lo)
    for i in range(1, n + 1):
        cur = lcp[i] if i < n else 0
        lo = i - 1
        while stack[-1][0] > cur:
            depth, ilo = stack.pop()
            parent_depth = stack[-1][0] if stack[-1][0] > cur else cur
            if depth > parent_depth and rmq.query(ilo, i - 1) > parent_depth + 1:
                return False, witness_in(ilo, i - 1, parent_depth + 1)
            lo = ilo
        if i < n and stack[-1][0] < cur:
            stack.append((cur, lo))
    return True, None


def verify_attractor_bruteforce(sym, gamma):
    """Exact check by the definition, no clever machinery: enumerate every
    distinct factor and every occurrence.  O(n^3) time, O(n^2) memory; only for
    small texts (and for cross-checking the fast verifier).

    Returns (ok, witness) with witness = (factor, length).
    """
    n = len(sym)
    gammaset = set(gamma)
    if any(p < 0 or p >= n for p in gammaset):
        raise ValueError("attractor position out of range")
    for k in range(1, n + 1):
        covered = {}
        for i in range(n - k + 1):
            key = tuple(sym[i:i + k])
            hit = any(p in gammaset for p in range(i, i + k))
            if hit:
                covered[key] = True
            elif key not in covered:
                covered[key] = False
        for key, ok in covered.items():
            if not ok:
                return False, (key, k)
    return True, None


def gamma_bruteforce(sym, limit=14):
    """Smallest attractor by exhaustive search over subsets.  Only for tiny n."""
    import itertools
    n = len(sym)
    if n > limit:
        raise ValueError("exhaustive gamma only for n <= %d" % limit)
    for size in range(0, n + 1):
        for comb in itertools.combinations(range(n), size):
            if verify_attractor_bruteforce(sym, comb)[0]:
                return comb
    return tuple(range(n))


# --------------------------------------------------------------------------
# predicted index sizes (asymptotic word counts, constants dropped)
# --------------------------------------------------------------------------


def index_predictions(n, sigma, r, delta_num, delta_den):
    """Asymptotic word counts from docs/research/SYNTHESIS.md.

    r-index (GNP'20)                      O(r) words
    delta-optimal (KNP, IEEE TIT'23 VI.6) O(delta * log(n log sigma / (delta log n))) words

    These are big-O word counts with constants dropped, NOT measured bytes; the
    logarithms are taken in base 2.  If the log argument is <= 1 the bound read
    literally says "O(delta or less)", printed here as <= delta.
    """
    out = {"r_index_words": r}
    delta = delta_num / delta_den
    out["delta_optimal_words"] = None
    out["delta_optimal_note"] = ""
    if n < 2 or sigma < 2 or delta <= 0:
        out["delta_optimal_note"] = "not applicable (n < 2 or sigma < 2)"
        return out
    log_sigma = math.log2(sigma)
    log_n = math.log2(n)
    if log_sigma <= 0 or log_n <= 0:
        out["delta_optimal_note"] = "not applicable (log sigma or log n is 0)"
        return out
    arg = (n * log_sigma) / (delta * log_n)
    if arg <= 1.0:
        out["delta_optimal_words"] = delta
        out["delta_optimal_note"] = "log argument <= 1: bound reads O(delta)"
        return out
    out["delta_optimal_words"] = delta * math.log2(arg)
    out["delta_optimal_note"] = "log2 argument = %.3f" % arg
    return out


# --------------------------------------------------------------------------
# generators (so the numbers in README.md are reproducible)
# --------------------------------------------------------------------------


def gen_text(spec):
    """--gen NAME[:ARG[:SEED]] -> list of int symbols."""
    import random
    parts = spec.split(":")
    name = parts[0]
    if name == "fibonacci":
        k = int(parts[1]) if len(parts) > 1 else 20
        # w_1 = a, w_2 = ab, w_{j+1} = w_j w_{j-1}, so |w_j| = F_{j+1} with
        # F_1 = F_2 = 1; return the Fibonacci word of length F_k (w_{k-1}).
        if k <= 2:                     # F_1 = F_2 = 1
            return [0]
        f_prev, f_cur = 1, 1
        for _ in range(2, k):
            f_prev, f_cur = f_cur, f_prev + f_cur
        target = f_cur
        a, b = [0], [0, 1]
        while len(b) < target:
            a, b = b, b + a
        return b
    if name == "thue-morse":
        k = int(parts[1]) if len(parts) > 1 else 16
        t = [0]
        for _ in range(k):
            t = t + [1 - c for c in t]
        return t
    if name == "random-binary":
        n = int(parts[1]) if len(parts) > 1 else 1 << 16
        seed = int(parts[2]) if len(parts) > 2 else 20240601
        rng = random.Random(seed)
        return [rng.getrandbits(1) for _ in range(n)]
    raise SystemExit("unknown --gen generator %r" % name)


# --------------------------------------------------------------------------
# main measurement
# --------------------------------------------------------------------------


def fmt_fraction(num, den):
    if den == 1:
        return "%d" % num
    return "%d/%d = %.4f" % (num, den, num / den)


def measure(sym, verbose=False, crosscheck=False, max_greedy_n=0,
            max_greedy_rounds=None, greedy_budget_seconds=60):
    t0 = time.time()
    n = len(sym)
    sigma = len(set(sym))
    res = {"n": n, "sigma": sigma}
    if n == 0:
        res["note"] = "empty text: nothing to measure"
        return res

    sa = suffix_array(sym)
    lcp = lcp_array(sym, sa)
    t_sa = time.time() - t0

    prof = dk_profile(n, lcp, sa)
    d_num, d_k = delta_exact(prof)
    t_delta = time.time() - t0

    bwt, r = bwt_and_runs_sentinel(sym)
    _, r_cyclic = bwt_and_runs_cyclic(sym)
    t_bwt = time.time() - t0

    gamma = None
    witness = None
    skipped = None
    if max_greedy_n and n > max_greedy_n:
        skipped = ("n = %d > --max-greedy-n = %d: the greedy attractor costs "
                   "O(n*|Gamma|) and is skipped; pass --max-greedy-n 0 to force it"
                   % (n, max_greedy_n))
    else:
        try:
            gamma = greedy_attractor(sym, max_rounds=max_greedy_rounds,
                                     budget_seconds=greedy_budget_seconds,
                                     progress=None if n < 4096 else 500)
        except BudgetExceeded as exc:
            gamma = None
            skipped = str(exc)
    t_greedy = time.time() - t0
    if gamma is not None:
        ok, witness = verify_attractor_sa(sym, gamma, sa=sa, lcp=lcp)
    else:
        ok = None
    t_verify = time.time() - t0

    res.update({
        "delta_num": d_num,
        "delta_den": d_k,
        "delta_argmax_k": d_k,
        "delta": d_num / d_k,
        "r": r,
        "r_cyclic_no_sentinel": r_cyclic,
        "runs_per_char": r / n,
        "delta_per_char": (d_num / d_k) / n,
        "greedy_attractor_size": None if gamma is None else len(gamma),
        "greedy_attractor_verified": ok,
        "greedy_attractor_witness": witness,
        "greedy_attractor_skipped": skipped,
        "greedy_over_delta": None if gamma is None else len(gamma) / (d_num / d_k),
    })
    res.update(index_predictions(n, sigma, r, d_num, d_k))
    res["d_k"] = prof[1:] if verbose else None

    # facts that must hold for every text: delta >= 1, delta >= sigma, and
    # delta <= gamma <= |Gamma| whenever |Gamma| was computed and verified
    assert d_num >= 1 and d_k >= 1
    assert d_num >= d_k * sigma, "delta >= sigma violated"
    if gamma is not None:
        assert len(gamma) >= 1 and ok
        assert d_num <= d_k * len(gamma), "bracket delta <= |Gamma| violated"

    if crosscheck:
        b_num, b_k = delta_exact_bruteforce(sym)
        assert (b_num, b_k) == (d_num, d_k), "delta mismatch: %s vs %s" % (
            (d_num, d_k), (b_num, b_k))
        _, rb = bwt_and_runs_sentinel_bruteforce(sym)
        assert rb == r, "r mismatch: %d vs %d" % (r, rb)
        if gamma is not None:
            ok2, wit2 = verify_attractor_bruteforce(sym, gamma)
            assert ok2, "brute-force verifier rejected the greedy attractor: %s" % (wit2,)
        res["brute_force_crosscheck"] = "ok"
        if n <= 14 and gamma is not None:
            best = gamma_bruteforce(sym)
            res["gamma_exact"] = len(best)
            res["gamma_exact_witness"] = list(best)

    res["timing_s"] = {
        "suffix_array_and_lcp": round(t_sa, 3),
        "delta": round(t_delta - t_sa, 3),
        "bwt": round(t_bwt - t_delta, 3),
        "greedy_attractor": round(t_greedy - t_bwt, 3),
        "verify": round(t_verify - t_greedy, 3),
        "total": round(t_verify, 3),
    }
    res["_gamma_positions"] = gamma or []
    res["_bwt"] = bwt if verbose else None
    return res


def delta_exact_bruteforce(sym):
    """Reference delta: distinct factors by sets.  O(n^2) memory."""
    n = len(sym)
    prof = [0] * (n + 1)
    for k in range(1, n + 1):
        prof[k] = len({tuple(sym[i:i + k]) for i in range(n - k + 1)})
    return delta_exact(prof)


def bwt_and_runs_sentinel_bruteforce(sym):
    """Reference BWT: sort all rotations of S$ explicitly."""
    n = len(sym)
    if n == 0:
        return [], 0
    t = [c + 1 for c in sym] + [0]
    big_n = n + 1
    order = sorted(range(big_n), key=lambda i: t[i:] + t[:i])
    bwt = [t[(p - 1) % big_n] for p in order]
    return bwt, 1 + sum(1 for i in range(1, big_n) if bwt[i] != bwt[i - 1])


def report(res, label, verbose=False):
    n = res["n"]
    if n == 0:
        print("empty text: nothing to measure")
        return
    sigma = res["sigma"]
    print("input       : %s" % label)
    print("n           : %d" % n)
    print("sigma       : %d  (distinct bytes/symbols)" % sigma)
    print("r           : %d  exact, equal-letter runs of BWT of S$  [O(n log^2 n)]"
          % res["r"])
    print("              (no-sentinel cyclic BWT would give %d; convention dependent)"
          % res["r_cyclic_no_sentinel"])
    print("delta       : %s  exact, max_k d_k/k at k = %d  [O(n) after SA+LCP]"
          % (fmt_fraction(res["delta_num"], res["delta_den"]), res["delta_argmax_k"]))
    if res["greedy_attractor_size"] is None:
        print("|Gamma|     : not computed -- %s" % res["greedy_attractor_skipped"])
        print("bracket     : %s <= gamma <= ?   (no upper bound without |Gamma|)"
              % fmt_fraction(res["delta_num"], res["delta_den"]))
    else:
        print("|Gamma|     : %d  greedy attractor, verified = %s  [O(|Gamma| n)]"
              % (res["greedy_attractor_size"], res["greedy_attractor_verified"]))
        print("bracket     : %s <= gamma <= %d   (gamma itself is NP-hard; |Gamma| is"
              " only an upper bound)"
              % (fmt_fraction(res["delta_num"], res["delta_den"]),
                 res["greedy_attractor_size"]))
    print("predicted index size, asymptotic words (constants dropped, NOT bytes):")
    print("  r-index            : ~%d words   (r/n = %.5f)"
          % (res["r_index_words"], res["runs_per_char"]))
    if res["delta_optimal_words"] is None:
        print("  delta-optimal      : n/a  (%s)" % res["delta_optimal_note"])
    else:
        print("  delta-optimal      : ~%.1f words   (ratio to n = %.5f)  [%s]"
              % (res["delta_optimal_words"],
                 res["delta_optimal_words"] / n, res["delta_optimal_note"]))
    if res["greedy_over_delta"] is not None:
        print("  |Gamma|/delta      : %.2f" % res["greedy_over_delta"])
    if res.get("brute_force_crosscheck"):
        print("cross-check : delta and r agree with brute force; brute-force"
              " attractor verifier accepts Gamma")
    if "gamma_exact" in res:
        print("gamma       : %d  (exact, exhaustive subset search, n <= 14)"
              % res["gamma_exact"])
    print("timing (s)  : %s" % json.dumps(res["timing_s"]))
    if verbose:
        print("d_k         : %s" % res["d_k"])
        print("Gamma       : %s" % res["_gamma_positions"])
        if res["_bwt"] is not None:
            print("BWT(S$)     : %s" % res["_bwt"])


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Measure r, delta, a greedy attractor and the bracket "
                    "delta <= gamma <= |Gamma| for a text.")
    src = ap.add_mutually_exclusive_group()
    src.add_argument("file", nargs="?", help="file; read as raw bytes")
    src.add_argument("--text", help="measure this literal string (UTF-8)")
    src.add_argument("--gen", help="generated input: fibonacci:K | thue-morse:K | "
                                  "random-binary:N:SEED")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    ap.add_argument("--verbose", action="store_true", help="also print d_k, BWT, Gamma")
    ap.add_argument("--crosscheck", action="store_true",
                    help="also run the slow O(n^2)/O(n^3) reference implementations")
    ap.add_argument("--greedy-budget-seconds", type=float, default=60.0, metavar="S",
                    help="wall-clock budget for the greedy attractor (default 60;"
                         " 0 = no limit).  The greedy costs O(n*|Gamma|) and |Gamma|"
                         " is Theta(n) on incompressible text, so on long random text"
                         " it is the expensive part.  A budget only decides whether"
                         " |Gamma| is computed, never its value.")
    ap.add_argument("--max-greedy-n", type=int, default=0, metavar="N",
                    help="skip the greedy attractor above this length (default 0 ="
                         " no limit)")
    ap.add_argument("--max-greedy-rounds", type=int, default=None, metavar="R",
                    help="hard cap on greedy rounds (each round places one position)")
    args = ap.parse_args(argv)

    if args.gen:
        sym = gen_text(args.gen)
        label = "gen:" + args.gen
    elif args.text is not None:
        sym = list(args.text.encode("utf-8"))
        label = "text"
    elif args.file:
        with open(args.file, "rb") as fh:
            sym = list(fh.read())
        label = args.file
    else:
        data = sys.stdin.buffer.read()
        sym = list(data)
        label = "<stdin>"

    auto_crosscheck = args.crosscheck or len(sym) <= 60
    res = measure(sym, verbose=args.verbose, crosscheck=auto_crosscheck,
                  max_greedy_n=args.max_greedy_n,
                  max_greedy_rounds=args.max_greedy_rounds,
                  greedy_budget_seconds=args.greedy_budget_seconds)
    if args.json:
        out = {k: v for k, v in res.items() if not k.startswith("_")}
        out["input"] = label
        json.dump(out, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        report(res, label, verbose=args.verbose)
    return 0


if __name__ == "__main__":
    sys.exit(main())
