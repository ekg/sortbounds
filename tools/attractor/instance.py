"""instance.py -- the minimum-attractor problem as an explicit set-cover instance.

Definitions used throughout this directory (S is the text, n = |S|, positions are
0..n-1):

  factor        a contiguous substring S[i:i+k], k >= 1;
  cover(p)      the set of distinct factors having an occurrence [i, i+k) with
                i <= p < i+k  ("crossing" p);
  attractor     a set Gamma of positions with union_{p in Gamma} cover(p) = all
                distinct factors of S;
  gamma         the smallest |Gamma| over all attractors.

THE UNIVERSE IS SMALLER THAN IT LOOKS.  The suffix tree of S has one node per
class of factors that share an occurrence set: node v with SA interval [lo, hi],
depth d and parent depth pd < d owns the factors of length pd+1 .. d, and every
one of those factors occurs exactly at the starts sa[lo..hi].  Two consequences
drive this whole directory:

  (R1)  Gamma is an attractor  <=>  for every node v, the SHORTEST factor of v
        (length pd+1, starts sa[lo..hi]) is covered by Gamma.
        (<=) if f is owned by v and some occurrence [i, i+pd+1) crosses p then
        [i, i+|f|) contains [i, i+pd+1) and so also crosses p; (=>) trivially.
        So the universe of the set-cover instance may be taken to be the nodes,
        which number at most 2n-1 instead of Theta(n^2) distinct factors.

  (R2)  For a factor f let C(f) = {p : p crosses some occurrence of f} = the set
        of positions whose cover contains f.  Inside one node C is monotone in
        the length, and occurrences are shared, so for f owned by v,
        C(f) >= C(shortest factor of v).  Hence a family of pairwise disjoint
        C-sets using arbitrary factors is matched in size by one using only the
        shortest factors of distinct nodes, and two factors of the same node
        never have disjoint C-sets.  So the packing lower bound (see
        packing_bound) loses nothing by looking at representatives only.

Costs: __init__ is O(n log^2 n) for SA + LCP (repmeter's prefix doubling) plus
O(sum over nodes of |occurrences|) to build the position/node bit masks.
`uncovered` is O(n + #nodes).  `verify` is the slow, definition-level check and
is deliberately not the fast path (see its docstring).

Only the suffix array, the LCP array and d_k/delta come from ../repmeter; the
attractor-specific code here is independent of repmeter's greedy bookkeeping.
"""

import os
import random
import sys
import time
from bisect import bisect_left
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPMETER = os.path.normpath(os.path.join(_HERE, os.pardir, "repmeter"))
if _REPMETER not in sys.path:
    sys.path.insert(0, _REPMETER)

from measure import (                  # noqa: E402  (path set up just above)
    RangeMin,
    delta_exact,
    dk_profile,
    lcp_array,
    suffix_array,
)


class Node:
    """One suffix-tree node: the factors of length min_len..depth share starts.

    lo, hi        SA interval; the occurrence starts are sa[lo..hi]
    depth         longest factor owned by the node
    parent_depth  longest factor owned by the parent; the node owns
                  parent_depth+1 .. depth, i.e. (depth - parent_depth) factors
    """

    __slots__ = ("lo", "hi", "depth", "parent_depth")

    def __init__(self, lo, hi, depth, parent_depth):
        assert 0 <= lo <= hi
        assert 0 <= parent_depth < depth
        self.lo = lo
        self.hi = hi
        self.depth = depth
        self.parent_depth = parent_depth

    @property
    def min_len(self):
        return self.parent_depth + 1

    @property
    def nfactors(self):
        return self.depth - self.parent_depth

    def __repr__(self):
        return "Node([%d,%d], %d..%d)" % (self.lo, self.hi, self.min_len, self.depth)


def normalize_text(text):
    """str | bytes | iterable of ints -> list of int symbols."""
    if isinstance(text, str):
        return list(text.encode("utf-8"))
    if isinstance(text, (bytes, bytearray)):
        return list(text)
    out = []
    for c in text:
        if not isinstance(c, int) or c < 0:
            raise TypeError("symbols must be non-negative ints")
        out.append(c)
    return out


def suffix_tree_nodes(sym, sa, lcp):
    """Every suffix-tree node of S as a Node, in a bottom-up-compatible order.

    The LCP-interval sweep: a stack of open intervals by depth; when lcp drops
    below the top interval's depth that interval is closed and its parent is the
    interval with depth max(stack top after the pop, the closing lcp value).
    Leaves are the suffixes; a leaf owns the lengths above the deeper of its two
    neighbour LCPs, and owns nothing when it is a prefix of a neighbour (its
    full length is already inside an explicit node).
    """
    n = len(sa)
    nodes = []
    stack = [(0, 0)]                       # (depth, lo); the root, depth 0
    for i in range(1, n + 1):
        cur = lcp[i] if i < n else 0
        lo = i - 1
        while stack[-1][0] > cur:
            depth, ilo = stack.pop()
            parent_depth = stack[-1][0] if stack[-1][0] > cur else cur
            nodes.append(Node(ilo, i - 1, depth, parent_depth))
            lo = ilo
        if i < n and stack[-1][0] < cur:
            stack.append((cur, lo))

    # leaves: suffix sa[r] owns the lengths parent+1 .. n-sa[r]
    for r in range(n):
        own = n - sa[r]
        left = lcp[r]
        right = lcp[r + 1] if r + 1 < n else 0
        parent_depth = left if left > right else right
        if parent_depth < own:
            nodes.append(Node(r, r, own, parent_depth))
    return nodes


class Instance:
    """Set-cover instance of one text.  See the module docstring for the model."""

    def __init__(self, text):
        self.sym = normalize_text(text)
        self.n = len(self.sym)
        n = self.n
        self.sa = suffix_array(self.sym) if n else []
        self.lcp = lcp_array(self.sym, self.sa) if n else []
        self.nodes = suffix_tree_nodes(self.sym, self.sa, self.lcp) if n else []
        self._checks()

        # full_mask: one bit per node (the set-cover universe)
        self.full_mask = (1 << len(self.nodes)) - 1
        # cover_masks[p]: bits of the nodes whose shortest factor p crosses
        self.cover_masks = [0] * n
        # elem_masks[v]: bits of the positions p that cross the shortest factor of v
        self.elem_masks = [0] * len(self.nodes)
        self._build_masks()

    # -- construction -------------------------------------------------------

    def _checks(self):
        """The node decomposition must partition the distinct factors."""
        n, sa, lcp = self.n, self.sa, self.lcp
        if n == 0:
            return
        prof = dk_profile(n, lcp, sa)
        self.d_profile = prof
        total = sum(v.nfactors for v in self.nodes)
        assert total == sum(prof[1:]), (
            "suffix-tree decomposition does not partition the distinct factors: "
            "%d owned vs %d distinct" % (total, sum(prof[1:])))
        for v in self.nodes:
            assert v.depth <= n - sa[v.lo]

    def _build_masks(self):
        """Fill cover_masks / elem_masks from C(shortest factor of each node).

        C(f) for f = S[i:i+len) is a union of the position intervals [i, i+len);
        the starts of one node are sorted first so the union is a linear merge,
        and the (usually very few) merged intervals are OR-ed into a bit mask.
        """
        n, sa, nodes = self.n, self.sa, self.nodes
        for v in range(len(nodes)):
            nd = nodes[v]
            length = nd.min_len
            starts = sorted(sa[nd.lo:nd.hi + 1])
            mask = 0
            bit = 1 << v
            cur_lo = cur_hi = -1
            for i in starts:
                lo, hi = i, i + length - 1
                if cur_hi >= 0 and lo <= cur_hi + 1:
                    if hi > cur_hi:
                        cur_hi = hi
                else:
                    if cur_hi >= 0:
                        mask |= ((1 << (cur_hi - cur_lo + 1)) - 1) << cur_lo
                        for p in range(cur_lo, cur_hi + 1):
                            self.cover_masks[p] |= bit
                    cur_lo, cur_hi = lo, hi
            if cur_hi >= 0:
                mask |= ((1 << (cur_hi - cur_lo + 1)) - 1) << cur_lo
                for p in range(cur_lo, cur_hi + 1):
                    self.cover_masks[p] |= bit
            self.elem_masks[v] = mask

    # -- the node's own factor, for printing witnesses ----------------------

    def node_factor(self, v):
        """The shortest factor of node v, as the actual substring (list of ints)."""
        nd = self.nodes[v]
        i = self.sa[nd.lo]
        return self.sym[i:i + nd.min_len]

    # -- delta --------------------------------------------------------------

    def delta(self):
        """delta = max_k d_k / k, exactly, as a Fraction (KNP: delta <= gamma)."""
        if self.n == 0:
            return Fraction(0)
        num, den = delta_exact(self.d_profile)
        return Fraction(num, den)

    def delta_argmax(self):
        if self.n == 0:
            return (0, 1)
        return delta_exact(self.d_profile)

    # -- fast path: how many distinct factors are still uncovered -----------

    def uncovered(self, gamma):
        """Number of distinct factors of S not covered by gamma.  0 <=> attractor.

        For a position set Gamma let nxt[i] be the smallest p in Gamma with
        p >= i (infinity if none) and K[i] = nxt[i]-i+1 (infinity if none): a
        window starting at i is covered iff its length is at least K[i].  A node
        v is an attractor-hole in the lengths [min_len, min(max_len, cov-1)] with
        cov = min over its occurrences of K, which is one range-minimum query on
        the array K[sa[.]].  This is the counting fast path; `verify` below is
        the independent definition-level decision procedure.
        """
        n = self.n
        pts = sorted(set(gamma))
        for p in pts:
            if not 0 <= p < n:
                raise ValueError("attractor position %r out of range" % (p,))
        if n == 0:
            return 0
        big = n + 2
        nxt = [big] * n
        is_pt = [False] * n
        for p in pts:
            is_pt[p] = True
        cur = big
        for i in range(n - 1, -1, -1):
            if is_pt[i]:
                cur = i
            nxt[i] = cur
        k_arr = [big if nxt[i] == big else nxt[i] - i + 1 for i in range(n)]
        rmq = RangeMin([k_arr[p] for p in self.sa])
        total = 0
        for nd in self.nodes:
            cov = rmq.query(nd.lo, nd.hi)
            shortest = nd.min_len
            if cov <= shortest:
                continue
            top = nd.depth if nd.depth < cov - 1 else cov - 1
            if top >= shortest:
                total += top - shortest + 1
        return total

    def covered_nodes(self, gamma):
        """Bit mask of the nodes covered by gamma (set-cover bookkeeping)."""
        mask = 0
        for p in gamma:
            mask |= self.cover_masks[p]
        return mask

    def coverers(self):
        """coverers[v] = the positions p whose cover contains node v (cached)."""
        cached = getattr(self, "_coverers_cache", None)
        if cached is not None:
            return cached
        coverers = [[] for _ in self.nodes]
        for p, mask in enumerate(self.cover_masks):
            u = mask
            while u:
                b = u & -u
                coverers[b.bit_length() - 1].append(p)
                u ^= b
        self._coverers_cache = coverers
        return coverers

    def rarest_element(self, need):
        """Of the nodes in `need`, the one with the fewest covering positions."""
        coverers = self.coverers()
        best, best_n = -1, None
        u = need
        while u:
            b = u & -u
            v = b.bit_length() - 1
            u ^= b
            cnt = len(coverers[v])
            if best_n is None or cnt < best_n:
                best, best_n = v, cnt
                if cnt <= 1:
                    break
        return best

    def position_covering(self, need):
        """A single position whose cover contains every node in `need`, or None.

        Only positions covering the rarest node of `need` can qualify, which is
        what keeps the local search's inner loop short.
        """
        if need == 0:
            return -1
        e = self.rarest_element(need)
        cm = self.cover_masks
        for p in self.coverers()[e]:
            if cm[p] & need == need:
                return p
        return None

    def uncovered_nodes(self, gamma):
        """Number of nodes (not factors) not covered by gamma."""
        return bin(self.full_mask & ~self.covered_nodes(gamma)).count("1")

    # -- the independent, definition-level check ---------------------------

    def witness(self, gamma):
        """First uncovered distinct factor found by a from-scratch definition check.

        Returns None when gamma is an attractor, else (factor_as_list, start_of_
        that_occurrence).  This is the INDEPENDENT check: it does not use
        cover_masks, elem_masks, `uncovered`, or anything the greedy updated.  It
        enumerates the distinct factors and, for each, scans its occurrence starts
        and intersects the concrete interval [i, i+len) with the sorted point list.

        Every distinct factor is visited: the suffix-tree nodes partition them
        (R1 in the module docstring), and inside a node all lengths share the
        occurrence set, while a longer window at the same start contains the
        shorter one -- so if the shortest factor of a node has no covered
        occurrence then every factor of that node is uncovered, and conversely a
        covered occurrence of the shortest one covers all longer factors there.
        The shortest factor of each node is therefore the only length that has to
        be tested, and check.py cross-checks that claim against a brute-force
        enumeration of every window: all position sets of every binary text of
        length <= 8, and random position sets of longer texts.
        """
        n = self.n
        pts = sorted(set(gamma))
        for p in pts:
            if not 0 <= p < n:
                raise ValueError("attractor position %r out of range" % (p,))
        if n == 0:
            return None
        for nd in self.nodes:
            length = nd.min_len
            hit = False
            for r in range(nd.lo, nd.hi + 1):
                i = self.sa[r]
                # explicit interval intersection: does [i, i+length) hold a point?
                j = bisect_left(pts, i)
                if j < len(pts) and pts[j] < i + length:
                    hit = True
                    break
            if not hit:
                i = self.sa[nd.lo]
                return (self.sym[i:i + length], i)
        return None

    def verify(self, gamma):
        """True iff gamma is an attractor, by the definition-level check above."""
        return self.witness(gamma) is None

    # -- packing lower bound ------------------------------------------------

    def packing_bound(self, seed=0, restarts=24, deadline=None):
        """A certified packing: k factors with pairwise disjoint C-sets, so gamma >= k.

        Two factors f, g can both be forced to different positions only if no
        single position crosses an occurrence of both, i.e. C(f) & C(g) = {}.
        A family f_1..f_k of them needs k distinct positions of any attractor
        (each f_j needs some p_j crossing it, and p_i = p_j would cross both), so
        gamma >= k.  By (R2) it suffices to look at the shortest factor of each
        node, and C of that factor is elem_masks[v].

        The maximum such family is a maximum independent set in the "C-sets
        intersect" graph -- NP-hard -- so this is a heuristic on top of a valid
        certificate: whatever family it returns is re-checked by
        `certify_packing`.  Returns (k, witnesses) with witnesses a list of
        (node_index, factor as list of ints, factor as str).
        """
        nodes = self.nodes
        m = len(nodes)
        if m == 0:
            return 0, []
        order_base = sorted(range(m), key=lambda v: (bin(self.elem_masks[v]).count("1"),
                                                    nodes[v].nfactors, v))
        best = []
        rng = random.Random(seed)
        for it in range(restarts):
            if deadline is not None and it and time.monotonic() > deadline:
                break
            if it == 0:
                order = order_base
            elif it < restarts // 3:
                order = sorted(range(m), key=lambda v: (nodes[v].nfactors, v))
            elif it < 2 * restarts // 3:
                order = sorted(range(m), key=lambda v: (-nodes[v].nfactors, v))
            else:
                order = order_base[:]
                rng.shuffle(order)
            chosen = []
            used = 0
            for v in order:
                mv = self.elem_masks[v]
                if mv & used:
                    continue
                chosen.append(v)
                used |= mv
            if len(chosen) > len(best):
                best = chosen
        best.sort()
        return len(best), [(v, self.node_factor(v),
                            factor_str(self.sym, self.node_factor(v))) for v in best]

    def certify_packing(self, witnesses):
        """Re-check a packing from the text alone; returns (ok, detail).

        Independent of elem_masks: for each witness factor the occurrence starts
        are found by scanning the text, C is rebuilt as the union of the concrete
        intervals [i, i+len), and the crossing-position sets must be pairwise
        disjoint.  Every position is checked against every factor's C, so this is
        the "no position covers two of them" argument done exhaustively.
        """
        n = self.n
        sets = []
        for w in witnesses:
            if not (isinstance(w, (tuple, list)) and len(w) == 3):
                raise TypeError("a packing witness is the (node, factor, text) triple "
                                "returned by packing_bound, not %r" % (w,))
            factor = list(w[1])
            length = len(factor)
            if length == 0:
                return False, "empty factor"
            hits = set()
            found = False
            for i in range(0, n - length + 1):
                if self.sym[i:i + length] == factor:
                    found = True
                    hits.update(range(i, i + length))
            if not found:
                return False, "factor %r does not occur in the text" % (factor,)
            sets.append(hits)
        for a in range(len(sets)):
            for b in range(a + 1, len(sets)):
                if sets[a] & sets[b]:
                    return False, ("factors %r and %r share position %d"
                                   % (witnesses[a][1], witnesses[b][1],
                                      min(sets[a] & sets[b])))
        for p in range(n):
            if sum(1 for s in sets if p in s) > 1:
                return False, "position %d crosses two witness factors" % p
        return True, [sorted(s) for s in sets]


def factor_str(sym, factor):
    """Render a factor as text when it is printable, else as byte values.

    Texts built from raw symbols 0..9 (repmeter's fibonacci/thue-morse/random-binary
    generators) are rendered as digits, which is what makes a binary witness
    readable as e.g. 0110.
    """
    if factor and all(0 <= c <= 9 for c in factor):
        return "".join(str(c) for c in factor)
    bs = bytes(c for c in factor if 0 <= c < 256)
    if len(bs) != len(factor):
        return str(list(factor))
    try:
        s = bs.decode("ascii")
    except UnicodeDecodeError:
        return str(list(factor))
    return s if s.isprintable() else str(list(factor))


