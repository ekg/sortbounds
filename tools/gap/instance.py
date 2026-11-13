"""instance.py -- the attractor as a set-cover instance, in three universes.

DEFINITIONS (the ones tools/attractor uses, restated so this file stands alone; S is a
text of length n over an integer alphabet, positions are 0..n-1):

  factor      a contiguous substring S[i:i+L], L >= 1;
  C(f)        the set of positions p that some occurrence [i, i+L) of f covers,
              i.e. {p : exists i, S[i:i+L] = f and i <= p < i+L};
  attractor   a set Gamma of positions with union_{p in Gamma} C^{-1}(p) = all
              distinct nonempty factors of S;
  gamma       the smallest |Gamma|.

The set-cover instance with universe = factors and set_p = {f : p in C(f)} has
optimum gamma (definition).  This module builds three universe choices, all of which
have the SAME integer optimum and (as verified in check.py) the same LP optimum:

  universe "nodes"      the suffix-tree nodes of S (<= 2n-1 elements): a node's element
                        is its shortest factor.  Built on tools/attractor's Instance.
  universe "factors"    every distinct nonempty factor (<= n(n+1)/2 elements), built by
                        brute force from the text with no suffix tree at all.  This is
                        the definition-level universe and is the one used to check the
                        node reduction; it is O(n^2) elements so it is only used at
                        small n.
  universe "factors_k"  every distinct factor of length exactly k ("single-k"), and
                        "factors_le_k" every distinct factor of length <= k.

WHY THE NODE UNIVERSE GIVES THE SAME OPTIMUM.  Two factors owned by one suffix-tree
node share their occurrence set (that is what a node is), and a longer window at a
fixed start contains the shorter one; hence C(f) is a SUPERSET of C(shortest factor
of the node) for every f in the node.  A set-cover constraint for a superset C-set is
implied by the constraint for the subset, so dropping all non-shortest factors leaves
the optimum of the *integer* program AND of the *LP relaxation* unchanged.  That
argument is tools/attractor's (R1); it is quoted here rather than re-derived, and
check.py measures both optima on every small text so that a wrong argument could not
hide.

NO FLOATING POINT, NO UNVERIFIED NUMBER.  `Cover.exact_min_cover` returns a position
set it has verified against every row; `Cover.lp` returns simplex's certified pair
(see simplex.py); `Instance.delta` is an exact Fraction.
"""

import importlib.util
import os
import sys
from bisect import bisect_left
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
_ATTRACTOR = os.path.normpath(os.path.join(_HERE, os.pardir, "attractor"))
_REPMETER = os.path.normpath(os.path.join(_HERE, os.pardir, "repmeter"))
for _p in (_ATTRACTOR, _REPMETER):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import simplex                                            # noqa: E402


class BudgetExhausted(RuntimeError):
    """An exact search hit its node cap: nothing is known, so no number is reported."""


def _load_module(path, name):
    """Load a .py file under its own module name, bypassing sys.path.

    tools/attractor/instance.py and this file are both called `instance`, so a plain
    `import instance` would resolve to whichever directory came first -- and
    attractor's own modules do `import instance` unqualified.  Loading it under the
    alias `attractor_instance` keeps the two apart while still reusing the tested code.
    """
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


_ATTR = _load_module(os.path.join(_ATTRACTOR, "instance.py"), "attractor_instance")
Instance = _ATTR.Instance
factor_str = _ATTR.factor_str
normalize_text = _ATTR.normalize_text


class Cover:
    """A set-cover instance: n positions, elements with their covering position sets.

    labels[e] is a human-readable name for element e (the factor, as text); rows[e] is
    the tuple of positions p with p in C(factor_e).
    """

    __slots__ = ("n", "labels", "rows", "universe")

    def __init__(self, n, labels, rows, universe):
        if len(labels) != len(rows):
            raise ValueError("%d labels for %d elements" % (len(labels), len(rows)))
        self.n = n
        self.labels = list(labels)
        self.rows = [tuple(sorted(set(r))) for r in rows]
        self.universe = universe

    # -- basic queries ------------------------------------------------------

    def __len__(self):
        return len(self.rows)

    def __repr__(self):
        return "Cover(%s, n=%d, elements=%d)" % (self.universe, self.n, len(self.rows))

    def verify_cover(self, gamma):
        """True iff every element is hit by some position of gamma."""
        pts = set(gamma)
        for p in pts:
            if not 0 <= p < self.n:
                raise ValueError("position %r outside 0..%d" % (p, self.n - 1))
        return all(any(p in pts for p in row) for row in self.rows)

    def uncovered(self, gamma):
        """The labels of the elements no position of gamma covers."""
        pts = set(gamma)
        return [self.labels[e] for e, row in enumerate(self.rows)
                if not any(p in pts for p in row)]

    def minimal_rows(self):
        """Drop rows that contain another row: their constraint is implied.

        Returns a list of (label, row) with pairwise distinct inclusion-minimal rows.
        Valid for the set-cover problem (any hit set for the subset is a hit set for
        the superset) and for the covering LP (same implication, coefficient 1), so it
        is only ever used to make the exact search and the tableau smaller; the answer
        is re-checked against `self.rows`.
        """
        uniq = sorted({row for row in self.rows}, key=lambda r: (len(r), r))
        keep = []
        for row in uniq:
            rs = set(row)
            if not any(set(k) <= rs for k in keep):
                keep.append(row)
        return keep

    # -- exact integer optimum ---------------------------------------------

    def exact_min_cover(self, node_cap=4000000):
        """(k, gamma): the smallest hitting set, verified.  Exact, by branch and bound.

        Standard minimum-set-cover branch and bound (branch on the uncovered element
        with the fewest remaining candidate positions).  It is exhaustive, so the value
        is the true optimum; the returned position set is then re-checked against EVERY
        row of the instance, so an unreported bug in the search can only be caught, not
        propagated.  Raises RuntimeError if the node cap is hit (never returns a bound).
        """
        k, gamma, _ = self._search(node_cap)
        if not self.verify_cover(gamma):
            raise AssertionError("exact_min_cover produced a non-cover %r" % (gamma,))
        if len(set(gamma)) != k:
            raise AssertionError("exact_min_cover size %d but %d positions" % (k, len(set(gamma))))
        return k, tuple(sorted(gamma))

    def _search(self, node_cap):
        m = len(self.rows)
        masks = [0] * m
        for e, row in enumerate(self.rows):
            if not row:
                raise ValueError("element %d has no covering position" % e)
            for p in row:
                masks[e] |= 1 << p
        mins = sorted({m_ for m_ in masks}, key=lambda x: (bin(x).count("1"), x))
        keep = []
        for r in mins:
            if not any(k & r == k for k in keep):
                keep.append(r)
        keep.sort(key=lambda x: (bin(x).count("1"), x))

        # greedy upper bound (max coverage on the minimal rows, then prune)
        chosen = 0
        while True:
            unc = [r for r in keep if not (r & chosen)]
            if not unc:
                break
            best_p, best_gain = -1, -1
            for r in unc:
                avail = r & ~chosen
                while avail:
                    b = avail & -avail
                    avail ^= b
                    gain = sum(1 for r2 in unc if r2 & b)
                    assert gain >= 1
                    if gain > best_gain:
                        best_gain = gain
                        best_p = b.bit_length() - 1
            chosen |= 1 << best_p
        best = [bin(chosen).count("1"), chosen]

        # rowmask[p] = the minimal rows that contain position p
        rowmask = [0] * self.n
        for i, r in enumerate(keep):
            avail = r
            while avail:
                b = avail & -avail
                avail ^= b
                rowmask[b.bit_length() - 1] |= 1 << i
        all_rows = (1 << len(keep)) - 1
        nodes = [0]

        def rec(chosen_pos, hit, k):
            nodes[0] += 1
            if nodes[0] > node_cap:
                raise BudgetExhausted("exact_min_cover hit its node cap (%d)"
                                      % node_cap)
            if hit == all_rows:
                if k < best[0]:
                    best[0] = k
                    best[1] = chosen_pos
                return
            if k + 1 >= best[0]:
                return
            # lower bound: a maximal family of pairwise disjoint uncovered rows needs one
            # position each, all outside the chosen ones -- so it is a valid bound
            used = chosen_pos
            pack = 0
            for i, r in enumerate(keep):
                if (hit >> i) & 1 or (r & used):
                    continue
                pack += 1
                used |= r
            if k + pack >= best[0]:
                return
            # branch on the uncovered row with the fewest positions still available
            pick = -1
            pick_avail = 0
            for i, r in enumerate(keep):
                if (hit >> i) & 1:
                    continue
                avail = r & ~chosen_pos
                assert avail != 0, "uncovered row with no free position"
                if pick < 0 or bin(avail).count("1") < bin(pick_avail).count("1"):
                    pick, pick_avail = i, avail
                    if bin(avail).count("1") == 1:
                        break
            assert pick >= 0
            cand = pick_avail
            while cand:
                b = cand & -cand
                cand ^= b
                rec(chosen_pos | b, hit | rowmask[b.bit_length() - 1], k + 1)

        rec(0, 0, 0)
        gamma = [p for p in range(self.n) if (best[1] >> p) & 1]
        return best[0], gamma, nodes[0]

    # -- the LP relaxation --------------------------------------------------

    def lp(self, pivot_cap=simplex.PIVOT_CAP, deadline=None):
        """LP* of min sum x_p s.t. every element covered, x >= 0.  Certified."""
        return simplex.cover_lp(self.rows, self.n, pivot_cap=pivot_cap, deadline=deadline)

    def lp_primal(self, pivot_cap=simplex.PIVOT_CAP, deadline=None):
        """LP* by two-phase simplex on the primal -- the independent cross-check."""
        return simplex.cover_lp_primal(self.rows, self.n, pivot_cap=pivot_cap,
                                       deadline=deadline)

    def gap(self, pivot_cap=simplex.PIVOT_CAP, deadline=None):
        """(gamma, LP*, gap = gamma / LP*) as exact Fractions.  LP* > 0 always."""
        gamma, _ = self.exact_min_cover()
        lp = self.lp(pivot_cap=pivot_cap, deadline=deadline)
        if lp.value <= 0:
            raise AssertionError("LP* = %s is not positive on a nonempty instance" % (lp.value,))
        return Fraction(gamma), lp.value, Fraction(gamma) / lp.value


class TextInstance:
    """One text: its symbol list, its suffix-tree node cover, and delta."""

    __slots__ = ("sym", "n", "inst", "nodes")

    def __init__(self, text):
        self.sym = normalize_text(text)
        self.n = len(self.sym)
        self.inst = Instance(self.sym) if self.n else None
        self.nodes = self._node_cover() if self.n else Cover(0, [], [], "nodes")

    def _node_cover(self):
        inst = self.inst
        coverers = inst.coverers()
        labels = [factor_str(self.sym, inst.node_factor(v))
                  for v in range(len(inst.nodes))]
        return Cover(self.n, labels, [coverers[v] for v in range(len(inst.nodes))],
                     "nodes")

    def delta(self):
        """delta = max_k d_k / k exactly (KNP: delta <= gamma).  0 for the empty text."""
        return self.inst.delta() if self.n else Fraction(0)

    def dk(self, k):
        """d_k = number of distinct factors of length k (0 outside 1..n)."""
        if not self.n or not isinstance(k, int) or k < 1 or k > self.n:
            return 0
        return self.inst.d_profile[k]

    def lp_lower_bound(self, universe, k=None):
        """The LP* lower bound the d_j/j counting argument gives for this universe.

        Summing the covering constraints of the distinct length-j factors gives
        d_j <= sum_p x_p * #{f : |f| = j, p crosses f} <= j * sum_p x_p, since a position
        crosses at most j windows of length j.  So LP* >= d_j/j for every j whose
        factors are all in the universe.  Hence LP* >= delta for the full universe,
        LP* >= d_k/k for the single-k universe, LP* >= max_{j<=k} d_j/j for the
        length-<=k universe.  (MY-INFERENCE: weak duality plus counting; checked as an
        exact Fraction on every instance measured.)
        """
        if universe in ("nodes", "factors"):
            return self.delta()
        if universe.startswith("factors_le_"):
            return max((Fraction(self.dk(j), j) for j in range(1, (k or 0) + 1)),
                       default=Fraction(0))
        if universe.startswith("factors_"):
            return Fraction(self.dk(k), k) if k else Fraction(0)
        raise ValueError("unknown universe %r" % (universe,))

    def node_factor_verify(self, gamma):
        """tools/attractor's independent definition-level check of a position set."""
        return self.inst.verify(gamma)

    def verify_factor_cover(self, gamma, lo=1, hi=None):
        """Definition-level check for a length range: (factor, start) or None.

        Enumerates EVERY window of length lo..hi, groups the windows by the factor they
        spell (so each distinct factor is tested once), and asks whether some position
        of gamma lies inside one of that factor's occurrence intervals, with an explicit
        binary search.  It shares no bookkeeping with Cover, with the suffix tree, or
        with the exact search: this is the definition, run directly.
        """
        pts = sorted(set(gamma))
        for p in pts:
            if not 0 <= p < self.n:
                raise ValueError("position %r outside 0..%d" % (p, self.n - 1))
        hi = self.n if hi is None else min(hi, self.n)
        occ = {}
        for length in range(max(1, lo), hi + 1):
            for i in range(0, self.n - length + 1):
                occ.setdefault(tuple(self.sym[i:i + length]), []).append((i, length))
        for f, starts in occ.items():
            hit = False
            for (i, length) in starts:
                j = bisect_left(pts, i)
                if j < len(pts) and pts[j] < i + length:
                    hit = True
                    break
            if not hit:
                return (f, starts[0][0])
        return None

    def cover(self, universe, k=None):
        """One of the universes above, as a Cover."""
        if universe == "nodes":
            return self.nodes
        if universe == "factors":
            return self._factor_cover(None, None)
        if universe == "factors_k":
            if not isinstance(k, int) or k < 1:
                raise ValueError("factors_k needs a positive integer k")
            return self._factor_cover(k, k)
        if universe == "factors_le_k":
            if not isinstance(k, int) or k < 1:
                raise ValueError("factors_le_k needs a positive integer k")
            return self._factor_cover(1, k)
        raise ValueError("unknown universe %r" % (universe,))

    def _factor_cover(self, lo, hi):
        """The definition-level instance: enumerate every window, no suffix tree.

        For the window [i, i+L) the positions covered are exactly i..i+L-1, so C(f) is
        the union of those ranges over the occurrences of f.  Elements are keyed by the
        factor itself (a tuple of symbols); lo/hi restrict the lengths.
        """
        sym, n = self.sym, self.n
        if lo is None:
            lo, hi = 1, n
        else:
            lo, hi = max(1, lo), min(hi, n)
        pos_sets = {}
        for L in range(lo, hi + 1):
            for i in range(0, n - L + 1):
                f = tuple(sym[i:i + L])
                pos_sets.setdefault(f, set()).update(range(i, i + L))
        labels = [factor_str(sym, list(f)) for f in pos_sets]
        rows = [sorted(pos_sets[f]) for f in pos_sets]
        name = "factors" if (lo, hi) == (1, n) else (
            "factors_%d" % lo if lo == hi else "factors_le_%d" % hi)
        return Cover(n, labels, rows, name)


def binary_strings(max_len, min_len=1):
    """All binary texts of length min_len..max_len (as lists of ints)."""
    import itertools
    for length in range(min_len, max_len + 1):
        for bits in itertools.product((0, 1), repeat=length):
            yield list(bits)


def ternary_strings(max_len, min_len=1):
    import itertools
    for length in range(min_len, max_len + 1):
        for bits in itertools.product((0, 1, 2), repeat=length):
            yield list(bits)


def text_str(sym):
    """A text as the digit string the attractor README prints (0..9 -> digits)."""
    return "".join(str(c) for c in sym)


if __name__ == "__main__":                      # pragma: no cover - manual probe
    import time
    for name in ["abracadabra", "mississippi"]:
        t0 = time.time()
        ti = TextInstance(name)
        for universe, k in [("nodes", None), ("factors", None), ("factors_k", 1),
                            ("factors_k", 2), ("factors_le_k", 2)]:
            cov = ti.cover(universe, k)
            g, lp, gap = cov.gap()
            print("%-12s %-14s n=%d elems=%d gamma=%s LP*=%s gap=%s (%.2fs)"
                  % (name, cov.universe, ti.n, len(cov), g, lp, gap, time.time() - t0))
