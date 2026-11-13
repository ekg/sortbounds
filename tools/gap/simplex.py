"""simplex.py -- exact rational LP for the minimum-attractor set-cover instance.

THE PAIR OF LINEAR PROGRAMS.  A set-cover instance is a list of elements e, each with
the set rows[e] of *positions* that can cover it, and n positions in total:

    (P)  min  sum_p x_p   s.t.  sum_{p in rows[e]} x_p >= 1  for every element e,
                              x >= 0
    (D)  max  sum_e y_e   s.t.  sum_{e : p in rows[e]} y_e <= 1  for every position p,
                              y >= 0

LP* = opt(P) = opt(D).  That equality is strong duality; the inequality used as the
certificate is weak duality: for any primal-feasible x and any dual-feasible y,
sum(y) <= LP* <= sum(x) (Chvatal, *Linear Programming*, 1983, Thm 5.1; Gale's 1951
theorem for the equality).  Both are quoted, not re-proved.

WHAT THIS MODULE PROMISES.  `cover_lp` never returns a number it has not certified:

  * a feasible dual y is produced by the simplex;
  * a candidate primal x is produced from the dual tableau (the shadow prices: the
    reduced cost of the slack column of dual constraint p is -x_p);
  * then BOTH are re-checked against the instance: every dual constraint <= 1, every
    primal row >= 1, and sum(x) == sum(y).

Feasibility on both sides plus equality of objectives *is* a proof that LP* = sum(y),
by weak duality alone -- so the reported value cannot be wrong even if the
pivot rule is.  A pivot rule can only fail to find the optimum, and that failure
shows up here as a certificate that does not pass, which raises LPCertificateError
rather than returning a number.  `cover_lp_primal` independently solves (P) by
two-phase simplex and check.py requires the two values to agree.

Only exact rational arithmetic is used (`fractions.Fraction`); there is no float
anywhere in this file, so no bound here depends on a floating-point comparison.

Tableau conventions, in one place, because getting them wrong is invisible:
the tableau has one row per constraint, one column per variable, one column per
slack, and a trailing right-hand-side column; the last row is the objective row,
whose entry j is the reduced cost d_j = c_j - z_j and whose last entry is
NEGATIVE the current objective value.  A pivot on (r, c) divides row r by T[r][c]
and subtracts T[i][c] * row_r from every other row including the objective row;
that preserves both invariants.  For a maximisation one enters a column with
d_c > 0, for a minimisation one with d_c < 0, and one leaves on the minimum ratio
T[i][rhs] / T[i][c] over T[i][c] > 0.
"""

import sys
import time
from fractions import Fraction

PIVOT_CAP = 200000


class LPError(RuntimeError):
    """A linear program was unbounded, infeasible, or its pivot cap was hit."""


class LPTimeout(LPError):
    """The LP solve passed its wall-clock deadline before reaching the optimum."""


class LPCertificateError(RuntimeError):
    """The primal/dual pair produced by the simplex failed to check out."""


# --------------------------------------------------------------------------
# the raw simplex
# --------------------------------------------------------------------------


def _objective_row(T, basis, cost, ncols):
    """The invariant objective row for the current basis, recomputed from scratch."""
    row = [Fraction(cost[j]) if j < len(cost) else Fraction(0) for j in range(ncols)]
    row.append(Fraction(0))
    for i, bv in enumerate(basis):
        cb = cost[bv] if bv < len(cost) else 0
        if cb:
            Ti = T[i]
            row = [row[j] - cb * Ti[j] for j in range(ncols + 1)]
    return row


def _pivot(T, basis, r, c, ncols, m):
    piv = T[r][c]
    if piv == 0:
        raise LPError("pivot on a zero entry")
    Tr = [v / piv for v in T[r]]
    T[r] = Tr
    for i in range(m + 1):
        if i == r:
            continue
        f = T[i][c]
        if f:
            Ti = T[i]
            T[i] = [Ti[j] - f * Tr[j] for j in range(ncols + 1)]
    basis[r] = c


def _simplex(T, basis, ncols, m, maximize, bland_after=None, pivot_cap=PIVOT_CAP,
             deadline=None):
    """Run the simplex to optimality in place.  Returns the number of pivots.

    Entering rule: Dantzig (most extreme reduced cost) for the first `bland_after`
    pivots, then Bland's rule (smallest eligible index), which is finite -- cycling is
    impossible under Bland's rule in exact arithmetic (Bland 1977).  The Dantzig prefix
    is only a speed measure, so a wrongly-tuned prefix cannot change the answer that is
    returned, only the time; and every returned answer is re-checked by the caller.
    """
    if bland_after is None:
        bland_after = 4 * (ncols + m) + 100
    pivots = 0
    while True:
        if deadline is not None and not pivots % 8 and time.monotonic() > deadline:
            raise LPTimeout("deadline passed after %d pivots" % pivots)
        obj = T[m]
        enter = -1
        if pivots < bland_after:
            best = Fraction(0)
            for j in range(ncols):
                d = obj[j]
                if (d > best) if maximize else (d < best):
                    best = d
                    enter = j
            if maximize and best == 0:
                enter = -1
        else:
            for j in range(ncols):
                if (obj[j] > 0) if maximize else (obj[j] < 0):
                    enter = j
                    break
        if enter < 0:
            return pivots
        leave = -1
        ratio = None
        for i in range(m):
            a = T[i][enter]
            if a > 0:
                q = T[i][ncols] / a
                if ratio is None or q < ratio or (q == ratio and basis[i] < basis[leave]):
                    ratio = q
                    leave = i
        if leave < 0:
            raise LPError("unbounded linear program")
        _pivot(T, basis, leave, enter, ncols, m)
        pivots += 1
        if pivots > pivot_cap:
            raise LPError("pivot cap %d exceeded" % pivot_cap)


def max_le(A, b, c, pivot_cap=PIVOT_CAP, deadline=None):
    """max c.x  s.t.  A x <= b, x >= 0, with every b_i >= 0.

    Returns (x, value, pivots, shadow).  The all-slack basis is feasible exactly because
    b >= 0, so no phase 1 is needed.  `shadow[i]` is the reduced cost of the slack of
    row i with its sign flipped; that is the objective's sensitivity to b_i, i.e. the
    solution of the dual linear program at its optimum (Chvatal 1983, Thm 5.3).  The
    tableau column order is x first then slacks, which is what makes the slacks
    addressable as column nv + i.
    """
    m = len(A)
    nv = len(c)
    if len(b) != m:
        raise ValueError("A has %d rows but b has %d entries" % (m, len(b)))
    for i in range(m):
        if b[i] < 0:
            raise ValueError("max_le needs b >= 0; row %d has %r" % (i, b[i]))
        if len(A[i]) != nv:
            raise ValueError("row %d has %d entries, expected %d" % (i, len(A[i]), nv))
    ncols = nv + m
    T = []
    for i in range(m):
        row = [Fraction(v) for v in A[i]] + [Fraction(0)] * m + [Fraction(b[i])]
        row[nv + i] = Fraction(1)
        T.append(row)
    basis = [nv + i for i in range(m)]
    T.append(_objective_row(T, basis, [Fraction(v) for v in c], ncols))
    pivots = _simplex(T, basis, ncols, m, maximize=True, pivot_cap=pivot_cap,
                      deadline=deadline)
    x = [Fraction(0)] * nv
    for i in range(m):
        if basis[i] < nv:
            x[basis[i]] = T[i][ncols]
    shadow = [-T[m][nv + i] for i in range(m)]
    return x, -T[m][ncols], pivots, shadow


def min_ge(A, b, c, pivot_cap=PIVOT_CAP, deadline=None):
    """min c.x  s.t.  A x >= b, x >= 0, for any sign of b.  Two-phase simplex.

    Returns (x, value, pivots).  Every row gets a surplus (sign -1) and an artificial
    (sign +1) column; phase 1 minimises the sum of the artificials, phase 2 the real
    cost.  Rows whose right-hand side is negative are negated first, which flips the
    row to a `<=` row -- such a row gets a slack (+1) and no surplus, but still an
    artificial, so that one code path covers both senses.
    """
    m = len(A)
    nv = len(c)
    if len(b) != m:
        raise ValueError("A has %d rows but b has %d entries" % (m, len(b)))
    rows = []
    for i in range(m):
        a = [Fraction(v) for v in A[i]]
        rhs = Fraction(b[i])
        if len(a) != nv:
            raise ValueError("row %d has %d entries, expected %d" % (i, len(a), nv))
        if rhs < 0:
            a = [-v for v in a]
            rhs = -rhs
            rows.append((a, rhs, 1))      # slack sense: <=
        else:
            rows.append((a, rhs, -1))     # surplus sense: >=
    nsur = m
    nart = m
    ncols = nv + nsur + nart
    T = []
    for i, (a, rhs, sign) in enumerate(rows):
        row = a + [Fraction(0)] * (nsur + nart) + [rhs]
        row[nv + i] = Fraction(sign)
        row[nv + nsur + i] = Fraction(1)
        T.append(row)
    basis = [nv + nsur + i for i in range(m)]
    cost1 = [Fraction(0)] * (nv + nsur) + [Fraction(1)] * nart
    T.append(_objective_row(T, basis, cost1, ncols))
    _simplex(T, basis, ncols, m, maximize=False, pivot_cap=pivot_cap, deadline=deadline)
    if -T[m][ncols] > 0:
        raise LPError("infeasible linear program (phase 1 optimum %s)"
                      % (-T[m][ncols],))
    # drop the artificial columns: pivot any artificial that stayed basic out of the
    # basis (it has value 0), else the row is redundant and is deleted
    keep_rows = []
    for i in range(m):
        if basis[i] >= nv + nsur:
            hit = -1
            for j in range(nv + nsur):
                if T[i][j] != 0:
                    hit = j
                    break
            if hit < 0:
                continue                   # redundant row: value 0 = 0
            _pivot(T, basis, i, hit, ncols, m)
        keep_rows.append(i)
    T2 = []
    basis2 = []
    for i in keep_rows:
        T2.append(T[i][:nv + nsur] + [T[i][ncols]])
        basis2.append(basis[i])
    m2 = len(T2)
    T2.append(_objective_row(T2, basis2, [Fraction(v) for v in c] + [Fraction(0)] * nsur,
                             nv + nsur))
    ncols2 = nv + nsur
    _simplex(T2, basis2, ncols2, m2, maximize=False, pivot_cap=pivot_cap,
             deadline=deadline)
    x = [Fraction(0)] * nv
    for i in range(m2):
        if basis2[i] < nv:
            x[basis2[i]] = T2[i][ncols2]
    return x, -T2[m2][ncols2], None


# --------------------------------------------------------------------------
# the set-cover LP
# --------------------------------------------------------------------------


def check_primal(rows, n, x):
    """Is x a feasible solution of (P)?  Returns a human-readable reason or None."""
    if len(x) != n:
        return "x has %d entries, %d positions" % (len(x), n)
    for p in range(n):
        if x[p] < 0:
            return "x[%d] = %s < 0" % (p, x[p])
    for e, row in enumerate(rows):
        if not row:
            return "element %d has no covering position" % e
        s = sum((x[p] for p in row), Fraction(0))
        if s < 1:
            return "element %d is covered with weight %s < 1" % (e, s)
    return None


def check_dual(rows, n, y):
    """Is y a feasible solution of (D)?  Returns a reason or None."""
    if len(y) != len(rows):
        return "y has %d entries, %d elements" % (len(y), len(rows))
    for e in range(len(rows)):
        if y[e] < 0:
            return "y[%d] = %s < 0" % (e, y[e])
    load = [Fraction(0)] * n
    for e, row in enumerate(rows):
        if y[e]:
            for p in row:
                load[p] += y[e]
    for p in range(n):
        if load[p] > 1:
            return "position %d is loaded to %s > 1" % (p, load[p])
    return None


class LPOptimum:
    """A certified LP optimum: value, primal x, dual y, and the pivot count."""

    __slots__ = ("value", "x", "y", "pivots")

    def __init__(self, value, x, y, pivots):
        self.value = value
        self.x = x
        self.y = y
        self.pivots = pivots

    def __repr__(self):
        return "LPOptimum(%s, pivots=%s)" % (self.value, self.pivots)


def cover_lp(rows, n, pivot_cap=PIVOT_CAP, deadline=None):
    """LP* of the covering LP (P) for `rows`, certified on both sides.

    `rows[e]` is the iterable of positions that cover element e; there are n positions.
    Returns an LPOptimum, or raises LPCertificateError if the primal and dual
    solutions do not close.  An empty instance has LP* = 0.
    """
    rows = [tuple(sorted(set(r))) for r in rows]
    for e, row in enumerate(rows):
        for p in row:
            if not 0 <= p < n:
                raise ValueError("element %d is covered by %d, outside 0..%d"
                                 % (e, p, n - 1))
    if not rows:
        return LPOptimum(Fraction(0), [Fraction(0)] * n, [], 0)
    m = len(rows)
    # (D) has one constraint per position: sum over elements covering p of y_e <= 1
    A = [[0] * m for _ in range(n)]
    for e, row in enumerate(rows):
        for p in row:
            A[p][e] = 1
    y, value, pivots, x = max_le(A, [1] * n, [1] * m, pivot_cap=pivot_cap,
                                 deadline=deadline)
    bad = check_dual(rows, n, y)
    if bad is not None:
        raise LPCertificateError("dual solution rejected: " + bad)
    # `max_le` returns the primal solution of (P) as the shadow prices of (D)
    bad = check_primal(rows, n, x)
    if bad is not None:
        raise LPCertificateError("recovered primal solution rejected: " + bad)
    if sum(y, Fraction(0)) != value:
        raise LPCertificateError(
            "dual objective does not match the reported value: %s vs %s"
            % (sum(y, Fraction(0)), value))
    if sum(x, Fraction(0)) != value:
        raise LPCertificateError(
            "primal and dual objectives differ: %s vs %s" % (sum(x, Fraction(0)), value))
    return LPOptimum(value, x, y, pivots)


def cover_lp_primal(rows, n, pivot_cap=PIVOT_CAP, deadline=None):
    """LP* of (P) by two-phase simplex on (P) itself -- an independent route.

    Used by check.py to confirm `cover_lp`'s tableau-shadow-price route; it shares the
    pivot code but not the formulation, the starting basis, or the primal read-off.
    """
    rows = [tuple(sorted(set(r))) for r in rows]
    if not rows:
        return Fraction(0)
    m = len(rows)
    A = [[0] * n for _ in range(m)]
    for e, row in enumerate(rows):
        for p in row:
            A[e][p] = 1
    x, value, _ = min_ge(A, [1] * m, [1] * n, pivot_cap=pivot_cap, deadline=deadline)
    bad = check_primal(rows, n, x)
    if bad is not None:
        raise LPCertificateError("primal simplex solution rejected: " + bad)
    return value


if __name__ == "__main__":                      # pragma: no cover - manual probe
    a, v, _, s = max_le([[1, 1], [1, 0]], [2, 1], [3, 2])
    print("max_le 3x+2y s.t. x+y<=2, x<=1 ->", v, [str(t) for t in a], "shadow",
          [str(t) for t in s])
    sys.exit(0)
