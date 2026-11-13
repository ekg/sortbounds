"""certify.py -- an INDEPENDENT re-verification of a gap certificate, at the definition level.

WHAT A CERTIFICATE IS.  For a text S, a claim "gamma(S) = g and LP*(S) = v" is proved by
three objects, none of which needs the solver that produced them to be correct:

  (i)   a position set Gamma with |Gamma| = g that intersects C(f) for EVERY distinct factor f
        (so gamma <= g, by exhibiting a cover of size g); and the matching lower bound
        gamma >= g is a separate exact computation (branch and bound) -- the certificate
        here only re-checks the upper half, plus re-checks g against the search;
  (ii)  a vector x >= 0 over positions with sum(rows[f] . x) >= 1 for every factor f and
        sum(x) = v  (so LP* <= v, by exhibiting a feasible primal of value v);
  (iii) a vector y >= 0 over factors with sum_{f : p in C(f)} y_f <= 1 for every position p
        and sum(y) = v  (so LP* >= v, by exhibiting a feasible dual of value v).

(ii) and (iii) together are `LP* = v` by weak duality alone: for feasible x, y,
sum(y) <= LP* <= sum(x).  Nothing here uses strong duality, the simplex, the suffix tree or
the node reduction.  The constraints are rebuilt from the DEFINITION: every window
S[i:i+L] is enumerated, the windows spelling the same factor are grouped, and C(f) is the
union of their intervals.  So a certificate that closes here also certifies the LP optimum
of the definition-level (n(n+1)/2-element) instance, which is stronger than the node
instance that the solver actually solved.

WHY THE DEFINITION-LEVEL CHECK IS THE RIGHT ONE.  The solver works in the node universe
(<= 2n-1 elements, one per suffix-tree node).  Re-checking x against *all* factors is
strictly harder than re-checking it against the nodes, so a pass here implies a pass
there.  Conversely, the dual y is supported on the node factors only; since dual
feasibility is a per-position load bound and factors carried with y_f = 0 add nothing to a
load, the same y is dual-feasible for the definition-level instance.  Hence the pair closes
at both levels, and the two LP optima are equal -- which is exactly the node reduction the
whole measurement rests on, verified per instance rather than assumed.

Also here: `check_gamma`, which re-checks a claimed minimum attractor two ways -- that the
set covers every factor (definition, by explicit interval/binary-search test) and that no
set of g-1 positions does (exhaustive enumeration over all (g-1)-subsets of positions, only
attempted when C(n, g-1) is small enough that the enumeration is honest about being
exhaustive).

No floating point anywhere in this file.
"""

from fractions import Fraction
from itertools import combinations

from instance import TextInstance, text_str


class CertificateError(RuntimeError):
    """A claimed gap certificate failed to re-verify: nothing may be reported."""


def definition_rows(ti):
    """label -> tuple of positions p whose window contains an occurrence of that factor.

    This is C(f) straight from the definition, with no suffix tree involved:
    instance.TextInstance._factor_cover enumerates every window of every length and unions
    the intervals of the windows that spell the same factor.
    """
    cov = ti.cover("factors")
    rows = {}
    for label, row in zip(cov.labels, cov.rows):
        if label in rows:
            raise CertificateError("the definition produced the factor %r twice" % (label,))
        rows[label] = tuple(row)
    return rows


def check_primal(rows, n, x):
    """(ok, min_slack, worst_label, offenders).  Direct summation over every factor row."""
    if len(x) != n:
        raise CertificateError("x has %d entries for %d positions" % (len(x), n))
    for p, v in enumerate(x):
        if v < 0:
            raise CertificateError("x[%d] = %s < 0: not a primal-feasible vector" % (p, v))
    worst = None
    worst_label = None
    offenders = []
    for label in sorted(rows):
        row = rows[label]
        s = sum((x[p] for p in row), Fraction(0))
        if worst is None or s < worst:
            worst, worst_label = s, label
        if s < 1:
            offenders.append((label, s))
    return (not offenders), worst, worst_label, offenders


def check_dual(rows, n, y):
    """(ok, max_load, worst_p, offenders).  Per-position loads, by direct summation."""
    for label, v in y.items():
        if v < 0:
            raise CertificateError("y[%r] = %s < 0: not a dual-feasible vector" % (label, v))
        if label not in rows:
            raise CertificateError("y is supported on %r, which is not a factor of S" % (label,))
    load = [Fraction(0)] * n
    for label in sorted(rows):
        v = y.get(label, Fraction(0))
        if v:
            for p in rows[label]:
                load[p] += v
    worst = max(load) if load else Fraction(0)
    worst_p = load.index(worst) if load else None
    offenders = [(p, l) for p, l in enumerate(load) if l > 1]
    return (not offenders), worst, worst_p, offenders


def check_gamma(ti, positions, exhaustive_upto=6, choose_cap=200000):
    """(ok, lines): re-check an attractor, by the definition and by exhaustive search.

    The covering half is the definition, run directly.  The minimality half is an
    enumeration of every (g-1)-subset of positions -- exhaustive, so it proves
    gamma >= g -- but only when C(n, g-1) <= choose_cap, which is reported either way so
    that "not attempted" can never be mistaken for "checked".
    """
    from math import comb
    lines = []
    g = len(set(positions))
    miss = ti.verify_factor_cover(positions)
    if miss is not None:
        raise CertificateError("Gamma = %r misses the factor %r at position %d"
                               % (positions, miss[0], miss[1]))
    nfac = len(ti.cover("factors"))
    lines.append("Gamma = %s covers all %d distinct factors of S (definition-level check)"
                 % (list(positions), nfac))
    attempted = False
    if g >= 1:
        trials = comb(ti.n, g - 1) if g - 1 <= ti.n else 0
        if trials <= choose_cap and g - 1 >= 0:
            attempted = True
            for sub in combinations(range(ti.n), g - 1):
                if ti.verify_factor_cover(list(sub)) is None:
                    raise CertificateError(
                        "gamma < %d: the %d positions %r also cover every factor"
                        % (g, g - 1, sub))
            lines.append("no set of %d positions covers every factor: all %d (g-1)-subsets "
                         "of the %d positions tested (exhaustive)" % (g - 1, trials, ti.n))
    if not attempted:
        lines.append("minimality NOT re-checked here: C(%d, %d) subsets is over the cap "
                     "(the exact branch and bound supplies it)" % (ti.n, g - 1))
    return lines


def certify(text, gamma_positions, x, y, claimed_value, rooted=True):
    """Re-verify (gamma, LP*) of one text from scratch; returns (facts, lines).

    `x` is indexed by position; `y` maps a factor LABEL (as instance.factor_str prints it)
    to its dual weight.  Raises CertificateError on any failure, so a returned report is a
    checked statement.
    """
    if isinstance(text, str):
        ti = TextInstance([int(c) for c in text])
    else:
        ti = TextInstance(list(text))
    txt = text_str(ti.sym)
    if rooted:
        rows = definition_rows(ti)
    else:                                   # pragma: no cover - not used
        cov = ti.nodes
        rows = dict(zip(cov.labels, cov.rows))
    n = ti.n

    lines = []
    lines.append("text `%s` (n = %d, alphabet size %d)" % (txt, n, len(set(ti.sym))))

    # (i) the attractor
    lines.extend(check_gamma(ti, gamma_positions))

    # (ii) the primal
    okp, min_slack, worst_label, offenders = check_primal(rows, n, x)
    if not okp:
        raise CertificateError("primal x does not cover %d factor(s), worst %r at %s"
                               % (len(offenders), worst_label, dict(offenders[:5])))
    sum_x = sum(x, Fraction(0))
    # (iii) the dual
    okd, max_load, worst_p, dload = check_dual(rows, n, y)
    if not okd:
        raise CertificateError("dual y overloads %d position(s), worst %d at %s"
                               % (len(dload), worst_p, dict(dload[:5])))
    sum_y = sum(y.values(), Fraction(0))
    if sum_x != sum_y:
        raise CertificateError("sum(x) = %s but sum(y) = %s: weak duality does not close "
                               "the pair" % (sum_x, sum_y))
    if sum_x != Fraction(claimed_value):
        raise CertificateError("the pair's value is %s but %s was claimed"
                               % (sum_x, claimed_value))
    lines.append("primal x is feasible for ALL %d factor rows (min row sum %s, at %r); "
                 "sum(x) = %s" % (len(rows), min_slack, worst_label, sum_x))
    lines.append("dual y is feasible (max per-position load %s at position %s, all <= 1); "
                 "sum(y) = %s" % (max_load, worst_p, sum_y))
    lines.append("weak duality closes: sum(y) = %s = sum(x), so LP* = %s exactly"
                 % (sum_y, claimed_value))

    facts = {
        "text": txt, "n": n, "gamma": len(set(gamma_positions)),
        "gamma_positions": list(gamma_positions), "lp": Fraction(claimed_value),
        "sum_x": sum_x, "sum_y": sum_y, "min_primal_slack": min_slack,
        "max_dual_load": max_load, "factors": len(rows),
    }
    return facts, lines


def format_vector(vec, per_line=6, label=""):
    """Print a rational vector in full: every numerator/denominator, nothing rounded."""
    items = [("%s:%s" % (k, v)) for k, v in vec]
    out = []
    for i in range(0, len(items), per_line):
        out.append(("  " + label if i == 0 else "  " + " " * len(label))
                   + " ".join(items[i:i + per_line]))
    return "\n".join(out) if out else "  " + label + "(empty)"


def support(vec):
    """The non-zero entries of a (key, value) vector, in key order."""
    return [(k, v) for k, v in vec if v != 0]


def certificate_block(text, gamma_positions, x, y, claimed_value):
    """The full printable certificate: the pair vectors in full, then the checks."""
    facts, lines = certify(text, gamma_positions, x, y, claimed_value)
    L = []
    L.append("certificate for `%s`:" % facts["text"])
    L.append("")
    L.append("```")
    L.extend(lines)
    L.append("")
    L.append("gamma = %d, witness attractor Gamma = %s"
             % (facts["gamma"], list(facts["gamma_positions"])))
    L.append("primal x (all %d coordinates, zeros included):" % facts["n"])
    L.append(format_vector([(p, str(v)) for p, v in enumerate(x)], per_line=8, label="x = "))
    L.append("dual y (support only; every other factor carries y_f = 0):")
    L.append(format_vector([(lab, str(v)) for lab, v in y.items() if v != 0],
                           per_line=4, label="y = "))
    L.append("")
    L.append("gap = gamma / LP* = %d / (%s) = %s" % (facts["gamma"], facts["lp"],
                                                     Fraction(facts["gamma"]) / facts["lp"]))
    L.append("```")
    return facts, "\n".join(L)


if __name__ == "__main__":                  # pragma: no cover - manual probe
    import sys
    from simplex import cover_lp
    sym = [int(c) for c in (sys.argv[1] if len(sys.argv) > 1 else "0110101101110")]
    ti = TextInstance(sym)
    cov = ti.nodes
    gamma, pos = cov.exact_min_cover()
    lp = cover_lp(cov.rows, cov.n)
    y = {lab: w for lab, w in zip(cov.labels, lp.y)}
    facts, block = certificate_block(sym, pos, lp.x, y, lp.value)
    print(block)
    print("gamma = %s, LP* = %s" % (gamma, facts["lp"]))
