#!/usr/bin/env python3
"""run_families.py -- measure the gap gamma - ceil(delta) across string families.

THE QUESTION.  `delta` (the KNP substring complexity) is a certified lower bound on
`gamma` (the smallest attractor) and is computable in O(n) from the suffix array, while
`gamma` is NP-hard.  So the natural naive conjecture is

    (N)  gamma = ceil(delta)   on "repetitive" strings,

which, if true, would make gamma computable exactly in linear time exactly where
compressed indexes live.  This script measures `gamma - ceil(delta)` per family with a
*certified bracket* on gamma and an *exact* delta, and says where (N) holds and where it
fails, and how the gap behaves as n grows.

WHAT IS CERTIFIED, AND BY WHOM.  Nothing here re-implements the two tools it stands on:

  * `tools/attractor/anytime.py::search` yields a monotone, verified attractor (ub) and a
    certified lower bound lb = max(ceil(delta), packing bound, completed-DFS proof);
  * `tools/attractor/instance.py::Instance` gives delta exactly (via repmeter's
    `delta_exact`), the definition-level `verify`, and the re-checkable packing
    certificate;
  * `tools/repmeter/measure.py::gen_text` supplies the Fibonacci, Thue-Morse and random
    texts, so those families are the same texts the rest of the repository measures.

Every number in the emitted table is one of: an exact rational (delta), a certified
endpoint (lb, ub), or the literal string "not computed".  A row is only *computed* if both
endpoints survived their own checks; otherwise it carries a reason.  `check.py` re-derives
every endpoint from the text alone.

THE ONE WORKAROUND, STATED.  `anytime.search` raises
`RuntimeError("greedy stalled with N uncovered nodes")` on some texts (e.g. the ternary de
Bruijn word of order 2, random 4-ary n = 64 seed 1).  The cause is in the GRASP restart:
`greedy(inst, top=3)` insists on collecting exactly 3 picks and pops the heap empty when
fewer than 3 positions still have positive gain (`anytime.py`, the `while len(picks) < top`
loop).  tools/attractor is outside this directory's ownership, so the crash is recorded
(`path == "primitives-fallback"`) and the row is measured with the same primitives that
`search` uses internally -- `greedy`, `prune`, `local_search`, `decision` -- scheduled in
ten lines.  Such rows are marked in the table; they are never silently dropped.

NOT CLAIMED.  Every growth statement over n is an empirical trend over the computed rows,
not a theorem.  `gamma` is reported as an integer only when it *is* one here: the bracket
closed (lb == ub) or the text is short enough for the complete DFS (n <= 14).

Budget: per-row wall clock, from `--base-budget` scaled with n; every run is under
`timeout` in run.sh, and every loop asserts progress.
"""

import argparse
import faulthandler
import json
import os
import random
import sys
import time
from fractions import Fraction
from math import ceil, log

_HERE = os.path.dirname(os.path.abspath(__file__))
_ATTRACTOR = os.path.normpath(os.path.join(_HERE, os.pardir))
_REPMETER = os.path.normpath(os.path.join(_HERE, os.pardir, os.pardir, "repmeter"))
for _p in (_ATTRACTOR, _REPMETER):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import anytime                                    # noqa: E402  (path set up above)
from instance import Instance, factor_str         # noqa: E402
from measure import gen_text                      # noqa: E402

# n up to this length gets the complete DFS, so gamma is known exactly even when the
# anytime bracket does not close.
EXACT_GAMMA_N = 14
# Node budget for the complete DFS; the DFS is exhaustive below EXACT_GAMMA_N.
BIG_NODE_CAP = 10 ** 9
# Per-row node budget for the "exact tail" that raises lb (anytime.search's default).
TAIL_NODE_CAP = 200000


# --------------------------------------------------------------------------
# the families: one spec per text, so check.py can rebuild the very same text
# --------------------------------------------------------------------------


def thue_morse_word(k):
    """t_0 = 0, t_{j+1} = t_j complement(t_j); length 2^k."""
    t = [0]
    for _ in range(k):                            # every step doubles, so it ends
        t = t + [1 - c for c in t]
    assert len(t) == 1 << k
    return t


def unary_word(n, symbol=0):
    return [symbol] * n


def periodic_word(periods, block=(0, 1)):
    """(ab)^periods and friends."""
    out = []
    for _ in range(periods):                      # progress: one period per round
        out.extend(block)
    assert len(out) == periods * len(block)
    return out


def mechanical_word(n, p, q):
    """s_i = ceil((i+1)p/q) - ceil(i p/q): the balanced word of rational slope p/q.

    Rational slope means the word is periodic (period q), NOT Sturmian -- Sturmian words
    are by definition aperiodic, the Fibonacci words below being the golden-slope case.
    """
    assert 0 < p < q
    out = []
    prev = 0
    for i in range(n):                            # progress: i increases
        cur = ((i + 1) * p + q - 1) // q
        out.append(cur - prev)
        prev = cur
    assert len(out) == n and set(out) == {0, 1}
    return out


def de_bruijn_word(k, sigma=2):
    """A binary/sigma-ary de Bruijn sequence of order k (Fredricksen-Kessler-Maiorana).

    Concatenate, in lexicographic order, every Lyndon word over {0..sigma-1} whose length
    divides k.  The result has length sigma^k and contains every length-k word exactly
    once cyclically; check.py verifies both properties instead of trusting this comment.
    """
    n = sigma ** k
    out = []
    a = [0] * (n + 1)

    def db(t, p):
        if t > k:
            if k % p == 0:
                out.extend(a[1:p + 1])
            return
        a[t] = a[t - p]
        db(t + 1, p)
        for j in range(a[t - p] + 1, sigma):
            a[t] = j
            db(t + 1, t)

    db(1, 1)
    assert len(out) == n, "de Bruijn construction produced %d symbols, want %d" % (
        len(out), n)
    return out[:n]


def random_word(n, seed, sigma=2):
    rng = random.Random("%s:%d" % (seed, sigma))
    return [rng.randrange(sigma) for _ in range(n)]


def run_length_word(L, periods):
    """(a^L b^L)^periods -- long runs, so the text is repetitive at every scale."""
    out = []
    for j in range(periods):                      # progress: j increases
        out.extend([j % 2] * L)                   # an a-run ...
        out.extend([(j + 1) % 2] * L)             # ... then a b-run
    assert len(out) == 2 * L * periods
    return out


def square_word(m, seed, sigma=2, reverse=False):
    """S S, or S S^R -- one repeated half."""
    s = random_word(m, seed, sigma)
    return s + (s[::-1] if reverse else s)


def build_text(spec):
    """Spec -> list of symbols.  The single source of truth for every text here."""
    kind = spec["kind"]
    if kind == "fibonacci":
        return gen_text("fibonacci:%d" % spec["k"])
    if kind == "thue-morse":
        return gen_text("thue-morse:%d" % spec["k"])
    if kind == "unary":
        return unary_word(spec["n"])
    if kind == "periodic":
        return periodic_word(spec["periods"])
    if kind == "mechanical":
        return mechanical_word(spec["n"], spec["p"], spec["q"])
    if kind == "debruijn":
        return de_bruijn_word(spec["k"], spec.get("sigma", 2))
    if kind == "random":
        return random_word(spec["n"], spec["seed"], spec.get("sigma", 2))
    if kind == "runs":
        return run_length_word(spec["L"], spec["periods"])
    if kind == "square":
        return square_word(spec["m"], spec["seed"], spec.get("sigma", 2),
                           spec.get("reverse", False))
    raise SystemExit("unknown spec kind %r" % (kind,))


def family_cases():
    """(family, label, spec) for every row, roughly cheapest first."""
    cases = []

    # 1. a^n -- the most repetitive text there is; gamma = delta = 1 expected.
    for n in (4, 8, 16, 64, 256):
        cases.append(("unary a^n", "a^%d" % n, {"kind": "unary", "n": n}))

    # 2. (ab)^n -- period 2.
    for m in (2, 4, 8, 16, 32, 64, 128):
        cases.append(("periodic (ab)^n", "(ab)^%d" % m,
                      {"kind": "periodic", "periods": m}))

    # 3. Fibonacci words F_k (the golden-ratio Sturmian word), lengths 13 .. 6765.
    for k in range(7, 21):
        cases.append(("Fibonacci (Sturmian)", "F_%d" % k, {"kind": "fibonacci", "k": k}))

    # 4. Thue-Morse t_k, lengths 4 .. 8192.
    for k in range(2, 14):
        cases.append(("Thue-Morse", "t_%d" % k, {"kind": "thue-morse", "k": k}))

    # 5. Balanced periodic words of rational slope p/q (NOT Sturmian: periodic).
    for (p, q) in ((1, 3), (2, 5), (3, 7)):
        for n in (42, 105, 210):
            cases.append(("balanced periodic p/q", "%d/%d n=%d" % (p, q, n),
                          {"kind": "mechanical", "n": n, "p": p, "q": q}))

    # 6. de Bruijn sequences: every length-k word exactly once.  k = 8 (n = 256) is the
    # last order whose bracket the search leaves open, which is itself a data point.
    for k in range(2, 9):
        cases.append(("de Bruijn sigma=2", "k=%d n=%d" % (k, 1 << k),
                      {"kind": "debruijn", "k": k}))
    cases.append(("de Bruijn sigma=3", "k=2 n=9", {"kind": "debruijn", "k": 2, "sigma": 3}))
    cases.append(("de Bruijn sigma=4", "k=2 n=16",
                  {"kind": "debruijn", "k": 2, "sigma": 4}))

    # 7. random over sigma = 2 (the incompressible baseline).  Seeds 11..13 are disjoint
    # from the square family's seeds 1, 2, so a "random" row is never a prefix of a
    # "square" row's S (which would make those two families silently correlated).
    for n in (16, 32, 64, 128):
        for seed in (11, 12, 13):
            cases.append(("random sigma=2", "n=%d s=%d" % (n, seed),
                          {"kind": "random", "n": n, "seed": seed}))
    for n in (256, 512, 1024):
        cases.append(("random sigma=2", "n=%d s=11" % n,
                      {"kind": "random", "n": n, "seed": 11}))

    # 8. random over sigma = 4.
    for n in (16, 32, 64, 128):
        for seed in (11, 12):
            cases.append(("random sigma=4", "n=%d s=%d" % (n, seed),
                          {"kind": "random", "n": n, "seed": seed, "sigma": 4}))
    for n in (256, 512):
        cases.append(("random sigma=4", "n=%d s=11" % n,
                      {"kind": "random", "n": n, "seed": 11, "sigma": 4}))

    # 9. run-length texts (a^L b^L)^m.
    for L in (2, 4, 8, 16):
        for periods in (16, 32, 64):
            n = 2 * L * periods
            if n > 2048:
                continue
            cases.append(("run-length (a^L b^L)^m", "L=%d m=%d n=%d" % (L, periods, n),
                          {"kind": "runs", "L": L, "periods": periods}))

    # 10/11. one repeated half: S S and S S^R.
    for m in (8, 16, 32, 64, 128, 256):
        for seed in (1, 2):
            cases.append(("square S S", "m=%d s=%d n=%d" % (m, seed, 2 * m),
                          {"kind": "square", "m": m, "seed": seed}))
    for m in (8, 16, 32, 64, 128, 256):
        for seed in (1, 2):
            cases.append(("reverse square S S^R", "m=%d s=%d n=%d" % (m, seed, 2 * m),
                          {"kind": "square", "m": m, "seed": seed, "reverse": True}))
    return cases


# --------------------------------------------------------------------------
# the measurement of one row
# --------------------------------------------------------------------------


def budget_for(n, base):
    """Wall-clock budget for one row: grows with n, capped so the sweep finishes."""
    return min(25.0, max(base, base * n / 128.0))


def certified_lower_bound(inst, ub, deadline, seed=0):
    """lb = max(ceil(delta), packing, completed-DFS proof), with its provenance.

    Only used by the primitives fallback (anytime.search computes the same three things
    internally); `check.py` re-derives this from scratch rather than calling it.
    """
    delta_ceil = int(ceil(inst.delta()))
    pack_k, pack_w = inst.packing_bound(seed=seed, restarts=32,
                                        deadline=None if deadline is None
                                        else time.monotonic() + 1.0)
    ok, _detail = inst.certify_packing(pack_w)
    assert ok, "packing certificate failed to re-check"
    lb = max(delta_ceil, pack_k)
    source = ("delta" if delta_ceil > pack_k else
              "packing" if pack_k > delta_ceil else "delta+packing")
    k = lb
    while k < ub:
        if deadline is not None and time.monotonic() > deadline:
            break
        sol, status = anytime.decision(inst, k, deadline=deadline, node_cap=TAIL_NODE_CAP)
        if status == "infeasible":
            k = k + 1                       # certified: no attractor of size <= k-1
            assert k > lb, "iterative deepening did not advance"
            lb, source = k, "exact tail"
            continue
        if status == "found":
            assert inst.verify(sol), "DFS returned a non-attractor"
            break
        break                               # node budget exhausted: conclude nothing
    return lb, source, pack_k, pack_w


def primitives_bracket(inst, budget_s, seed=0):
    """The fallback: the same primitives search() schedules, without the GRASP restart.

    `anytime.search` cannot be used when its `greedy(top=3)` restart crashes (see the
    module docstring); this reproduces its phases 1-4 for such a text: greedy, prune,
    local search (all from anytime), then the certified lower bound above.  ub is
    monotone by construction because only shorter verified attractors are adopted.
    """
    t0 = time.monotonic()
    deadline = t0 + budget_s
    gamma = anytime.prune(inst, anytime.greedy(inst))
    assert inst.verify(gamma), "greedy+prune produced a non-attractor"
    if time.monotonic() < deadline:
        shorter = anytime.local_search(inst, gamma, deadline=deadline,
                                       rng=random.Random(seed))
        assert inst.verify(shorter), "local search produced a non-attractor"
        assert len(shorter) <= len(gamma), "local search returned a longer attractor"
        gamma = shorter
    lb, source, pack_k, pack_w = certified_lower_bound(inst, len(gamma), deadline, seed)
    assert lb <= len(gamma), "certified lb %d exceeds ub %d" % (lb, len(gamma))
    return [{"t": round(time.monotonic() - t0, 3), "gamma": list(gamma),
             "ub": len(gamma), "lb": lb, "packing": pack_k, "phase": "primitives",
             "lb_source": source, "done": True,
             "certified_exact": lb >= len(gamma)}], "primitives-fallback"


def run_anytime(inst, budget_s, seed=0):
    """(final record, path, note).  Records the anytime.search crash instead of hiding it."""
    try:
        steps = list(anytime.search(inst, budget_s=budget_s, seed=seed))
        assert steps and steps[-1].get("done"), "search did not reach its final record"
        return steps[-1], "search", ""
    except RuntimeError as exc:
        final, path = primitives_bracket(inst, budget_s, seed)
        return final[0], path, str(exc)


def measure_row(family, label, spec, base_budget, exact_limit=EXACT_GAMMA_N):
    """One row of the table, or a row that says honestly why it is not there."""
    row = {"family": family, "label": label, "spec": spec,
           "status": "not computed", "reason": ""}
    t0 = time.monotonic()
    try:
        text = build_text(spec)
        inst = Instance(text)
    except Exception as exc:                      # a generator bug is not a data point
        row["reason"] = "text/instance build failed: %r" % (exc,)
        return row
    n = inst.n
    budget = budget_for(n, base_budget)
    row.update({"n": n, "sigma": len(set(text)) if n else 0, "budget_s": round(budget, 2),
                "head": "".join(str(c) for c in text[:40])})
    try:
        delta = inst.delta()
        final, path, note = run_anytime(inst, budget)
    except Exception as exc:                      # any tool failure is reported, not hidden
        row["reason"] = "measurement failed: %r" % (exc,)
        row["seconds"] = round(time.monotonic() - t0, 2)
        return row

    ub = final["ub"]
    gamma = list(final["gamma"])
    ub_source = "anytime-search" if path == "search" else "primitives-fallback"
    assert inst.verify(gamma), "the reported attractor does not verify"
    assert len(gamma) == ub, "ub %d != |gamma| %d" % (ub, len(gamma))
    lb = final["lb"]
    assert lb <= ub, "lb %d > ub %d" % (lb, ub)

    # gamma is an integer only when the bracket closed or the DFS is complete.
    gamma_exact = None
    how = ""
    if lb >= ub:
        gamma_exact, how = ub, "bracket closed"
    elif n <= exact_limit:
        sol, _proved = anytime.exact_gamma(inst, node_cap=BIG_NODE_CAP, lb=lb)
        if sol is not None:
            assert inst.verify(sol), "complete DFS returned a non-attractor"
            assert len(sol) <= ub, "complete DFS found %d > ub %d" % (len(sol), ub)
            gamma_exact, how = len(sol), "complete DFS (n <= %d)" % exact_limit
            if len(sol) < ub:                     # tighten ub with the exact answer
                ub, gamma, ub_source = len(sol), list(sol), "complete DFS"
    else:
        how = "not computed"

    delta_ceil = int(ceil(delta))
    row.update({
        "status": "computed",
        "delta_num": delta.numerator, "delta_den": delta.denominator,
        "delta_float": round(float(delta), 6), "delta_ceil": delta_ceil,
        "lb": lb, "ub": ub, "lb_source": final.get("lb_source", "?"),
        "ub_source": ub_source, "closed": bool(lb >= ub),
        "gamma": gamma, "gamma_exact": gamma_exact, "gamma_exact_how": how,
        "gap_lo": lb - delta_ceil, "gap_hi": ub - delta_ceil,
        "packing": final.get("packing"),
        "path": path, "path_note": note,
        "seconds": round(time.monotonic() - t0, 2),
    })
    # The packing family that supports this row's lb, recorded so check.py can re-certify
    # the *reported* witness rather than only a freshly rebuilt one.  The node index is
    # kept because it is what the exact tail's prune consumes (packing_mask).
    pack_k, pack_w = inst.packing_bound(seed=0, restarts=32)
    ok_pack, _detail = inst.certify_packing(pack_w)
    assert ok_pack, "the recorded packing family does not re-certify"
    row["packing_nodes"] = [int(w[0]) for w in pack_w]
    row["packing_factors"] = [[int(c) for c in w[1]] for w in pack_w]
    row["packing_k_recomputed"] = pack_k
    return row


# --------------------------------------------------------------------------
# rendering: the table in the note is this function's output, byte for byte
# --------------------------------------------------------------------------


def fmt_delta(row):
    if row["delta_den"] == 1:
        return "%d" % row["delta_num"]
    return "`%d/%d`" % (row["delta_num"], row["delta_den"])


def fmt_gap(row):
    if row["gamma_exact"] is not None:
        return "%d" % (row["gamma_exact"] - row["delta_ceil"])
    return "[%d, %d]" % (row["gap_lo"], row["gap_hi"])


def fmt_gamma(row):
    if row["gamma_exact"] is not None:
        return "%d (%s)" % (row["gamma_exact"], row["gamma_exact_how"])
    return "not computed"


def render_table(rows):
    out = ["| family | text | n | delta | ceil(delta) | lb | ub | gamma | bracket | "
           "gap = gamma - ceil(delta) |",
           "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    for row in rows:
        if row["status"] != "computed":
            out.append("| %s | %s | — | — | — | — | — | not computed | — | %s |"
                       % (row["family"], row["label"], row["reason"]))
            continue
        bracket = "CLOSED" if row["closed"] else "open"
        if row["path"] != "search":
            bracket += ", fallback"
        out.append("| %s | %s | %d | %s | %d | %d | %d | %s | %s | %s |"
                   % (row["family"], row["label"], row["n"], fmt_delta(row),
                      row["delta_ceil"], row["lb"], row["ub"], fmt_gamma(row),
                      bracket, fmt_gap(row)))
    return "\n".join(out)


def family_gap_trends(rows, min_points=3):
    """Families with at least min_points rows, each sorted by (n, label)."""
    by_family = {}
    for row in rows:
        if row["status"] != "computed":
            continue
        by_family.setdefault(row["family"], []).append(row)
    return [(family, sorted(by_family[family], key=lambda r: (r["n"], r["label"])))
            for family in sorted(by_family)
            if len(by_family[family]) >= min_points]


def gap_series(rows):
    """Per family: {n: min gap_lo over the seeds computed}.

    The *minimum* lower end at each n is a certified statement ("some computed text of this
    family at this n has a gap at least this large"), which is what a trend in n can rest on
    without averaging bounds of different strength.
    """
    series = {}
    for family, fam in family_gap_trends(rows, min_points=1):
        for row in fam:
            current = series.setdefault(family, {}).get(row["n"])
            if current is None or row["gap_lo"] < current:
                series[family][row["n"]] = row["gap_lo"]
    return series


def render_trends(rows):
    """Generated block 2: the gap per text on the families where it is nonzero."""
    out = ["| family | n | delta | ceil(delta) | gap range | gap / delta |",
           "| --- | --- | --- | --- | --- | --- |"]
    for family, fam in family_gap_trends(rows, min_points=3):
        for row in fam:
            if row["ub"] - row["delta_ceil"] <= 0:
                continue                     # gap 0 at both ends: nothing to trend
            ratio = row["gap_lo"] * row["delta_den"] / float(row["delta_num"])
            out.append("| %s | %d | %s | %d | [%d, %d] | %.2f |"
                       % (family, row["n"], fmt_delta(row), row["delta_ceil"],
                          row["gap_lo"], row["gap_hi"], ratio))
    return "\n".join(out)


def growth_factor(name, n0, n1, d0, d1):
    """The factor by which each candidate shape grows between n0 and n1."""
    if name == "constant":
        return 1.0
    if name == "log2 n":
        return log(n1, 2) / log(n0, 2)
    if name == "sqrt n":
        return (n1 / n0) ** 0.5
    if name == "n":
        return n1 / n0
    if name == "delta":
        return d1 / d0
    raise AssertionError("unknown shape %r" % (name,))


SHAPES = ("constant", "log2 n", "sqrt n", "n", "delta")


def render_rates(rows):
    """Generated block 3: how fast the gap grows, against the named shapes.

    For each family, the smallest and largest n with a nonzero certified gap, the end
    points of the gap series (minimum over the seeds computed), and the factor by which
    each candidate shape -- constant, log2 n, sqrt n, n, delta -- would grow over that n
    range; the closest shape in log space is marked `*`.  This classifies a measured
    trend; it is not a theorem, and the seed-to-seed spread in block 2 is comparable to
    the effect on the S S / S S^R families.
    """
    out = ["| family | n range | gap at n_min | gap at n_max | gap grew by | log-log "
           "exponent | " + " | ".join(SHAPES) + " | closest shape | n values |",
           "| " + " | ".join(["---"] * (7 + len(SHAPES) + 1)) + " |"]
    series = gap_series(rows)
    for family in sorted(series):
        pts = sorted((n, gap) for n, gap in series[family].items() if gap > 0)
        if len(pts) < 2:
            continue
        n0, g0 = pts[0]
        n1, g1 = pts[-1]
        grew = g1 / g0
        here = [r for r in rows if r["status"] == "computed" and r["family"] == family]
        d0 = min(r["delta_num"] / r["delta_den"] for r in here if r["n"] == n0)
        d1 = max(r["delta_num"] / r["delta_den"] for r in here if r["n"] == n1)
        factors = {name: growth_factor(name, n0, n1, d0, d1) for name in SHAPES}
        best = min(SHAPES, key=lambda name: abs(log(grew) - log(factors[name])))
        cells = ["x%.2f%s" % (factors[name], " *" if name == best else "")
                 for name in SHAPES]
        exponent = log(grew) / log(n1 / n0) if n1 > n0 else 0.0
        out.append("| %s | %d..%d | %d | %d | x%.2f | %.2f | %s | %s | %s |"
                   % (family, n0, n1, g0, g1, grew, exponent,
                      " | ".join(cells), best, ", ".join(str(n) for n, _g in pts)))
    return "\n".join(out)


def render_verdicts(rows):
    """Generated block 1: per family, where gamma = ceil(delta) and where it does not.

    "gamma > ceil(delta)" counts only rows whose gap is proved positive (the certified
    lower end of the gap exceeds 0); "undecided" counts rows whose bracket is still open
    at both ends of the gap, so the family's verdict on that row is not decided here.
    """
    by_family = {}
    for row in rows:
        by_family.setdefault(row["family"], []).append(row)
    out = ["| family | rows | computed | gamma known exactly | gamma = ceil(delta) | "
           "gamma > ceil(delta) | undecided | max certified gap | n range |",
           "| --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    for family in sorted(by_family):
        fam = by_family[family]
        computed = [r for r in fam if r["status"] == "computed"]
        exact = [r for r in computed if r["gamma_exact"] is not None]
        eq = [r for r in exact if r["gamma_exact"] == r["delta_ceil"]]
        gt = [r for r in exact if r["gamma_exact"] > r["delta_ceil"]]
        undecided = [r for r in computed if r["gamma_exact"] is None]
        out.append("| %s | %d | %d | %d | %d | %d | %d | %d | %d..%d |"
                   % (family, len(fam), len(computed), len(exact), len(eq), len(gt),
                      len(undecided), max((r["gap_lo"] for r in computed), default=0),
                      min(r["n"] for r in fam), max(r["n"] for r in fam)))
    return "\n".join(out)


def render_summary(rows):
    """Counts that the note quotes; generated so they cannot drift."""
    computed = [r for r in rows if r["status"] == "computed"]
    closed = [r for r in computed if r["closed"]]
    eq = [r for r in computed if r["gamma_exact"] is not None
          and r["gamma_exact"] == r["delta_ceil"]]
    gt = [r for r in computed if r["gamma_exact"] is not None
          and r["gamma_exact"] > r["delta_ceil"]]
    exact = [r for r in computed if r["gamma_exact"] is not None]
    fallback = [r for r in computed if r["path"] != "search"]

    def over_delta(row, key):
        return row[key] * row["delta_den"] / row["delta_num"]

    worst_lo = max(computed, key=lambda r: over_delta(r, "gap_lo"))
    worst_hi = max(computed, key=lambda r: over_delta(r, "gap_hi"))
    positive = [r for r in computed if r["gap_lo"] > 0]
    tightest = min(positive, key=lambda r: over_delta(r, "gap_lo")) if positive else None
    lines = [
        "rows listed: %d, computed: %d, not computed: %d"
        % (len(rows), len(computed), len(rows) - len(computed)),
        "brackets CLOSED: %d of %d" % (len(closed), len(computed)),
        "gamma known exactly (closed bracket or complete DFS): %d" % len(exact),
        "among those: gamma == ceil(delta): %d, gamma > ceil(delta): %d"
        % (len(eq), len(gt)),
        "rows measured through the primitives fallback: %d (%s)"
        % (len(fallback), sorted({r["spec"]["kind"] for r in fallback})),
        "largest gap/delta in this table: %.2f at the certified lower ends (%s), "
        "%.2f at the upper ends (%s)"
        % (over_delta(worst_lo, "gap_lo"), worst_lo["label"],
           over_delta(worst_hi, "gap_hi"), worst_hi["label"]),
        "smallest gap/delta among the rows with a proved positive gap: %.2f (%s)"
        % (over_delta(tightest, "gap_lo"), tightest["label"]),
    ]
    return "\n".join(lines)


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------


def main(argv=None):
    faulthandler.dump_traceback_later(7200, exit=True)      # never hang
    ap = argparse.ArgumentParser(description="measure gamma - ceil(delta) per family")
    ap.add_argument("--out-dir", default=_HERE,
                    help="where results.json and table.md are written (default: here)")
    ap.add_argument("--base-budget", type=float, default=3.0,
                    help="per-row budget in seconds at n <= 128 (default 3)")
    ap.add_argument("--only", default=None,
                    help="comma-separated family substrings to run (default: all)")
    ap.add_argument("--limit", type=int, default=0,
                    help="stop after this many rows (0 = all), for a smoke test")
    args = ap.parse_args(argv)

    cases = family_cases()
    if args.only:
        wanted = [w.strip().lower() for w in args.only.split(",") if w.strip()]
        cases = [c for c in cases if any(w in c[0].lower() for w in wanted)]
        assert cases, "no family matches %r" % (args.only,)
    if args.limit:
        cases = cases[:args.limit]

    rows = []
    t_start = time.monotonic()
    for i, (family, label, spec) in enumerate(cases):
        row = measure_row(family, label, spec, args.base_budget)
        rows.append(row)
        assert len(rows) == i + 1, "row accounting lost a row"
        if row["status"] == "computed":
            sys.stderr.write("  [%3d/%3d] %-26s %-18s n=%5d lb=%4d ub=%4d %s %5.1fs\n"
                             % (i + 1, len(cases), family, label, row["n"], row["lb"],
                                row["ub"], "CLOSED" if row["closed"] else "open",
                                row["seconds"]))
        else:
            sys.stderr.write("  [%3d/%3d] %-26s %-18s NOT COMPUTED: %s\n"
                             % (i + 1, len(cases), family, label, row["reason"]))
    elapsed = round(time.monotonic() - t_start, 1)

    table = render_table(rows)
    verdicts = render_verdicts(rows)
    trends = render_trends(rows)
    rates = render_rates(rows)
    summary = render_summary(rows)

    os.makedirs(args.out_dir, exist_ok=True)
    payload = {"generated_by": "tools/attractor/experiments/run_families.py",
               "exact_gamma_n": EXACT_GAMMA_N, "base_budget_s": args.base_budget,
               "elapsed_s": elapsed, "summary": summary, "rows": rows}
    with open(os.path.join(args.out_dir, "results.json"), "w") as fh:
        json.dump(payload, fh, indent=1, sort_keys=True)
        fh.write("\n")
    with open(os.path.join(args.out_dir, "table.md"), "w") as fh:
        fh.write(table + "\n")
    with open(os.path.join(args.out_dir, "trends.md"), "w") as fh:
        fh.write(trends + "\n")
    with open(os.path.join(args.out_dir, "rates.md"), "w") as fh:
        fh.write(rates + "\n")
    with open(os.path.join(args.out_dir, "summary.md"), "w") as fh:
        fh.write(summary + "\n")
    with open(os.path.join(args.out_dir, "verdicts.md"), "w") as fh:
        fh.write(verdicts + "\n")

    print(verdicts)
    print()
    print(table)
    print()
    print(trends)
    print()
    print(rates)
    print()
    print(summary)
    sys.stderr.write("total %.1fs\n" % elapsed)
    return 0


if __name__ == "__main__":
    sys.exit(main())
