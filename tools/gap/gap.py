"""gap.py -- measure the integrality gap gamma / LP* of the attractor set-cover LP.

THE QUESTION.  For the set-cover instance of a text S (universe = distinct factors of S,
set_p = factors crossing position p), how large is

    gap(S) = gamma(S) / LP*(S)  >=  1,

where gamma is the minimum attractor (integer program) and LP* its LP relaxation, in
exact rational arithmetic?  An O(1) gap would put a constant-factor approximation within
reach of LP rounding; a Theta(log n) gap would suggest the log-factor bounds are inherent
for LP-based methods.

WHAT IS MEASURED, AND HOW IT IS CERTIFIED.

  * gamma from `Cover.exact_min_cover`: exhaustive branch and bound (so exact), and the
    returned position set is re-checked against every row of the instance, and again by
    tools/attractor's independent definition-level verifier.
  * LP* from `Cover.lp` (simplex.py): a dual-feasible y and a primal-feasible x of equal
    objective, both re-checked, so LP* is certified by weak duality -- see simplex.py.
  * every record is screened against the two invariants that must hold:
        LP* <= gamma     (the LP relaxes the integer program)
        LP* >= delta     (see below, proved in the README)
    A record that violates either is an error, not a data point.

WHY LP* >= delta.  Let F_k be the set of distinct factors of length k, |F_k| = d_k, so
delta = max_k d_k/k.  For any primal-feasible x, summing the constraints of the elements
of F_k gives

        d_k <= sum_{f in F_k} sum_{p in C(f)} x_p = sum_p x_p * #{f in F_k : p in C(f)}.

A position p crosses only the length-k factors occurring in [p-k+1, p+k-1], at most k of
them, so the right-hand side is at most k * sum_p x_p and sum_p x_p >= d_k/k for every k,
i.e. LP* >= delta.  (MY-INFERENCE from weak duality plus counting; checked exactly, as a
Fraction, on every instance this file measures.)

CORPORA (from the task):
  (a) every binary string n <= 12,   (b) every ternary string n <= 8,
  (c) Fibonacci and Thue-Morse words, up to the largest n the exact rational LP finishes
      for, (d) random binary strings,
  plus the single-k instance (universe = factors of length exactly k, k = 1, 2, 3) and the
  companion universe of all factors of length <= k.

WHY gap_full >= gap_k, ALWAYS.  The single-k universe F_k is a sub-universe of all
factors, so LP*_full <= LP*_k (dropping constraints relaxes the LP further) while
gamma_full >= gamma_k (covering every factor covers F_k).  Hence
gamma_full/LP*_full >= gamma_k/LP*_k.  So a single-k gap can never exceed the full gap:
if the fixed-k gaps sit at 1 while the full gap is larger, the difficulty is in the
*mixing* of lengths, not in one length.  (This file checks the inequality too.)

Run:  timeout 900 python3 gap.py --all --max-seconds 60
"""

import argparse
import json
import sys
import time
from fractions import Fraction

from instance import (BudgetExhausted, TextInstance, binary_strings, ternary_strings,
                      text_str)
from measure import gen_text
from simplex import LPError

HIST_TOP = 12          # distinct gap values kept in the printed histogram


# --------------------------------------------------------------------------
# one text, one universe
# --------------------------------------------------------------------------


def measure(sym, universe="nodes", k=None, max_seconds=None, cross_check=False,
            fast=False):
    """gamma, LP*, gap and delta of one text in one universe, all certified.

    max_seconds bounds the LP solve: the exact simplex is slow on long texts, and on
    expiry this raises LPTimeout instead of reporting a bound it did not prove.
    cross_check also computes gamma and LP* in the other universe and asserts they
    agree (the node reduction loses nothing); check.py does this exhaustively.
    """
    t0 = time.monotonic()
    ti = TextInstance(sym)
    deadline = None if max_seconds is None else time.monotonic() + max_seconds
    rec = {"text": text_str(ti.sym), "n": ti.n, "universe": universe, "k": k}
    if ti.n == 0:
        rec.update({"gamma": "0", "lp": "0", "gap": "1", "delta": "0", "elements": 0})
        return rec
    cov = ti.cover(universe, k)
    rec["universe"] = cov.universe
    rec["elements"] = len(cov)
    gamma, positions = cov.exact_min_cover()
    lp = cov.lp(deadline=deadline)
    if lp.value <= 0:
        raise AssertionError("LP* = %s <= 0 on a nonempty instance" % (lp.value,))
    gap = Fraction(gamma) / lp.value
    delta = ti.delta()
    lb = ti.lp_lower_bound(cov.universe, k)
    if lp.value > gamma:
        raise AssertionError("LP* = %s > gamma = %s on %r" % (lp.value, gamma, rec["text"]))
    if lp.value < lb:
        raise AssertionError("LP* = %s < %s = %s on %r"
                             % (lp.value, cov.universe, lb, rec["text"]))
    if gap < 1:
        raise AssertionError("gap = %s < 1 on %r" % (gap, rec["text"]))
    if cov.universe in ("nodes", "factors"):
        if not ti.node_factor_verify(positions):
            raise AssertionError("attractor %r failed the definition-level verifier"
                                 % (positions,))
    else:
        if cov.universe.startswith("factors_le_"):
            lo, hi = 1, k
        else:
            lo, hi = k, k
        miss = ti.verify_factor_cover(positions, lo, hi)
        if miss is not None:
            raise AssertionError("positions %r miss the length-%d..%d factor %r at %d"
                                 % (positions, lo, hi, miss[0], miss[1]))
    rec.update({
        "gamma": str(gamma),
        "gamma_positions": list(positions),
        "lp": str(lp.value),
        "gap": str(gap),
        "delta": str(delta),
        "lp_bound": str(lb),
        "pivots": lp.pivots,
        "seconds": round(time.monotonic() - t0, 3),
    })
    if not fast:
        # the second LP route (two-phase simplex on the primal): every sweep in check.py
        # runs it, the big scans skip it because the pair certificate already pins LP*
        rec["lp_primal_crosscheck"] = str(cov.lp_primal(deadline=deadline))
        if rec["lp_primal_crosscheck"] != rec["lp"]:
            raise AssertionError("the two LP routes disagree on %r: %s vs %s"
                                 % (rec["text"], rec["lp"], rec["lp_primal_crosscheck"]))
    if max_seconds is not None and time.monotonic() > deadline:
        raise LPError("instance budget exhausted after the measurement")
    if cross_check:
        other = "factors" if cov.universe != "factors" else "nodes"
        cov2 = ti.cover(other, k if cov.universe.startswith("factors_") else None)
        g2, _ = cov2.exact_min_cover()
        lp2 = cov2.lp(deadline=deadline)
        if (g2, lp2.value) != (gamma, lp.value):
            raise AssertionError("%s and %s disagree on %r: (%s, %s) vs (%s, %s)"
                                 % (cov.universe, cov2.universe, rec["text"], gamma,
                                    lp.value, g2, lp2.value))
        rec["cross_universe"] = cov2.universe
    return rec


def measure_full(sym, ks=(1, 2, 3), max_seconds=None, le_k=False, factors=False,
                 fast=False):
    """One text: the full-universe record plus the single-k records as sub-records."""
    out = measure(sym, "nodes", None, max_seconds, fast=fast)
    out["sub"] = {}
    if factors and out["n"]:
        out["sub"]["factors"] = measure(sym, "factors", None, max_seconds, fast=fast)
    for k in ks:
        if out["n"] and k <= out["n"]:
            out["sub"]["factors_%d" % k] = measure(sym, "factors_k", k, max_seconds,
                                                   fast=fast)
            if le_k:
                out["sub"]["factors_le_%d" % k] = measure(sym, "factors_le_k", k,
                                                          max_seconds, fast=fast)
    return out


# --------------------------------------------------------------------------
# hunting for the largest gap at a length the exhaustive scan cannot reach
# --------------------------------------------------------------------------


def hunt(n, universe="nodes", k=None, restarts=8, steps=200, max_seconds=60.0, seed=0):
    """Hill-climb over texts of length n for the largest gap; returns (gap, text, record).

    Not a bound and not a substitute for the exhaustive scan: it is a search whose output
    is one certified instance.  Every accepted text's gap is measured by `measure`, so the
    reported value is as certified as any other row of this file.  Mutation is a single
    uniform symbol change, so the walk never leaves the alphabet; ties are accepted so
    that plateaux can be crossed.
    """
    import random
    rng = random.Random(seed)
    t0 = time.monotonic()
    alpha = 2 if universe in ("nodes", "factors") or not k else 3
    best = (Fraction(0), None, None)
    gap_cache = {}

    def gap_of(sym):
        key = tuple(sym)
        if key in gap_cache:
            return gap_cache[key]
        rec = measure(list(sym), universe, k, max_seconds)
        val = Fraction(rec["gap"])
        gap_cache[key] = (val, rec)
        return gap_cache[key]

    for _ in range(restarts):
        sym = [rng.randrange(alpha) for _ in range(n)]
        cur, rec = gap_of(sym)
        for _ in range(steps):
            if time.monotonic() - t0 > max_seconds:
                break
            i = rng.randrange(n)
            old = sym[i]
            sym[i] = rng.randrange(alpha - 1)
            if sym[i] >= old:
                sym[i] += 1
            val, rec2 = gap_of(sym)
            if val >= cur:
                cur, rec = val, rec2
                if val > best[0]:
                    best = (val, list(sym), rec2)
            else:
                sym[i] = old
        if time.monotonic() - t0 > max_seconds:
            break
    return best


# --------------------------------------------------------------------------
# summaries: the distribution, not just the mean
# --------------------------------------------------------------------------


def summarise(records, key="gap"):
    """max, argmax, histogram, mean and median of an exact-Fraction quantity."""
    vals = [(Fraction(r[key]), r) for r in records if key in r]
    if not vals:
        return {"count": 0}
    vals.sort(key=lambda t: -t[0])
    total = sum((v for v, _ in vals), Fraction(0))
    n = len(vals)
    mid = n // 2
    median = vals[mid][0] if n % 2 else (vals[mid - 1][0] + vals[mid][0]) / 2
    hist = {}
    for v, _ in vals:
        hist[v] = hist.get(v, 0) + 1
    order = sorted(hist, reverse=True)
    return {
        "count": n,
        "max": vals[0][0],
        "argmax": [r for v, r in vals if v == vals[0][0]],
        "argmax_count": sum(1 for v, _ in vals if v == vals[0][0]),
        "min": vals[-1][0],
        "mean": total / n,
        "median": median,
        "num_gt_one": sum(1 for v, _ in vals if v > 1),
        "histogram": [(v, hist[v]) for v in order],
        "histogram_rest": sum(hist[v] for v in order[HIST_TOP:]),
    }


def fmt_frac(x):
    return str(x)


def fmt_float(x):
    """A float rendering, for orientation only -- never used to decide anything."""
    return "%.4f" % (float(x.numerator) / float(x.denominator))


def summary_block(title, s, show_argmax=2):
    """A markdown render of one summary."""
    if s.get("count", 0) == 0:
        return "**%s**: no instances measured.\n" % title
    L = []
    L.append("**%s** -- %d instances" % (title, s["count"]))
    L.append("")
    L.append("| quantity | value |")
    L.append("| --- | --- |")
    L.append("| max gap | **%s** (%s) at %d instance(s) |"
             % (fmt_frac(s["max"]), fmt_float(s["max"]), s["argmax_count"]))
    L.append("| min gap | %s (%s) |" % (fmt_frac(s["min"]), fmt_float(s["min"])))
    L.append("| mean gap | %s (%s) |" % (fmt_frac(s["mean"]), fmt_float(s["mean"])))
    L.append("| median gap | %s |" % (fmt_frac(s["median"]),))
    L.append("| instances with gap > 1 | %d of %d (%.2f %%) |"
             % (s["num_gt_one"], s["count"], 100.0 * s["num_gt_one"] / s["count"]))
    L.append("")
    L.append("distribution of gap values (exact, descending):")
    L.append("")
    L.append("| gap | count |")
    L.append("| --- | --- |")
    for v, c in s["histogram"][:HIST_TOP]:
        L.append("| %s | %d |" % (fmt_frac(v), c))
    if s["histogram_rest"]:
        L.append("| (further distinct values, all smaller) | %d |" % s["histogram_rest"])
    L.append("")
    for r in s["argmax"][:show_argmax]:
        L.append("argmax witness: text `%s` (n=%d, %s), gamma = %s at positions %s, "
                 "LP* = %s, gap = %s, delta = %s"
                 % (r["text"], r["n"], r.get("universe", "?"), r["gamma"],
                    r.get("gamma_positions", "?"), r["lp"], r["gap"],
                    r.get("delta", "?")))
    L.append("")
    return "\n".join(L)


# --------------------------------------------------------------------------
# corpora
# --------------------------------------------------------------------------


def corpus_binary(max_n, min_n=1):
    return [("binary n=%d" % len(s), s) for s in binary_strings(max_n, min_n)]


def corpus_ternary(max_n, min_n=1):
    return [("ternary n=%d" % len(s), s) for s in ternary_strings(max_n, min_n)]


def family_specs(which):
    """(label, symbols) for the morphic families and the random texts."""
    out = []
    if which in ("fib", "all"):
        for k in range(2, 17):
            w = gen_text("fibonacci:%d" % k)
            out.append(("fibonacci F_%d" % k, w))
    if which in ("tm", "all"):
        for k in range(1, 10):
            w = gen_text("thue-morse:%d" % k)
            out.append(("thue-morse 2^%d" % k, w))
    if which in ("random", "all"):
        for n in (8, 10, 12, 16, 20, 24, 32, 40, 48, 64, 96, 128):
            for seed in (1, 2, 3):
                w = gen_text("random-binary:%d:%d" % (n, seed))
                out.append(("random n=%d seed %d" % (n, seed), w))
    for label, w in out:
        if not label.endswith(")"):
            label = "%s (n=%d)" % (label, len(w))
    return out


def sub_records(records, key):
    """Flatten the sub-records of one corpus under `key`, keeping the parent label."""
    out = []
    for r in records:
        s = r.get("sub", {}).get(key)
        if s is not None:
            s = dict(s)
            s["label"] = r.get("label", "")
            s["parent_text"] = r["text"]
            out.append(s)
    return out


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def run_corpus(items, args, title):
    records = []
    t0 = time.monotonic()
    skipped = 0
    for i, (label, sym) in enumerate(items):
        try:
            rec = measure_full(sym, ks=args.ks, max_seconds=args.max_seconds,
                               le_k=args.le_k, factors=args.factors, fast=args.fast)
        except (LPError, BudgetExhausted) as exc:   # a budget ran out: no number, no claim
            skipped += 1
            print("     %s: not computed (%s)" % (label, exc), file=sys.stderr)
            continue
        rec["label"] = label
        rec["corpus"] = title
        records.append(rec)
        done = i + 1
        if done % args.progress == 0:
            print("     %s: %d/%d instances, %.1fs"
                  % (title, done, len(items), time.monotonic() - t0), file=sys.stderr)
        if args.max_total_seconds and time.monotonic() - t0 > args.max_total_seconds:
            print("     %s: stopping after %d/%d instances (corpus budget)"
                  % (title, done, len(items)), file=sys.stderr)
            break
    if skipped:
        print("     %s: %d instance(s) not computed (LP budget)" % (title, skipped),
              file=sys.stderr)
    return records


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--all", action="store_true",
                    help="binary n<=12, ternary n<=8, families, unary, single-k")
    ap.add_argument("--binary", type=int, default=0, help="scan all binary strings n<=N")
    ap.add_argument("--ternary", type=int, default=0, help="scan all ternary strings n<=N")
    ap.add_argument("--family", default="", help="fib | tm | random | all")
    ap.add_argument("--unary", action="store_true", help="also the texts a^n")
    ap.add_argument("--factors", action="store_true",
                    help="also measure the O(n^2)-element full factor universe")
    ap.add_argument("--ks", default="1,2,3", help="single-k universes (default 1,2,3)")
    ap.add_argument("--le-k", action="store_true", help="also the length <= k universes")
    ap.add_argument("--max-seconds", type=float, default=60.0,
                    help="per-instance budget (default 60 s)")
    ap.add_argument("--max-total-seconds", type=float, default=0.0,
                    help="per-corpus budget, 0 = unlimited")
    ap.add_argument("--hunt", default="",
                    help="comma-separated lengths to hill-climb for the largest gap")
    ap.add_argument("--hunt-seconds", type=float, default=60.0, help="budget per length")
    ap.add_argument("--hunt-k", type=int, default=0,
                    help="hunt in the single-k universe instead of the full one")
    ap.add_argument("--fast", action="store_true",
                    help="skip the second (primal) LP route; the pair certificate still "
                         "pins LP*, and check.py runs both routes on everything small")
    ap.add_argument("--growth", type=int, default=0,
                    help="per-length table: max gap over all binary strings of length n, "
                         "n <= N, with the argmax text")
    ap.add_argument("--growth-ternary", type=int, default=0,
                    help="the same for ternary strings")
    ap.add_argument("--progress", type=int, default=500)
    ap.add_argument("--json", default="", help="one JSON record per line here")
    ap.add_argument("--out", default="", help="write the markdown report here")
    args = ap.parse_args(argv)
    args.ks = tuple(int(t) for t in args.ks.split(",") if t.strip())
    if not (args.binary or args.ternary or args.family or args.all or args.unary
            or args.hunt or args.growth or args.growth_ternary):
        ap.error("nothing to do: pass --all, --binary N, --ternary N, --family X, --unary")

    lines = []
    everything = []
    corpora = []
    if args.binary or args.all:
        corpora.append(("(a) all binary strings n <= %d, full universe"
                        % (args.binary or 12), corpus_binary(args.binary or 12)))
    if args.ternary or args.all:
        corpora.append(("(b) all ternary strings n <= %d, full universe"
                        % (args.ternary or 8), corpus_ternary(args.ternary or 8)))
    if args.unary or args.all:
        corpora.append(("unary texts a^n (gamma = LP* = 1 by hand)",
                        [("a^%d" % m, [0] * m) for m in (1, 2, 3, 5, 8, 13, 21, 34)]))
    if args.family:
        corpora.append(("(c)+(d) morphic families and random binary texts, full universe",
                        family_specs(args.family)))

    for title, items in corpora:
        recs = run_corpus(items, args, title)
        everything.extend(recs)
        _emit(lines, title, recs, args)
        if args.family and title.startswith("(c)"):
            per = {}
            for r in recs:
                per.setdefault(r["label"].split()[0], []).append(r)
            for fam in sorted(per):
                _emit(lines, "family %s, full universe" % fam, per[fam], args)

    if args.growth:
        lines.append(growth_table(corpus_binary(args.growth, 1), args, "binary",
                                  args.growth, sink=everything))
    if args.growth_ternary:
        lines.append(growth_table(corpus_ternary(args.growth_ternary, 1), args, "ternary",
                                  args.growth_ternary, sink=everything))

    if args.hunt:
        for n in [int(t) for t in args.hunt.split(",") if t.strip()]:
            universe = "factors_k" if args.hunt_k else "nodes"
            val, sym, rec = hunt(n, universe, args.hunt_k or None,
                                 max_seconds=args.hunt_seconds, seed=n)
            if rec is None:
                lines.append("**hunt n=%d**: nothing measured.\n" % n)
                continue
            everything.append(dict(rec, label="hunt n=%d" % n))
            lines.append("**hunt, %s universe, n = %d** -- largest gap found: **%s** "
                         "(%s)\n" % (universe, n, val, fmt_float(val)))
            lines.append("text `%s`, gamma = %s at positions %s, LP* = %s, gap = %s\n"
                         % (rec["text"], rec["gamma"], rec["gamma_positions"],
                            rec["lp"], rec["gap"]))

    # the single-k universes, pooled over every corpus measured
    for k in args.ks:
        subs = sub_records(everything, "factors_%d" % k)
        if subs:
            _emit(lines, "single-k universe: factors of length exactly %d, pooled over "
                  "every corpus above" % k, subs, args)
        if args.le_k:
            subs = sub_records(everything, "factors_le_%d" % k)
            if subs:
                _emit(lines, "universe: factors of length <= %d, pooled over every "
                      "corpus above" % k, subs, args)

    text = "\n".join(lines)
    print(text)
    if args.out:
        with open(args.out, "w") as f:
            f.write(text + "\n")
    if args.json:
        with open(args.json, "w") as f:
            for r in everything:
                f.write(json.dumps(r) + "\n")
    return 0


def growth_table(items, args, alphabet, max_n, sink=None):
    """Per length: max gap, the text attaining it, and how many texts exceed 1.

    This is the shape of the answer to "O(1) or Theta(log n)": a bounded maximum at every
    length is evidence for a bounded gap; a maximum that climbs like log n is evidence the
    other way.  Empirical, and labelled as such -- n <= 12 proves nothing by itself.
    """
    t0 = time.monotonic()
    by_n = {}
    for i, (label, sym) in enumerate(items):
        try:
            rec = measure_full(sym, ks=args.ks, max_seconds=args.max_seconds, fast=True)
        except (LPError, BudgetExhausted) as exc:
            print("     %s: not computed (%s)" % (label, exc), file=sys.stderr)
            continue
        rec["label"] = label
        rec["corpus"] = "%s growth" % alphabet
        by_n.setdefault(rec["n"], []).append(rec)
        if sink is not None:
            sink.append(rec)
        if (i + 1) % args.progress == 0:
            print("     growth %s: %d/%d, %.1fs" % (alphabet, i + 1, len(items),
                                                    time.monotonic() - t0),
                  file=sys.stderr)
    lines = ["**growth of the max gap over all %s strings of length n**\n" % alphabet,
             "| n | texts | max gap | # with gap > 1 | argmax text (gamma, LP*) "
             "| max single-k gap k=1,2,3 |",
             "| --- | --- | --- | --- | --- | --- |"]
    data = []
    for n in sorted(by_n):
        recs = by_n[n]
        s = summarise(recs)
        arg = s["argmax"][0]
        ks = []
        for k in args.ks:
            subs = sub_records(recs, "factors_%d" % k)
            ks.append(str(summarise(subs)["max"]) if subs else "-")
        lines.append("| %d | %d | **%s** (%s) | %d | `%s` (%s, %s) | %s |"
                     % (n, s["count"], s["max"], fmt_float(s["max"]), s["num_gt_one"],
                        arg["text"], arg["gamma"], arg["lp"], ", ".join(ks)))
        data.append({"n": n, "max_gap": str(s["max"]), "argmax": arg["text"],
                     "gamma": arg["gamma"], "lp": arg["lp"],
                     "num_gt_one": s["num_gt_one"], "count": s["count"],
                     "single_k": list(ks)})
    lines.append("")
    if data:
        lines.append(fit_growth(data))
    args.growth_data = data
    return "\n".join(lines)


def fit_growth(data, models=None):
    """Least-squares fit of `gap(n) - 1 = c / f(n)` for the candidate shapes.

    Floats appear ONLY here: a fit is a description of the trend, and no bound in this
    file is derived from it.  Candidate shapes: a bounded constant, `1 + c/log2 n`,
    `1 + c/sqrt(n)`, `1 + c/n^(1/3)`.  All four are fitted through the origin on
    `y = gap - 1` with the single parameter `c`, so the comparison is a single number per
    model: the residual sum of squares relative to the total.
    """
    import math
    pts = [(d["n"], float(Fraction(d["max_gap"]))) for d in data if d["n"] >= 3]
    if len(pts) < 3:
        return ""
    shapes = models or [
        ("constant 4/3", None),
        ("1 + c/log2 n", lambda n: math.log2(n)),
        ("1 + c/sqrt(n)", lambda n: math.sqrt(n)),
        ("1 + c/n^(1/3)", lambda n: n ** (1.0 / 3.0)),
    ]
    ys = [g - 1.0 for _, g in pts]
    tot = sum(y * y for y in ys)
    out = ["fits of the per-length maximum, `gap - 1` against one parameter "
           "(`n >= 3`, %d points; empirical, floats used here and nowhere else):" % len(pts),
           "", "| model | c | residual SS / total SS | max abs residual |", "| --- | --- | --- | --- |"]
    for name, f in shapes:
        if f is None:
            c = sum(ys) / len(ys)  # least-squares constant on gap itself
            pred = [c for _ in ys]
            cc = c
        else:
            xs = [1.0 / f(n) for n, _ in pts]
            cc = sum(x * y for x, y in zip(xs, ys)) / sum(x * x for x in xs)
            pred = [cc * x for x in xs]
        res = sum((y - p) ** 2 for y, p in zip(ys, pred))
        mx = max(abs(y - p) for y, p in zip(ys, pred))
        out.append("| %s | %.4f | %.3f | %.4f |" % (name, cc, res / tot if tot else 0.0, mx))
    out.append("")
    return "\n".join(out)


def _emit(lines, title, recs, args):
    """Append the markdown summary of one corpus to the report."""
    if not recs:
        lines.append("**%s**: no instances measured.\n" % title)
        return
    lines.append(summary_block(title, summarise(recs)))
    if args.factors:
        subs = sub_records(recs, "factors")
        if subs:
            lines.append(summary_block(
                title + " -- universe = every distinct factor (the definition-level "
                "instance, O(n^2) elements)", summarise(subs)))


if __name__ == "__main__":
    sys.exit(main())
