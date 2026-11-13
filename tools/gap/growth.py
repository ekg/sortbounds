"""growth.py -- extend the exhaustive measurement of gap(S) = gamma / LP* past n = 16.

WHAT THIS ADDS TO gap.py.  gap.py already measures one text exactly and prints a sweep;
this file is the batch instrument for the one question the brief asks: how far does the
maximum gap go, and does the trend look bounded?  It is exhaustive per length, parallel,
budgeted, and it reports "did not finish" rather than a bound it did not prove.

  python3 growth.py --scan 13,14,15,16,17 --jobs 14 --budget 3600 --json n17.json
  python3 growth.py --report n17.json            # the curve + the fits
  python3 growth.py --symmetry-check             # the invariance the search relies on

EVERY REPORTED GAP IS A CERTIFIED RATIONAL.  gamma comes from `Cover.exact_min_cover`
(exhaustive branch and bound, its answer re-checked against every row); LP* comes from
`Cover.lp`, which returns a primal-feasible x and a dual-feasible y of equal value, so
weak duality pins LP* (simplex.py).  Each text is screened by the two invariants that must
hold on every instance -- `LP* <= gamma` (the LP relaxes the integer program) and
`LP* >= delta` (the d_k/k counting bound of README.md SS1b) -- and by `gap >= 1`.  A
violation raises; it never becomes a data point.  `certify.py` re-verifies any instance we
report as a witness at the definition level (every distinct factor, every window), which is
strictly stronger than the node tuple the solver used.

RAY/ARCHIVE.  A per-length scan is independent of every other, so it is embarrassingly
parallel: `--jobs` worker processes over disjoint ranges of the 2^n texts.  Each chunk
returns only counts plus a witness per distinct gap value, so memory does not grow with
the sweep.  The scan prints its rate and asserts `count == 2^n` at the end; anything else
is reported as NOT FINISHED with the measured per-instance cost.

TIME INVARIANCES USED BY THE SEARCH (nested.py), VERIFIED HERE.  gap(rev S) = gap(S),
gap(complement S) = gap(S), and gap(S) is unchanged by any injective renaming of the
alphabet.  Reason: reversing the text maps position p to n-1-p and factor f to rev(f), and
C(rev f) = {n-1-p : p in C(f)}, so the two covering instances are isomorphic; renaming is a
bijection on factors.  `--symmetry-check` verifies both equalities by exact measurement on
every binary text n <= 10 and on a sample at larger n, so the beam search may quotient by
them.
"""

import argparse
import json
import multiprocessing as mp
import os
import sys
import time
from fractions import Fraction

from instance import TextInstance, text_str
from simplex import LPError

# the published exhaustive maximum for n <= 16, from docs/research/lp-gap.md SS3.1
PUBLISHED = {1: "1", 2: "1", 3: "1", 4: "1", 5: "1", 6: "1", 7: "6/5", 8: "9/7",
             9: "9/7", 10: "9/7", 11: "9/7", 12: "4/3", 13: "15/11", 14: "4/3",
             15: "4/3", 16: "4/3"}
BEST_KNOWN = Fraction(15, 11)


# --------------------------------------------------------------------------
# one text, lean path, with the invariants asserted
# --------------------------------------------------------------------------


def measure_text(sym, verify_sample=False):
    """(gap, gamma, lp_value, delta, #distinct factors) of one text, with the invariants.

    `verify_sample` also runs the O(n^2) definition-level attractor verifier -- the sweep
    runs it on a sample instead of on all 2^n texts, because it is pure re-checking and
    the exact search already re-checks its own answer against every row.
    """
    ti = TextInstance(sym)
    cov = ti.nodes
    gamma, positions = cov.exact_min_cover()
    lp = cov.lp()
    if lp.value <= 0:
        raise AssertionError("LP* = %s <= 0 on the nonempty text %r"
                             % (lp.value, text_str(ti.sym)))
    if lp.value > gamma:
        raise AssertionError("LP* = %s > gamma = %s on %r"
                             % (lp.value, gamma, text_str(ti.sym)))
    delta = ti.delta()
    if lp.value < delta:
        raise AssertionError("LP* = %s < delta = %s on %r"
                             % (lp.value, delta, text_str(ti.sym)))
    gap = Fraction(gamma) / lp.value
    if gap < 1:
        raise AssertionError("gap = %s < 1 on %r" % (gap, text_str(ti.sym)))
    if verify_sample:
        miss = ti.verify_factor_cover(positions)
        if miss is not None:
            raise AssertionError("the attractor %r of %r misses the factor %r at %d"
                                 % (positions, text_str(ti.sym), miss[0], miss[1]))
    return gap, gamma, lp.value, delta, sum(ti.dk(k) for k in range(1, ti.n + 1))


def _syms_worker(block):
    """Measure an explicit list of texts; returns [(gap str, gamma, lp str), ...]."""
    out = []
    for sym in block:
        gap, gamma, lp, _, nfac = measure_text(sym)
        out.append((str(gap), gamma, str(lp), nfac))
    return out


def measure_syms(syms, jobs=1, block=8):
    """(gap, gamma, lp, #factors) for each text of `syms`, in order.  Exact, screened.

    The batch path for the targeted search: same `measure_text` (hence the same
    invariants and the same exact branch and bound + certified LP) as the exhaustive
    sweep, so a search result is as certified as a sweep result.  Results come back in
    input order, so a caller can zip them against its own beam.
    """
    syms = [list(s) for s in syms]
    assert syms, "measure_syms called with no texts"
    blocks = [syms[i:i + block] for i in range(0, len(syms), block)]
    if jobs <= 1 or len(blocks) == 1:
        pieces = [_syms_worker(b) for b in blocks]
    else:
        ctx = mp.get_context("fork")
        with ctx.Pool(min(jobs, len(blocks))) as pool:
            pieces = list(pool.imap(_syms_worker, blocks))
    out = [x for piece in pieces for x in piece]
    if len(out) != len(syms):
        raise AssertionError("measure_syms returned %d results for %d texts"
                             % (len(out), len(syms)))
    return out


def _chunk_worker(job):
    """Measure a block of texts; return counts plus one witness per distinct gap value.

    `job` = (base, size, n, verify_first).  The texts are the `size` integers starting at
    `base`, read as n-bit binary strings (so the sweep covers each of the 2^n texts once).
    Returning witnesses keyed by the exact gap keeps the parent's memory bounded by the
    number of distinct gap values, not by the number of texts.
    """
    base, size, n, verify_first = job
    count = 0
    hist = {}
    witness = {}
    above = []
    for t in range(base, base + size):
        assert 0 <= t < (1 << n), "text index %d outside 0..%d" % (t, (1 << n) - 1)
        sym = [(t >> (n - 1 - i)) & 1 for i in range(n)]
        gap, gamma, lp, _, _ = measure_text(
            sym, verify_sample=(verify_first and count == 0))
        key = str(gap)
        count += 1
        hist[key] = hist.get(key, 0) + 1
        if key not in witness:
            witness[key] = [text_str(sym), gamma, str(lp)]
        if gap > BEST_KNOWN:
            above.append([key, text_str(sym), gamma, str(lp)])
    return count, hist, witness, above


# --------------------------------------------------------------------------
# the exhaustive per-length scan
# --------------------------------------------------------------------------


def scan_length(n, jobs=1, budget=None, chunk=None, progress_every=20000):
    """Max gap over ALL 2^n binary texts of length n.  Exact, exhaustive, budgeted.

    Returns a dict whose `finished` flag is the honest answer to "did the sweep complete":
    True only if all 2^n texts were measured, in which case `max_gap` is the TRUE maximum
    for that length.  If the budget expired the dict says `finished: False` and reports
    how far it got -- no bound, no maximum.
    """
    total = 1 << n
    if chunk is None:
        chunk = max(256, min(8192, total // (jobs * 8) or 256))
    ranges = [(b, min(chunk, total - b), n, b == 0) for b in range(0, total, chunk)]
    assert sum(s for _, s, _, _ in ranges) == total, "the chunking lost texts"
    t0 = time.monotonic()
    count = 0
    hist = {}
    witness = {}
    above = []
    finished = False
    deadline = None if budget is None else t0 + budget
    if jobs <= 1:
        it = (_chunk_worker(j) for j in ranges)
        pool = None
    else:
        ctx = mp.get_context("fork")
        pool = ctx.Pool(jobs)
        it = pool.imap_unordered(_chunk_worker, ranges)
    try:
        for piece in it:
            c, h, w, a = piece
            assert c > 0, "empty chunk"
            count += c
            for k, v in h.items():
                hist[k] = hist.get(k, 0) + v
            for k, v in w.items():
                witness.setdefault(k, v)
            above.extend(a)
            if count % progress_every < c:
                dt = time.monotonic() - t0
                print("  n=%d: %d/%d texts, %.1fs, max so far %s"
                      % (n, count, total, dt, max((Fraction(k) for k in hist), default=1)),
                      file=sys.stderr, flush=True)
            if deadline is not None and time.monotonic() > deadline:
                print("  n=%d: budget of %.0fs reached after %d/%d texts"
                      % (n, budget, count, total), file=sys.stderr, flush=True)
                break
    finally:
        if pool is not None:
            pool.terminate()
            pool.join()
    dt = time.monotonic() - t0
    if count == total:
        finished = True
    max_gap = max((Fraction(k) for k in hist), default=Fraction(0))
    return {
        "n": n,
        "texts": total,
        "measured": count,
        "finished": finished,
        "max_gap": str(max_gap),
        "argmax_texts": sorted(t for k, (t, _, _) in witness.items()
                               if Fraction(k) == max_gap),
        "argmax_witness": [v for k, v in sorted(witness.items(),
                                                key=lambda kv: -Fraction(kv[0]))
                           if Fraction(k) == max_gap][:4],
        "num_gt_one": sum(v for k, v in hist.items() if Fraction(k) > 1),
        "num_at_best_known": hist.get(str(BEST_KNOWN), 0),
        "num_above_best_known": len(above),
        "above_best_known": above[:20],
        "histogram": sorted(((k, v) for k, v in hist.items()),
                            key=lambda kv: -Fraction(kv[0])),
        "witness_by_gap": {k: witness[k] for k in
                           sorted(witness, key=lambda k: -Fraction(k))},
        "seconds": round(dt, 1),
        "ms_per_text": round(1000.0 * dt / max(1, count), 3),
        "budget": budget,
    }


# --------------------------------------------------------------------------
# the growth verdict: fits of the per-length maximum
# --------------------------------------------------------------------------


def fit_curve(points, n_max=None):
    """Least-squares one-parameter fits of `gap(n) - 1`; floats, descriptive only.

    The same four shapes the earlier note used, so the new point can be read against the
    old table: a bounded constant, `1 + c/log2 n`, `1 + c/sqrt n`, `1 + c/n^(1/3)`.  Every
    candidate decays except the constant, so the *prediction at a larger n* separates them:
    a single instance above a decaying model's prediction falsifies that model.  No bound
    in this file is derived from these numbers.
    """
    import math
    pts = [(n, float(Fraction(g))) for n, g in points if n >= 3 and (n_max is None or n <= n_max)]
    if len(pts) < 3:
        return None
    ys = [g - 1.0 for _, g in pts]
    tot = sum(y * y for y in ys)
    shapes = [("bounded constant", None),
              ("1 + c/log2 n", lambda n: math.log2(n)),
              ("1 + c/sqrt(n)", lambda n: math.sqrt(n)),
              ("1 + c/n^(1/3)", lambda n: n ** (1.0 / 3.0))]
    out = []
    for name, f in shapes:
        if f is None:
            c = sum(ys) / len(ys)
            pred = [c for _ in ys]
        else:
            xs = [1.0 / f(n) for n, _ in pts]
            denom = sum(x * x for x in xs)
            assert denom > 0, "degenerate fit for %s" % name
            c = sum(x * y for x, y in zip(xs, ys)) / denom
            pred = [c * x for x in xs]
        res = sum((y - p) ** 2 for y, p in zip(ys, pred))
        mx = max(abs(y - p) for y, p in zip(ys, pred))
        if f is None:
            predicts = {"64": c + 1, "128": c + 1, "1024": c + 1}
        else:
            predicts = {str(m): 1.0 + c / f(m) for m in (64, 128, 1024)}
        out.append({"model": name, "c": c, "rss_over_tss": res / tot if tot else 0.0,
                    "max_abs_residual": mx, "predicts": predicts})
    return {"n_points": len(pts), "models": out}


def verdict(points, n_exhausted):
    """The falsifiable statement, and the comparison with each model's predictions.

    A "verdict" here is only ever one of: (a) the maximum over the exhaustive range, with
    the range named; (b) a statement of the form "no instance with gap > B was found over
    N_exhaustive lengths and M searched texts, so if the maximum were to exceed B it would
    first do so at n > ..." -- always with its scope attached.
    """
    got = {n: Fraction(g) for n, g in points}
    mx = max(got.values())
    at = sorted(n for n, g in got.items() if g == mx)
    L = []
    L.append("Exhaustive range: every binary text with n <= %d (%d texts of length %d "
             "alone)." % (n_exhausted, 2 ** n_exhausted, n_exhausted))
    L.append("Maximum over that range: **%s** (%.4f), first attained at n = %d."
             % (mx, float(mx), at[0]))
    L.append("Per-length maxima for n = %s: %s."
             % (", ".join(str(n) for n in sorted(got)),
                ", ".join(str(got[n]) for n in sorted(got))))
    return "\n".join(L), mx, at


# --------------------------------------------------------------------------
# the symmetry the search quotients by
# --------------------------------------------------------------------------


def symmetry_check(max_n=10, samples=0, seed=7):
    """gap(S) = gap(rev S) = gap(complement S), measured exactly on a corpus.

    Needed by nested.py, which explores each text only up to reversal and complement.
    """
    import random
    from instance import binary_strings
    rng = random.Random(seed)
    checked = 0
    t0 = time.monotonic()
    for sym in binary_strings(max_n):
        g0 = measure_text(sym)[0]
        for other in (list(reversed(sym)), [1 - c for c in sym],
                      [1 - c for c in reversed(sym)]):
            g1 = measure_text(other)[0]
            if g1 != g0:
                raise AssertionError("gap is not invariant on %r: %s vs %s on %r"
                                     % (text_str(sym), g0, g1, text_str(other)))
        checked += 1
        assert checked > 0
    for _ in range(samples):
        n = rng.randrange(11, 21)
        sym = [rng.randrange(2) for _ in range(n)]
        g0 = measure_text(sym)[0]
        g1 = measure_text(list(reversed(sym)))[0]
        g2 = measure_text([1 - c for c in sym])[0]
        if not (g0 == g1 == g2):
            raise AssertionError("gap is not invariant on %r: %s %s %s"
                                 % (text_str(sym), g0, g1, g2))
        checked += 1
        assert checked > 0
    return checked, time.monotonic() - t0


# --------------------------------------------------------------------------
# the report
# --------------------------------------------------------------------------


def curve_table(records, exhaustive_upto):
    L = ["| n | texts | exhaustive? | max gap | ≈ | # gap > 1 | argmax text | "
         "(gamma, LP*) | seconds |", "| --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    for r in sorted(records, key=lambda r: r["n"]):
        w = r["argmax_witness"][0] if r["argmax_witness"] else ["?", "?", "?"]
        L.append("| %d | %d | %s | **%s** | %.4f | %d | `%s` | (%s, %s) | %s |"
                 % (r["n"], r["measured"],
                    "yes" if r["finished"] else "NO (%d/%d)" % (r["measured"], r["texts"]),
                    r["max_gap"], float(Fraction(r["max_gap"])), r["num_gt_one"],
                    w[0], w[1], w[2], r["seconds"]))
    return "\n".join(L)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--scan", default="", help="comma-separated lengths to sweep exhaustively")
    ap.add_argument("--jobs", type=int, default=1, help="worker processes (default 1)")
    ap.add_argument("--budget", type=float, default=0.0,
                    help="wall-clock budget PER LENGTH in seconds, 0 = unlimited")
    ap.add_argument("--total-budget", type=float, default=0.0,
                    help="wall-clock budget for the whole run, 0 = unlimited")
    ap.add_argument("--chunk", type=int, default=0, help="texts per work item")
    ap.add_argument("--json", default="", help="write the per-length records here")
    ap.add_argument("--report", default="", help="print the curve from a JSON file")
    ap.add_argument("--symmetry-check", action="store_true",
                    help="verify gap(S) = gap(rev S) = gap(complement S) exactly")
    args = ap.parse_args(argv)
    if not (args.scan or args.report or args.symmetry_check):
        ap.error("nothing to do: pass --scan, --report or --symmetry-check")

    if args.symmetry_check:
        checked, dt = symmetry_check(samples=40)
        print("symmetry check: gap(S) = gap(rev S) = gap(~S) on %d texts "
              "(all binary n <= 10 plus 40 samples at n = 11..20), %.1fs" % (checked, dt))

    if args.report:
        with open(args.report) as f:
            recs = json.load(f)["lengths"]
        recs = [r for r in recs if r["measured"]]
        ex = max((r["n"] for r in recs if r["finished"]), default=0)
        print(curve_table(recs, ex))
        print("")
        pts = [(r["n"], r["max_gap"]) for r in recs if r["finished"]]
        text, mx, at = verdict(pts, ex)
        print(text)
        print("")
        for k in ("all", "up_to_16"):
            lim = None if k == "all" else 16
            fit = fit_curve(pts, lim)
            if fit is None:
                continue
            print("fits of `gap - 1`, points n = 3..%s (%d points), descriptive only:"
                  % ("%d" % max(n for n, _ in pts) if lim is None else "16", fit["n_points"]))
            print("")
            print("| model | c | residual SS / total SS | max abs residual | predicts n=64 "
                  "| n=128 | n=1024 |")
            print("| --- | --- | --- | --- | --- | --- | --- |")
            for m in fit["models"]:
                print("| %s | %.4f | %.3f | %.4f | %.4f | %.4f | %.4f |"
                      % (m["model"], m["c"], m["rss_over_tss"], m["max_abs_residual"],
                         m["predicts"]["64"], m["predicts"]["128"], m["predicts"]["1024"]))
            print("")
        return 0

    recs = []
    t0 = time.monotonic()
    for n in [int(t) for t in args.scan.split(",") if t.strip()]:
        if args.total_budget and time.monotonic() - t0 > args.total_budget:
            print("total budget reached before n=%d" % n, file=sys.stderr)
            break
        budget = args.budget or None
        if args.total_budget:
            left = args.total_budget - (time.monotonic() - t0)
            budget = left if budget is None else min(budget, left)
        print("scanning all 2^%d = %d binary texts of length %d (jobs=%d, budget=%s)"
              % (n, 1 << n, n, args.jobs, budget), file=sys.stderr, flush=True)
        rec = scan_length(n, jobs=args.jobs, budget=budget,
                          chunk=args.chunk or None)
        recs.append(rec)
        print("  n=%d: %s in %.1fs, %d/%d texts, max gap %s, %d with gap > 1"
              % (n, "FINISHED" if rec["finished"] else "NOT FINISHED",
                 rec["seconds"], rec["measured"], rec["texts"], rec["max_gap"],
                 rec["num_gt_one"]), file=sys.stderr, flush=True)
        if not rec["finished"]:
            print("  n=%d did not finish: %.3f ms/text measured, so the full sweep needs "
                  "about %.0f s at this rate" % (n, rec["ms_per_text"],
                                                 rec["ms_per_text"] * rec["texts"] / 1000.0),
                  file=sys.stderr, flush=True)
        rec["published_max_gap"] = PUBLISHED.get(n)
        if rec["finished"] and n in PUBLISHED and rec["max_gap"] != PUBLISHED[n]:
            raise AssertionError("n=%d: this run's maximum %s disagrees with the "
                                 "published %s" % (n, rec["max_gap"], PUBLISHED[n]))
    if args.json:
        with open(args.json, "w") as f:
            json.dump({"lengths": recs, "best_known": str(BEST_KNOWN),
                       "seconds": round(time.monotonic() - t0, 1)}, f, indent=1)
        print("wrote %s" % args.json, file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
