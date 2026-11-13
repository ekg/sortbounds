"""nested.py -- the targeted search for an instance beating 15/11, n = 17 .. 40.

WHY A SEARCH AND NOT A SWEEP.  2^40 texts cannot be swept with an exact rational LP per
text (the n = 17 sweep alone is 1.3 * 10^5 instances in ~2.5 min on 14 cores).  So past
the exhaustive range the question becomes: does any text have gap > 15/11?  This file
attacks it with two independent searches, and reports their scope exactly -- how many
instances were measured, at which lengths, from which seeds.  A negative answer is
"no instance above 15/11 among the N instances measured, exhaustive at n <= 17"; it is
*not* a proof, and every table it prints says so.

SEARCH 1 -- NESTED EXTENSION OF THE KNOWN EXTREMAL TEXTS (the brief's arm).
  Seeds: the four n = 13 texts with gap 15/11, the four n = 12 texts with gap 4/3, and
  (optionally) the argmax texts of an exhaustive sweep, read from growth.py's JSON.
  Moves, one symbol at a time: insert 0 or 1 at ANY position (n+1 positions, so a text has
  2(n+1) one-symbol supersets).  Past `--insert-upto` the move set narrows to the four
  END extensions (append/prepend 0/1), because the number of children grows with n and the
  LP is what costs.
  Because the gap is NOT monotone under extension (n = 13 has 15/11, n = 14 does not),
  a greedy "keep only what beats 15/11" walk dies at the first step.  So this is a BEAM:
  at every length the best `--width` texts survive, ordered by gap and then by
  (number of distinct factors, canonical form) -- the second key is a deterministic
  tie-break that prefers repetitive texts, which is the structure the extremal texts have
  ("short repeated factors").  The beam is a heuristic; the *measurements* are exact.

  Symmetries quotiented out (verified by `growth.py --symmetry-check`): gap is invariant
  under reversal, complement and alphabet renaming, so each text is replaced by the least
  of {S, rev S, ~S, ~rev S}.  That is a factor-4 saving in the number of instances
  measured and loses no distinct gap value.

SEARCH 2 -- STRUCTURED FAMILIES (the brief's second arm).
  The extremal texts are repetitive, so at every length n = 17..40 this arm measures a
  deterministic corpus of 8 repetitive shapes: random run-length compositions (short and
  medium runs), periodic texts (a random block repeated), squares S S, S S^R, padded
  seeds S 0^m S, morphic prefixes (Fibonacci, Thue-Morse, period-doubling), and the
  n = 13 witness stretched by 0 -> 0^a, 1 -> 1^b.  All are generated from a fixed seed,
  so the corpus is reproducible; every instance is measured by the same certified path.

CERTIFICATES.  Every instance that beats 15/11 -- and the best instance found at every
length, whether or not it beats 15/11 -- is re-verified by certify.py at the definition
level (all distinct factors, every window) and printed with both vectors in full.  A
claimed gap that does not re-verify raises CertificateError instead of being reported.

  timeout 3600 python3 nested.py --nmax 40 --jobs 14 --width 512 --json nested.json
"""

import argparse
import json
import random
import sys
import time
from fractions import Fraction

from certify import certificate_block
from growth import BEST_KNOWN, measure_syms
from instance import TextInstance, text_str

# the extremal texts the earlier exhaustive sweeps found, spelled out
WITNESSES_13 = ["0110101101110", "0111011010110", "1000100101001", "1001010010001"]
WITNESSES_12 = ["001010010001", "011101101011", "100010010100", "110101101110"]


# --------------------------------------------------------------------------
# symmetry: canonical form of a binary text
# --------------------------------------------------------------------------


def canonical(sym):
    """The least of {S, rev S, ~S, ~rev S} -- the symmetry class of the text.

    gap(S) = gap(rev S) = gap(~S), exactly, because reversal is an isomorphism of the
    covering instance (p -> n-1-p, f -> rev f, C(rev f) = {n-1-p : p in C(f)}) and symbol
    complement is a bijection on factors.  Verified by growth.py --symmetry-check.
    """
    s = tuple(sym)
    r = s[::-1]
    c = tuple(1 - x for x in s)
    cr = c[::-1]
    return min(s, r, c, cr)


def end_extensions(sym):
    """The four one-symbol supersets that add a symbol at an end."""
    s = list(sym)
    return ([[0] + s, [1] + s, s + [0], s + [1]])


def all_insertions(sym):
    """Every one-symbol superset: insert 0 or 1 at each of the n+1 gaps.  2(n+1) texts."""
    s = list(sym)
    out = []
    for c in (0, 1):
        for i in range(len(s) + 1):
            out.append(s[:i] + [c] + s[i:])
    return out


# --------------------------------------------------------------------------
# the beam
# --------------------------------------------------------------------------


def _rank(item):
    """Beam order: largest gap first, then fewest distinct factors, then canonical form.

    Deterministic, so a rerun reproduces the beam exactly.  The tie-breaks are heuristic
    (they pick which equally-good texts to keep exploring); they never affect a reported
    gap value, which is always a measured exact rational.
    """
    gap, nfac, canon = item
    return (-gap, nfac, canon)


def beam_search(seeds, nmax, width_at, jobs=1, insert_upto=20, log=print):
    """Grow a beam of texts from `seeds` to length `nmax`; returns per-length records.

    Every record carries the entries actually measured at that length: how many, the
    maximum gap, the argmax text, and every instance that beat 15/11.
    """
    beam = []
    seen = set()
    for s in seeds:
        c = canonical(s)
        if c in seen:
            continue
        seen.add(c)
        beam.append(list(s))
    if not beam:
        raise ValueError("beam_search needs at least one seed")
    n0 = len(beam[0])
    if any(len(s) != n0 for s in beam):
        raise ValueError("seeds must all have the same length")
    records = []
    hits = []
    t0 = time.monotonic()
    for n in range(n0 + 1, nmax + 1):
        t_level = time.monotonic()
        cands = []
        seen = set()
        for s in beam:
            kids = all_insertions(s) if n <= insert_upto else end_extensions(s)
            for t in kids:
                c = canonical(t)
                if c in seen:
                    continue
                seen.add(c)
                cands.append(t)
        assert cands, "the beam produced no candidates at n=%d" % n
        res = measure_syms(cands, jobs=jobs)
        if len(res) != len(cands):
            raise AssertionError("measured %d of %d candidates at n=%d"
                                 % (len(res), len(cands), n))
        ranked = []
        best = (Fraction(0), None, None, None)
        level_hits = []
        num_at_best = 0
        for sym, (gap_s, gamma, lp_s, nfac) in zip(cands, res):
            gap = Fraction(gap_s)
            ranked.append((gap, nfac, tuple(sym), sym))
            if gap > best[0]:
                best = (gap, sym, gamma, lp_s)
            if gap >= BEST_KNOWN:
                num_at_best += 1
                if len(level_hits) < 4:          # keep a sample; count them all
                    level_hits.append({"n": n, "text": text_str(sym), "gap": gap_s,
                                       "gamma": gamma, "lp": lp_s})
        hits.extend(level_hits)
        ranked.sort(key=lambda r: (-r[0], r[1], r[2]))
        width = width_at(n)
        beam = [r[3] for r in ranked[:width]]
        rec = {
            "n": n, "candidates": len(cands), "beam": len(beam), "width": width,
            "max_gap": str(best[0]), "argmax_text": text_str(best[1]),
            "argmax_gamma": best[2], "argmax_lp": best[3],
            "num_gt_one": sum(1 for r in ranked if r[0] > 1),
            "num_at_best_known": num_at_best,
            "num_above_best_known": sum(1 for r in ranked if r[0] > BEST_KNOWN),
            "seconds": round(time.monotonic() - t_level, 1),
        }
        records.append(rec)
        log("  beam n=%2d: %5d candidates, max %-6s (%.4f) `%s` gamma=%s LP*=%s, "
            "%d at/above %s, %.1fs"
            % (n, len(cands), best[0], float(best[0]), text_str(best[1]), best[2],
               best[3], num_at_best, BEST_KNOWN, rec["seconds"]))
        assert rec["max_gap"] is not None
    log("  beam total %.1fs, %d candidate(s) measured, %d instance(s) at or above %s"
        % (time.monotonic() - t0, sum(r["candidates"] for r in records), len(hits),
           BEST_KNOWN))
    return records, hits


# --------------------------------------------------------------------------
# the extremal chase: how far does the 15/11 class itself extend?
# --------------------------------------------------------------------------


def _dedupe(texts):
    """Texts, one representative per reversal/complement class, in input order."""
    out = []
    seen = set()
    for t in texts:
        c = canonical(t)
        if c in seen:
            continue
        seen.add(c)
        out.append(t)
    return out


def extremal_chase(seeds, nmax, width=64, jobs=1, log=print):
    """Grow ONLY the texts at the current maximum gap, by one-symbol insertion.

    A beam keeps the best `width` texts whether or not they are extremal, which buys
    diversity but spends most of its measurements on texts far below the maximum.  This
    arm asks the sharp question instead: from the extremal texts at length n, is there a
    one-symbol insertion that is extremal at length n+1?  If the answer is no at length
    n+1 the class has died *along this path* (stated as such -- other paths may reach a
    text with the same gap, and the beam arm is the evidence for that).

    Returns per-length records with the exact best gap, the number of extremal texts found
    and up to three of them, plus every text at gap >= 15/11 for certification.
    """
    parents = _dedupe([list(s) for s in seeds])
    if not parents:
        raise ValueError("extremal_chase needs a seed")
    n0 = len(parents[0])
    if any(len(p) != n0 for p in parents):
        raise ValueError("seeds must all have the same length")
    recs = []
    top = []
    t0 = time.monotonic()
    for n in range(n0 + 1, nmax + 1):
        t_level = time.monotonic()
        cands = _dedupe([t for p in parents for t in all_insertions(p)])
        assert cands, "the chase produced no candidates at n=%d" % n
        res = measure_syms(cands, jobs=jobs)
        rows = []
        at_best = []
        best = Fraction(0)
        best_sym = None
        for sym, (gap_s, gamma, lp_s, nfac) in zip(cands, res):
            gap = Fraction(gap_s)
            rows.append((gap, nfac, tuple(sym), sym))
            if gap > best:
                best, best_sym = gap, (sym, gamma, lp_s)
        rows.sort(key=lambda r: (-r[0], r[1], r[2]))
        for r in rows:
            if r[0] < best:
                break
            if len(at_best) < width:
                at_best.append(r[3])
        level_top = [r for r in rows if r[0] >= BEST_KNOWN][:4]
        for r in level_top:
            top.append({"n": n, "text": text_str(r[3]), "gap": str(r[0])})
        parents = at_best
        recs.append({
            "n": n, "candidates": len(cands), "parents": len(parents),
            "max_gap": str(best), "argmax_text": text_str(best_sym[0]),
            "num_at_max": sum(1 for r in rows if r[0] == best),
            "holds_15_11": best >= BEST_KNOWN,
            "examples": [text_str(r[3]) for r in rows[:3]],
            "seconds": round(time.monotonic() - t_level, 1),
        })
        log("  chase n=%2d: %4d insertions, max %-6s `%s`, %d extremal text(s), %s"
            % (n, len(cands), best, text_str(best_sym[0]),
               recs[-1]["num_at_max"], "holds" if best >= BEST_KNOWN else "BELOW 15/11"))
        assert recs[-1]["max_gap"] is not None
    log("  chase total %.1fs" % (time.monotonic() - t0))
    return recs, top


# --------------------------------------------------------------------------
# the structured corpus
# --------------------------------------------------------------------------


def _fib_prefix(n):
    """Prefix of length n of the Fibonacci word: the fixed point of 0 -> 01, 1 -> 0."""
    a, b = [0], [0, 1]
    while len(b) < n:
        a, b = b, b + a
    return b[:n]


def _tm_prefix(n):
    """Prefix of length n of the Thue-Morse word: the fixed point of 0 -> 01, 1 -> 10."""
    t = [0]
    while len(t) < n:
        t = t + [1 - c for c in t]
    return t[:n]


def _period_doubling(n):
    """Prefix of length n of the period-doubling word: 0 -> 01, 1 -> 00."""
    t = [0]
    while len(t) < n:
        t = [b for c in t for b in ((0, 1) if c == 0 else (0, 0))]
    return t[:n]


def structured_corpus(n, per_family=64, seed=2026):
    """Deterministic repetitive texts of length n: the shapes the extremal texts have.

    Eight families, each `per_family` texts: random run-length compositions (runs of
    length 1..2, and of length 1..4), periodic texts (a random block repeated to length
    n), squares S S, mirror squares S S^R, padded seeds S 0^m S, the witness stretched by
    0 -> 0^a, 1 -> 1^b, and morphic prefixes.  Fixed seed => the same corpus every run.
    """
    rng = random.Random(seed * 100000 + n)
    out = []

    def runs(maxrun):
        sym = [rng.randrange(2)]
        while len(sym) < n:
            r = rng.randrange(1, maxrun + 1)
            sym.extend([1 - sym[-1]] * r)
        return sym[:n]

    for _ in range(per_family):
        out.append(runs(2))
    for _ in range(per_family):
        out.append(runs(4))

    # periodic: a random block of length p, repeated and truncated
    for _ in range(per_family):
        p = rng.randrange(2, max(3, min(n, 12)))
        block = [rng.randrange(2) for _ in range(p)]
        out.append((block * (n // p + 1))[:n])

    # squares and mirror squares of a random half
    for _ in range(per_family):
        h = (n + 1) // 2
        half = [rng.randrange(2) for _ in range(h)]
        out.append((half + half)[:n])
    for _ in range(per_family):
        h = (n + 1) // 2
        half = [rng.randrange(2) for _ in range(h)]
        out.append((half + half[::-1])[:n])

    # padded seeds S 0^m S: the shape that keeps a short repeated factor in the middle
    for _ in range(per_family):
        m = rng.randrange(1, 5)
        h = max(1, (n - m) // 2)
        block = [rng.randrange(2) for _ in range(h)]
        sym = block + [0] * m + block
        out.append((sym + block * (n // max(1, len(block)) + 1))[:n])

    # the n=13 witness stretched by 0 -> 0^a, 1 -> 1^b, then truncated / repeated
    w = [int(c) for c in WITNESSES_13[0]]
    for _ in range(per_family):
        a, b = rng.randrange(1, 4), rng.randrange(1, 4)
        sym = []
        for c in w:
            sym.extend([c] * (a if c == 0 else b))
        while len(sym) < n:
            sym = sym + sym
        out.append(sym[:n])

    # morphic prefixes
    out.extend(_fib_prefix(n) for _ in range(per_family // 4))
    out.extend(_tm_prefix(n) for _ in range(per_family // 4))
    out.extend(_period_doubling(n) for _ in range(per_family // 4))

    fixed = []
    for s in out:
        if len(s) != n:
            raise AssertionError("structured corpus produced length %d, wanted %d"
                                 % (len(s), n))
        fixed.append(s)
    return fixed


def structured_search(ns, jobs=1, per_family=64, log=print):
    """Measure the structured corpus at every requested length; per-length records."""
    records = []
    hits = []
    for n in ns:
        t0 = time.monotonic()
        corpus = structured_corpus(n, per_family=per_family)
        seen = set()
        texts = []
        for s in corpus:
            c = canonical(s)
            if c in seen:
                continue
            seen.add(c)
            texts.append(s)
        res = measure_syms(texts, jobs=jobs)
        best = (Fraction(0), None, None, None)
        cnt_gt1 = 0
        for sym, (gap_s, gamma, lp_s, nfac) in zip(texts, res):
            gap = Fraction(gap_s)
            if gap > 1:
                cnt_gt1 += 1
            if gap > best[0]:
                best = (gap, sym, gamma, lp_s)
            if gap >= BEST_KNOWN:
                hits.append({"n": n, "text": text_str(sym), "gap": gap_s,
                             "gamma": gamma, "lp": lp_s})
        records.append({
            "n": n, "measured": len(texts), "max_gap": str(best[0]),
            "argmax_text": text_str(best[1]), "argmax_gamma": best[2],
            "argmax_lp": best[3], "num_gt_one": cnt_gt1,
            "seconds": round(time.monotonic() - t0, 1),
        })
        log("  struct n=%2d: %4d texts, max %-6s (%.4f) `%s`, %d with gap > 1, %.1fs"
            % (n, len(texts), best[0], float(best[0]), text_str(best[1]), cnt_gt1,
               records[-1]["seconds"]))
        assert records[-1]["max_gap"] is not None
    return records, hits


# --------------------------------------------------------------------------
# certificates for the instances worth printing
# --------------------------------------------------------------------------


def certificate_for(text, log=print):
    """The full certificate of one text, re-verified at the definition level."""
    from simplex import cover_lp
    ti = TextInstance([int(c) for c in text] if isinstance(text, str) else list(text))
    cov = ti.nodes
    gamma, positions = cov.exact_min_cover()
    lp = cover_lp(cov.rows, cov.n)
    y = {lab: w for lab, w in zip(cov.labels, lp.y)}
    facts, block = certificate_block(text, positions, lp.x, y, lp.value)
    if facts["gamma"] != gamma:
        raise AssertionError("the certified gamma %d disagrees with the search's %d"
                             % (facts["gamma"], gamma))
    return facts, block


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--nmax", type=int, default=40)
    ap.add_argument("--nmin", type=int, default=17)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--width", type=int, default=512, help="beam width for n <= 20")
    ap.add_argument("--width-mid", type=int, default=256, help="beam width for n <= 30")
    ap.add_argument("--width-far", type=int, default=128, help="beam width above n = 30")
    ap.add_argument("--insert-upto", type=int, default=20,
                    help="use all-position insertion (2(n+1) children) up to this length")
    ap.add_argument("--per-family", type=int, default=64,
                    help="texts per structured family per length")
    ap.add_argument("--arms", default="chase,beam,struct",
                    help="comma list of chase, beam, struct")
    ap.add_argument("--chase-width", type=int, default=64,
                    help="how many extremal texts the chase carries forward")
    ap.add_argument("--budget", type=float, default=0.0,
                    help="wall-clock budget in seconds for the whole run, 0 = unlimited")
    ap.add_argument("--seed-texts", default="",
                    help="comma-separated texts to seed the chase with (default: the "
                         "n = 13 witnesses, or the beam's own extremal hits)")
    ap.add_argument("--json", default="")
    args = ap.parse_args(argv)
    t0 = time.monotonic()

    def log(msg):
        print(msg, file=sys.stderr, flush=True)

    def width_at(n):
        if n <= 20:
            return args.width
        if n <= 30:
            return args.width_mid
        return args.width_far

    records = {"chase": [], "beam": {}, "structured": [], "hits": []}
    arms = [a.strip() for a in args.arms.split(",") if a.strip()]
    if "beam" in arms:
        # two independent lineages, each a legal one-symbol-at-a-time extension chain:
        # the four n = 13 texts with gap 15/11, and the four n = 12 texts with gap 4/3
        for label, group, n0 in (("n=13_15/11", WITNESSES_13, 13),
                                 ("n=12_4/3", WITNESSES_12, 12)):
            seeds = [list(int(c) for c in t) for t in group]
            log("beam %s: %d seeds of length %d, growing to n = %d, width %d/%d/%d"
                % (label, len(seeds), n0, args.nmax, args.width, args.width_mid,
                   args.width_far))
            recs, hits = beam_search(seeds, args.nmax, width_at, jobs=args.jobs,
                                     insert_upto=args.insert_upto, log=log)
            records["beam"][label] = recs
            records["hits"] = records["hits"] + hits
    if "struct" in arms:
        ns = [n for n in range(args.nmin, args.nmax + 1)
              if not args.budget or time.monotonic() - t0 < args.budget]
        recs, hits = structured_search(ns, jobs=args.jobs, per_family=args.per_family,
                                      log=log)
        records["structured"] = recs
        records["hits"] = records["hits"] + hits

    if "chase" in arms:
        # grow ONLY the extremal texts, continuing from the best the beam found: this is
        # the "does the 15/11 class extend?" arm, seeded so that it starts from an
        # extremal text at the largest length reached rather than from n = 13
        by_n = {}
        for h in records["hits"]:
            if Fraction(h["gap"]) >= BEST_KNOWN:
                by_n.setdefault(h["n"], []).append(h["text"])
        if args.seed_texts:
            seeds = [[int(c) for c in t] for t in args.seed_texts.split(",") if t]
            by_n = {len(seeds[0]): [text_str(s) for s in seeds]}
        if by_n:
            n0 = max(by_n)
            seeds = [[int(c) for c in t] for t in by_n[n0]]
        else:
            n0 = 13
            seeds = [list(int(c) for c in t) for t in WITNESSES_13]
        log("chase: %d extremal seed(s) of length %d (gap >= %s), grown to n = %d"
            % (len(seeds), n0, BEST_KNOWN, args.nmax))
        recs, hits = extremal_chase(seeds, args.nmax, width=args.chase_width,
                                    jobs=args.jobs, log=log)
        records["chase"] = recs
        records["hits"] = records["hits"] + hits

    # the best text overall, and its full certificate
    allrecs = [(r["n"], r["max_gap"], r["argmax_text"])
               for arm in records["beam"].values() for r in arm]
    allrecs += [(r["n"], r["max_gap"], r["argmax_text"]) for r in records["structured"]]
    allrecs += [(r["n"], r["max_gap"], r["argmax_text"]) for r in records["chase"]]
    best = max(allrecs, key=lambda t: (Fraction(t[1]), t[0])) if allrecs else None
    records["best"] = ({"n": best[0], "gap": best[1], "text": best[2]} if best else None)
    if best:
        facts, block = certificate_for(best[2], log=log)
        print("")
        print("### The best instance found above the exhaustive range (n = %d)" % best[0])
        print("")
        print("```")
        print(block.strip("`\n"))
        print("```")
    # every instance the search put at or above 15/11, certified one by one; the ones
    # ABOVE 15/11 are the deliverable the brief asks for, so they are printed first
    seen_hit = set()
    hits = []
    for h in sorted(records["hits"], key=lambda h: (-Fraction(h["gap"]), -h["n"])):
        key = (h["n"], h["text"])
        if key in seen_hit:
            continue
        seen_hit.add(key)
        hits.append(h)
    for h in hits[:12]:
        print("")
        print("### An instance at gap %s found by the search (n = %d)" % (h["gap"], h["n"]))
        print("")
        facts, block = certificate_for(h["text"], log=log)
        print(block)
    records["hits"] = hits
    records["seconds"] = round(time.monotonic() - t0, 1)
    if args.json:
        with open(args.json, "w") as f:
            json.dump(records, f, indent=1)
        log("wrote %s" % args.json)
    log("done in %.1fs" % records["seconds"])
    return records


if __name__ == "__main__":
    sys.exit(0 if main() is not None else 1)
