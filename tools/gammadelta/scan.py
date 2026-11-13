#!/usr/bin/env python3
"""scan.py -- how large does gamma - ceil(delta) get on binary text, n = 20..64?

THE QUESTION (open problem 2 of docs/research/RESULTS.md).  `delta <= gamma` is a theorem
(SortBounds/Projects/Repetitiveness), so `gap(S) = gamma(S) - ceil(delta(S))` is a
non-negative integer; `delta` is computable in O(n) from the suffix array while `gamma` is
NP-hard.  Every measurement before this lane had `gap <= 2` for n <= 18 and `gap = 3` at a
single kernel-checked n = 32 instance (`Packing.lean`, `s32`).  Does the maximum grow?

WHAT IS CERTIFIED IN EVERY ROW.  Nothing here re-implements gamma or delta:

  * `delta(S)` exact, as a `Fraction`, from `tools/attractor/instance.py::Instance.delta`
    (repmeter's `delta_exact`);
  * `ub` -- a *verified* attractor: `Instance.witness` (the definition-level checker) must
    return None, so `gamma <= ub`;
  * `lb` -- one of three independently checkable certificates: `ceil(delta)`, a packing
    family of factors whose crossing-position sets are pairwise disjoint (each such factor
    forces its own position, so `gamma >= family size`, re-checked from the text by
    `Instance.certify_packing`), or a completed DFS at `k = lb-1` proving no attractor that
    small exists (`anytime.search`, `lb_source = "exact tail"`).

Hence `gap in [lb - ceil(delta), ub - ceil(delta)]`, both endpoints certified, and the row is
a point only when the bracket closes (`lb == ub`).

THE TWO DIRECTIONS THE SWEEP MEASURES.

  * lower: `--search` / `--local` hunt for instances with a large *certified* lower bound
    `lb - ceil(delta)` (and, as a tie-break, a large `ub - ceil(delta)`), over the families
    of the brief plus the "alternating run lengths" family that produced the record;
  * upper: `--exhaustive N` evaluates *every* binary text of length N and reports
    `max over S of (ub(S) - ceil(delta(S)))`, which is a certified upper bound on the maximum
    gap at that length for *all* texts (no search, no sampling).

INCREMENTAL OUTPUT.  The driver (this process) is the only writer.  Every interesting row is
appended to `results.jsonl` and the merged `results.json` (per-length best, the curve, the
exhaustive summaries) is rewritten after every improvement, so a crash or a timeout loses at
most one instance.

USAGE

  python3 scan.py --exhaustive 20,21,22 --workers 6 --json results.json
  python3 scan.py --search --ns 20,24,28,32,40,48,64 --workers 6 --iters 400 --json results.json
  python3 scan.py --local --ns 32,40,48,64 --workers 6 --iters 2000 --json results.json
  python3 scan.py --bracket --texts-from results.json --budget 120 --workers 6 --json results.json
  python3 scan.py --report --json results.json

stdlib only; every loop asserts progress; `--deadline` bounds the driver, each worker task is
bounded by `--iters`/`--budget` and by `multiprocessing` worker recycling.
"""

import argparse
import json
import os
import random
import sys
import time
from fractions import Fraction
from math import ceil
from multiprocessing import Pool

_HERE = os.path.dirname(os.path.abspath(__file__))
_ATTRACTOR = os.path.normpath(os.path.join(_HERE, os.pardir, "attractor"))
_REPMETER = os.path.normpath(os.path.join(_HERE, os.pardir, "repmeter"))
for _p in (_ATTRACTOR, _REPMETER):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from instance import Instance, factor_str        # noqa: E402
from anytime import greedy, prune, local_search, search, decision   # noqa: E402
from measure import gen_text                     # noqa: E402


# --------------------------------------------------------------------------
# texts: the families of the brief, plus the run-length family that works
# --------------------------------------------------------------------------


def runs_to_text(runs, start=0):
    """Alternating runs of two symbols: [3,2,1] -> 000 11 0."""
    out = []
    c = start
    for L in runs:
        assert L >= 1
        out.extend([c] * L)
        c ^= 1
    return out


def _random_runs(rng, n, maxrun):
    runs = []
    tot = 0
    while tot < n:
        L = rng.randint(1, maxrun)
        if tot + L > n:
            L = n - tot
        runs.append(L)
        tot += L
    return runs


def fam_runs(rng, n, maxrun):
    return runs_to_text(_random_runs(rng, n, maxrun))


def fam_runs_ge2(rng, n):
    """Run lengths in {2,3}: the periodic core `000111000111...` with defects."""
    runs = []
    tot = 0
    while tot < n:
        L = rng.choice((2, 3))
        if tot + L > n:
            L = n - tot
        runs.append(L)
        tot += L
    return runs_to_text(runs)


def fam_periodic_defect(rng, n, p):
    """(u)^m for a random primitive-looking u of length p, then a few flips."""
    u = [rng.getrandbits(1) for _ in range(p)]
    if len(set(u)) == 1:
        u[0] ^= 1
    sym = [u[i % p] for i in range(n)]
    flips = max(1, n // 16)
    for _ in range(flips):
        i = rng.randrange(n)
        sym[i] ^= 1
    return sym


def fam_square(rng, n, kind):
    h = n // 2
    s = [rng.getrandbits(1) for _ in range(h)]
    if kind == "ss":
        sym = s + s
    elif kind == "ssr":
        sym = s + s[::-1]
    elif kind == "ssh":
        sym = s + s + s
    else:
        raise ValueError(kind)
    return sym[:n]


def fam_stutter(rng, n):
    """u v u / u v u v with short random blocks (nested inflation)."""
    k = rng.choice((2, 3, 4))
    L = max(1, n // (2 * k + 1))
    u = [rng.getrandbits(1) for _ in range(L)]
    v = [rng.getrandbits(1) for _ in range(L)]
    sym = []
    while len(sym) < n:
        sym.extend(u)
        if len(sym) < n:
            sym.extend(v)
    return sym[:n]


def fam_separator(rng, n):
    """u 0^m v: a low-period block with an aperiodic insertion."""
    L = max(2, n // 3)
    u = [rng.getrandbits(1) for _ in range(L)]
    v = [rng.getrandbits(1) for _ in range(L)]
    m = n - 2 * L
    if m < 0:
        return (u + v)[:n]
    out = u + [0] * (m // 2) + v + [0] * (m - m // 2)
    return out[:n]


def fam_pool(rng, n, pool, blen):
    """Concatenate blocks drawn from a small pool: repeated shapes, few factors."""
    blocks = [[rng.getrandbits(1) for _ in range(blen)] for _ in range(pool)]
    sym = []
    while len(sym) < n:
        sym.extend(blocks[rng.randrange(pool)])
    return sym[:n]


def _fib_word(n):
    return gen_text("fibonacci:%d" % 20)[:n]


def _pd_word(n):
    """Period-doubling word (0 -> 01, 1 -> 00): delta = 2 at the lengths we sample."""
    s = [0]
    while len(s) < n:
        s = [y for c in s for y in ((0, 1) if c == 0 else (0, 0))]
    return s[:n]


def _rs_word(n):
    """Rudin-Shapiro parity word (0 -> 00, 1 -> 01): delta = 2 at the lengths we sample."""
    s = [0, 0, 0, 1]
    while len(s) < n:
        s = [y for c in s for y in ((0, 0) if c == 0 else (0, 1))]
    return s[:n]


def _tm_word(n):
    return gen_text("thue-morse:%d" % max(10, n.bit_length() + 1))[:n]


def fam_extend(rng, n, base):
    """One-symbol extensions of a known witness (the n = 32 record and friends)."""
    sym = list(base)
    while len(sym) < n:
        sym.append(rng.getrandbits(1))
    return sym[:n]


def _lowdelta_templates(n):
    """Templates for the delta-bounded walk: Fibonacci, Thue-Morse, and known winners."""
    return [_fib_word(n), _tm_word(n), _pd_word(n), _rs_word(n), S64, S32]


class DeltaWalk:
    """Grow a text one symbol at a time, refusing any prefix with `ceil(delta) > dmax`.

    `delta = max_k d_k/k` is monotone non-decreasing when a text is extended (`d_k` only
    grows), and `ceil(delta) <= dmax` is exactly `d_k <= dmax*k` for every k.  So a walk
    that keeps every prefix inside the class reaches exactly texts of the class, and the
    factors added by one appended symbol are the suffixes ending at it -- which makes the
    update O(n) set insertions instead of a fresh suffix array per step.  The suffixes are
    `bytes` slices so the hashing runs at C speed; at n = 512 a whole walk is milliseconds.
    """

    def __init__(self, dmax):
        self.dmax = dmax
        self.buf = bytearray()
        self.dk = {}
        self.seen = set()
        self.violations = 0
        self.added = []          # per step: the factors that step introduced

    def push(self, c):
        self.buf.append(c)
        n = len(self.buf)
        added = []
        for j in range(n):
            f = bytes(self.buf[j:n])
            if f in self.seen:
                continue
            self.seen.add(f)
            added.append(f)
            k = n - j
            before = self.dk.get(k, 0)
            self.dk[k] = before + 1
            if before <= self.dmax * k < before + 1:
                self.violations += 1
        self.added.append(added)
        return self.ok()

    def pop(self):
        assert self.buf, "pop on an empty walk"
        del self.buf[-1]
        for f in self.added.pop():
            self.seen.discard(f)
            k = len(f)
            self.dk[k] -= 1
            if self.dk[k] <= self.dmax * k < self.dk[k] + 1:
                self.violations -= 1

    def ok(self):
        return self.violations == 0

    def sym(self):
        return list(self.buf)

    def delta(self):
        best = Fraction(0)
        for k, d in self.dk.items():
            v = Fraction(d, k)
            if v > best:
                best = v
        return best


def fam_lowdelta(n, rng, dmax, samples, templates=(), dev=0.15, max_steps=None):
    """Texts of length n with ceil(delta) <= dmax, sampled by the walk above.

    A purely random order of symbols almost never survives the `delta <= 2` bound past
    n = 100 (the class is a thin neighbourhood of the Sturmian words), so each step copies
    a `template` symbol with probability `1 - dev` before trying the other one; a template
    longer than n is truncated and a shorter one is padded at random.  Templates are the
    Fibonacci word, the Thue-Morse word, and the winners stored in results.json, so the
    sampler explores neighbourhoods of very different low-`delta` texts.
    """
    max_steps = max_steps or 200 * n
    out = []
    attempts = 0
    while len(out) < samples and attempts < 50 * samples:
        attempts += 1
        walk = DeltaWalk(dmax)
        template = templates[rng.randrange(len(templates))] if templates else []
        steps = 0
        while len(walk.buf) < n:
            steps += 1
            if steps > max_steps:
                break
            m = len(walk.buf)
            want = template[m] if m < len(template) else rng.getrandbits(1)
            if rng.random() > dev:
                opts = (want, 1 - want)
            else:
                opts = (1 - want, want)
            placed = False
            for c in opts:
                if walk.push(c):
                    placed = True
                    break
                walk.pop()
            if not placed:
                for _ in range(rng.randint(1, 5)):
                    walk.pop()
            assert walk.ok(), "the walk left the delta class"
        if len(walk.buf) == n:
            out.append(walk.sym())
    return out


# the kernel-checked n = 32 record (SortBounds/Projects/Packing/Packing.lean)
S32 = [1 if c == "b" else 0 for c in "bbbaaaabbabbaaabbaaaabbaabbaabaa"]

# the n = 64 record found by this lane's first search (see the report)
S64 = "0001110111000111000111000101010001101100111011101110001110110010"
S64 = [int(c) for c in S64]


def families(n, rng):
    """Every seed text of length n: (label, symbols) pairs.  Order is deterministic."""
    out = []
    for maxrun in (2, 3, 4, 6):
        out.append(("runs-max%d" % maxrun, fam_runs(rng, n, maxrun)))
    out.append(("runs-2-3", fam_runs_ge2(rng, n)))
    for p in (3, 4, 6, 8):
        out.append(("periodic%d-defect" % p, fam_periodic_defect(rng, n, p)))
    for kind in ("ss", "ssr", "ssh"):
        out.append(("square-" + kind, fam_square(rng, n, kind)))
    out.append(("stutter", fam_stutter(rng, n)))
    out.append(("separator", fam_separator(rng, n)))
    for pool, blen in ((2, 3), (2, 5), (3, 4), (4, 6)):
        out.append(("pool%d-%d" % (pool, blen), fam_pool(rng, n, pool, blen)))
    out.append(("fibonacci", _fib_word(n)))
    out.append(("thue-morse", _tm_word(n)))
    out.append(("random", [rng.getrandbits(1) for _ in range(n)]))
    out.append(("extend-s32", fam_extend(rng, n, S32)))
    out.append(("extend-s64", fam_extend(rng, n, S64)))
    for label, sym in out:
        assert len(sym) == n, (label, len(sym), n)
    return out


# --------------------------------------------------------------------------
# evaluation: exact delta, a verified upper bound, a certified lower bound
# --------------------------------------------------------------------------


def _di(sym):
    return "".join(str(c) for c in sym)


def evaluate(sym, packing_restarts=32):
    """(delta, ceil delta, ub, greedy attractor, packing size, packing witnesses)."""
    inst = Instance(sym)
    delta = inst.delta()
    dc = int(ceil(delta))
    g = local_search(inst, prune(inst, greedy(inst)))
    wit = inst.witness(g)
    if wit is not None:
        raise AssertionError("greedy+prune+local_search produced a non-attractor: %r" % (wit,))
    pk, pw = inst.packing_bound(restarts=packing_restarts)
    ok, _detail = inst.certify_packing(pw)
    if not ok:
        raise AssertionError("packing certificate failed to re-check")
    return delta, dc, len(g), g, pk, pw


def score_of(delta_ceil, lb, ub):
    """Hill-climbing objective: certified gap first, then the weak (ub) gap.

    `lb - ceil(delta)` is what a row can *claim*; `ub - ceil(delta)` is where the true gap
    may be.  Both are integers in [-n, n], so 1000 is a safe multiplier.
    """
    return 1000 * (lb - delta_ceil) + (ub - delta_ceil)


REJECT = -10 ** 6


def quick(sym, packing_restarts=32, delta_max=None):
    """One evaluation with the score, without building a result row.

    With `delta_max` set, a text with `ceil(delta) > delta_max` scores `REJECT`, which is
    how the "for fixed delta, how large can gamma be?" curve is measured: the hill climb
    then maximises the gap *inside* one delta class.
    """
    delta, dc, ub, g, pk, pw = evaluate(sym, packing_restarts)
    lb = max(dc, pk)
    score = score_of(dc, lb, ub)
    if delta_max is not None and dc > delta_max:
        score = REJECT
    return {"delta": delta, "dc": dc, "ub": ub, "gamma": g, "packing": pk,
            "packing_w": pw, "lb": lb, "score": score}


# --------------------------------------------------------------------------
# local search on the text (the brief's stage 3, driven by the *certified* gap)
# --------------------------------------------------------------------------


def mutate(sym, rng):
    """One random mutation of a binary text; length is preserved."""
    n = len(sym)
    out = list(sym)
    op = rng.random()
    if op < 0.40:                                    # flip one symbol
        out[rng.randrange(n)] ^= 1
    elif op < 0.65:                                  # flip a short window
        L = rng.randint(2, max(2, n // 8))
        i = rng.randrange(n - L + 1)
        for j in range(i, i + L):
            out[j] ^= 1
    elif op < 0.85:                                  # move a block
        L = rng.randint(1, max(1, n // 4))
        i = rng.randrange(n - L + 1)
        block = out[i:i + L]
        del out[i:i + L]
        k = rng.randrange(len(out) + 1)
        out[k:k] = block
    else:                                            # copy a block over another
        L = rng.randint(1, max(1, n // 6))
        i = rng.randrange(n - L + 1)
        k = rng.randrange(n - L + 1)
        out[k:k + L] = out[i:i + L]
    assert len(out) == n
    return out


def climb(sym, rng, iters, deadline=None, packing_restarts=32, allow_sideways=True,
          delta_max=None):
    """Iterated hill climbing on `score_of`; returns (best_sym, best_eval, accepted)."""
    cur = quick(sym, packing_restarts, delta_max)
    cur_sym = list(sym)
    best = (list(cur_sym), cur)
    accepted = 0
    for it in range(iters):
        if deadline is not None and time.monotonic() > deadline:
            break
        cand_sym = mutate(cur_sym, rng)
        cand = quick(cand_sym, packing_restarts, delta_max)
        improved = cand["score"] > cur["score"]
        if improved or (
                allow_sideways and cand["score"] == cur["score"] and rng.random() < 0.05):
            cur_sym, cur = cand_sym, cand
            if improved:
                accepted += 1
                if cand["score"] > best[1]["score"]:
                    best = (list(cand_sym), cand)
        if it and it % 500 == 0:
            # iterated local search: fall back to the best and perturb it
            cur_sym = list(best[0])
            for _ in range(rng.randint(2, 6)):
                cur_sym = mutate(cur_sym, rng)
            cur = quick(cur_sym, packing_restarts, delta_max)
    assert best[0] is not None
    return best[0], best[1], accepted


# --------------------------------------------------------------------------
# the certified bracket (anytime.search, with the primitives fallback)
# --------------------------------------------------------------------------


def bracket(sym, budget_s, node_cap, seed=0):
    """Certified [lb, ub] on gamma from `anytime.search`, re-verified; never raises."""
    inst = Instance(sym)
    delta = inst.delta()
    dc = int(ceil(delta))
    last = None
    path = "search"
    try:
        for step in search(inst, budget_s=budget_s, seed=seed, node_cap=node_cap):
            last = step
    except RuntimeError as exc:            # the GRASP restart can pop an empty heap
        path = "primitives-fallback (%s)" % (str(exc)[:60],)
        last = _bracket_primitives(inst, budget_s, node_cap, seed)
    if last is None:
        raise AssertionError("anytime.search yielded nothing")
    gamma = list(last["gamma"])
    if inst.witness(gamma) is not None:
        raise AssertionError("bracket: the reported attractor is not an attractor")
    pk, pw = inst.packing_bound(seed=seed, restarts=64)
    ok, _detail = inst.certify_packing(pw)
    if not ok:
        raise AssertionError("bracket: packing certificate failed to re-check")
    lb = max(last["lb"], pk, dc)
    ub = len(gamma)
    if lb > ub:
        raise AssertionError("bracket: lb %d > ub %d" % (lb, ub))
    if ub != last["ub"]:
        raise AssertionError("bracket: ub disagrees with the reported attractor")
    return {"delta": delta, "dc": dc, "lb": lb, "ub": ub, "gamma": gamma,
            "packing": pk, "packing_w": pw,
            "lb_source": last.get("lb_source", "delta/packing"),
            "path": path, "certified_exact": lb == ub}


def _bracket_primitives(inst, budget_s, node_cap, seed):
    """`anytime.search`'s own phases in ten lines, for texts where its GRASP restart dies."""
    t0 = time.monotonic()
    deadline = t0 + budget_s
    rng = random.Random(seed)
    delta = inst.delta()
    dc = int(ceil(delta))
    pk, _pw = inst.packing_bound(seed=seed, restarts=32, deadline=t0 + 0.25 * budget_s)
    lb = max(dc, pk)
    lb_source = "delta" if dc > pk else ("packing" if pk > dc else "delta+packing")
    best = local_search(inst, prune(inst, greedy(inst, rng=rng)),
                        deadline=deadline, rng=rng)
    assert inst.witness(best) is None
    k = lb
    while k < len(best) and time.monotonic() < deadline:
        sol, status = decision(inst, k, deadline=deadline, node_cap=node_cap)
        if status == "found":
            if inst.witness(sol) is None and len(sol) < len(best):
                best = sorted(sol)
            break
        if status == "infeasible":
            k += 1
            lb, lb_source = k, "exact tail"
            assert k <= len(best), "exact tail proved lb > ub"
        else:
            break
    return {"t": round(time.monotonic() - t0, 3), "gamma": sorted(best), "ub": len(best),
            "lb": lb, "lb_source": lb_source, "phase": "primitives"}


def make_row(sym, data, family, seed=0, extra=None):
    """A result row: exact delta, certified bracket, and the text itself."""
    lb, ub, dc = data["lb"], data["ub"], data["dc"]
    row = {
        "family": family, "n": len(sym), "text": _di(sym),
        "delta_num": data["delta"].numerator, "delta_den": data["delta"].denominator,
        "delta": str(data["delta"]), "delta_ceil": dc,
        "lb": lb, "ub": ub, "packing": data["packing"],
        "packing_factors": ["".join(str(c) for c in f) for _v, f, _s in data["packing_w"]],
        "attractor": list(data["gamma"]),
        "closed": lb == ub, "gap_lo": lb - dc, "gap_hi": ub - dc,
        "lb_source": data.get("lb_source", "delta/packing"),
        "path": data.get("path", "primitives-fallback"),
        "verified": True, "seed": seed,
    }
    if extra:
        row.update(extra)
    return row


# --------------------------------------------------------------------------
# workers
# --------------------------------------------------------------------------


def _init_worker():
    os.nice(10)


def task_search(task):
    """Seed from every family at length n, then hill-climb from the best few."""
    n, seed, iters = task["n"], task["seed"], task["iters"]
    budget_s, node_cap, min_report = task["budget"], task["node_cap"], task["min_report"]
    only, delta_max, restarts = task.get("only"), task.get("delta_max"), task.get("top", 2)
    rng = random.Random((n << 20) ^ seed)
    t0 = time.monotonic()
    deadline = t0 + budget_s
    rows = []
    scored = []
    for label, sym in families(n, rng):
        if only and only not in label:
            continue
        if time.monotonic() > deadline:
            break
        ev = quick(sym, delta_max=delta_max)
        scored.append((ev["score"], label, sym, ev))
    assert scored, "no family was evaluated at n=%d" % n
    scored.sort(key=lambda t: -t[0])
    for _s, label, sym, ev in scored[:restarts]:
        if time.monotonic() > deadline:
            break
        best_sym, best_ev, accepted = climb(sym, rng, iters, deadline=deadline,
                                           delta_max=delta_max)
        rows.append(("climb(%s)" % label, best_sym, best_ev, accepted))
    rows.append(("families-best", scored[0][2], scored[0][3], 0))
    # certify the best candidates with a real bracket call
    rows.sort(key=lambda r: -r[2]["score"])
    out = []
    for label, sym, ev, accepted in rows[:2]:
        if ev["score"] <= min_report:
            continue
        d = bracket(sym, budget_s=max(5.0, min(60.0, deadline - time.monotonic())),
                    node_cap=node_cap, seed=seed)
        out.append(make_row(sym, d, label, seed=seed,
                            extra={"iters": iters, "accepted": accepted,
                                   "delta_max": delta_max,
                                   "seconds": round(time.monotonic() - t0, 2)}))
    return {"n": n, "seed": seed, "rows": out, "evaluated": len(scored),
            "seconds": round(time.monotonic() - t0, 2)}


def task_local(task):
    """Hill-climb from stored witnesses and from fresh family seeds at length n."""
    n, seed, iters = task["n"], task["seed"], task["iters"]
    budget_s, node_cap, min_report = task["budget"], task["node_cap"], task["min_report"]
    only, delta_max = task.get("only"), task.get("delta_max")
    starts = task.get("starts")
    rng = random.Random((n << 21) ^ seed)
    t0 = time.monotonic()
    deadline = t0 + budget_s
    pool = [[int(c) for c in s][:n] for s in (starts or []) if len(s) >= n]
    for label, sym in families(n, rng):
        if only and only not in label:
            continue
        pool.append(sym)
    if delta_max is not None:
        # inside one delta class, random family seeds are almost never in it; sample the
        # class directly instead (DeltaWalk keeps every prefix inside it).
        pool.extend(fam_lowdelta(n, rng, delta_max, task.get("samples") or 40,
                                 templates=_lowdelta_templates(n)))
    best = None
    out = []
    for sym in pool:
        if time.monotonic() > deadline:
            break
        best_sym, best_ev, accepted = climb(sym, rng, iters, deadline=deadline,
                                           delta_max=delta_max)
        if best is None or best_ev["score"] > best[2]["score"]:
            best = (best_sym, accepted, best_ev)
    assert best is not None, "no climbing happened at n=%d" % n
    if best[2]["score"] > min_report:
        d = bracket(best[0], budget_s=max(5.0, min(120.0, deadline - time.monotonic())),
                    node_cap=node_cap, seed=seed)
        out.append(make_row(best[0], d, "local-search", seed=seed,
                            extra={"iters": iters, "accepted": best[1],
                                   "delta_max": delta_max,
                                   "seconds": round(time.monotonic() - t0, 2)}))
    return {"n": n, "seed": seed, "rows": out, "evaluated": len(pool),
            "seconds": round(time.monotonic() - t0, 2)}


def task_sample(task):
    """Evaluate many draws from the seed families (no climbing) and bracket the best.

    This is the instrument for lengths where a hill climb costs too much: a fresh random
    draw from a family is O(n) to build and ~n*2n/64 ms to measure, so thousands of draws
    per second still fit.  Every draw is scored exactly as in `quick`, and only the best
    one goes to `bracket`.
    """
    n, seed = task["n"], task["seed"]
    samples = task.get("samples") or 50
    delta_max = task.get("delta_max")
    only = task.get("only")
    node_cap, min_report = task["node_cap"], task["min_report"]
    rng = random.Random((n << 22) ^ seed)
    t0 = time.monotonic()
    texts = []
    if delta_max is not None:
        texts = fam_lowdelta(n, rng, delta_max, samples,
                             templates=_lowdelta_templates(n))
    else:
        while len(texts) < samples:
            before = len(texts)
            for label, sym in families(n, rng):
                if only and only not in label:
                    continue
                texts.append(sym)
            assert len(texts) > before, "no family matched %r at n=%d" % (only, n)
    assert texts, "no sample was built at n=%d" % n
    best = None
    hist = {}
    for sym in texts:
        ev = quick(sym, delta_max=delta_max)
        if ev["score"] == REJECT:
            continue
        g = ev["lb"] - ev["dc"]
        hist[g] = hist.get(g, 0) + 1
        if best is None or ev["score"] > best[1]["score"]:
            best = (sym, ev)
    assert best is not None, "every sample was rejected at n=%d" % n
    out = []
    if best[1]["score"] > min_report:
        d = bracket(best[0], budget_s=task["budget"], node_cap=node_cap, seed=seed)
        out.append(make_row(best[0], d, task.get("label") or "sample-best", seed=seed,
                            extra={"samples": len(texts), "delta_max": delta_max,
                                   "hist_gap_lb": {str(k): v for k, v in sorted(hist.items())},
                                   "seconds": round(time.monotonic() - t0, 2)}))
    return {"n": n, "seed": seed, "rows": out, "evaluated": len(texts),
            "seconds": round(time.monotonic() - t0, 2)}


def task_bracket(task):
    """A certified bracket for one stored text, with a generous budget."""
    text, budget_s, node_cap, family, seed = task
    sym = [int(c) for c in text]
    d = bracket(sym, budget_s=budget_s, node_cap=node_cap, seed=seed)
    return {"n": len(sym), "seed": seed, "rows": [make_row(sym, d, family, seed=seed,
                                                           extra={"budget_s": budget_s})]}


def task_exhaustive(task):
    """Every binary text of length n in [lo, hi): a certified bracket on the *maximum* gap.

    `ub(S) - ceil(delta(S))` is an upper bound on gap(S) for every S, so the maximum of it
    over all 2^n texts bounds the maximum gap from above.  The converse direction needs the
    lower bound: `lb(S) - ceil(delta(S))` is a certified lower bound on gap(S), so its
    maximum over all texts bounds the maximum gap from below.  Because `lb <= ub`, a text
    with `ub - ceil(delta) <= 1` has `lb - ceil(delta) <= 1`, so computing the packing bound
    only for the texts with `ub - ceil(delta) >= 2` loses nothing.
    """
    n, lo, hi, packing_restarts = task
    hist = {}
    best_ub = None               # (gap_hi, text, delta, dc, ub, packing, lb, attractor)
    best_lb = None               # (gap_lo, text, ...)
    top = []                     # up to 8 texts with the largest gap_hi in this chunk
    checked = 0
    t0 = time.monotonic()
    for code in range(lo, hi):
        sym = [(code >> j) & 1 for j in range(n)]
        inst = Instance(sym)
        delta = inst.delta()
        dc = int(ceil(delta))
        g = local_search(inst, prune(inst, greedy(inst)))
        ub = len(g)
        checked += 1
        gap = ub - dc
        hist[gap] = hist.get(gap, 0) + 1
        if gap >= 2:
            top.append((gap, _di(sym)))
            if len(top) > 64:
                top.sort(reverse=True)
                del top[8:]
        if best_ub is None or gap > best_ub[0]:
            if inst.witness(g) is not None:
                raise AssertionError("non-attractor at %r" % (_di(sym),))
            pk, pw = inst.packing_bound(restarts=packing_restarts)
            ok, _d = inst.certify_packing(pw)
            if not ok:
                raise AssertionError("packing certificate failed at %r" % (_di(sym),))
            best_ub = (gap, _di(sym), delta, dc, ub, pk, max(dc, pk), g)
            if best_lb is None or max(dc, pk) - dc > best_lb[0]:
                best_lb = (max(dc, pk) - dc, _di(sym), delta, dc, ub, pk, max(dc, pk), g)
        elif gap >= 2:                        # could still improve the certified side
            pk, pw = inst.packing_bound(restarts=packing_restarts)
            lb = max(dc, pk)
            if best_lb is None or lb - dc > best_lb[0]:
                ok, _d = inst.certify_packing(pw)
                if not ok:
                    raise AssertionError("packing certificate failed at %r" % (_di(sym),))
                if inst.witness(g) is not None:
                    raise AssertionError("non-attractor at %r" % (_di(sym),))
                best_lb = (lb - dc, _di(sym), delta, dc, ub, pk, lb, g)
    assert checked == hi - lo

    def _row(b):
        if b is None:
            return None
        return {"gap_hi": b[4] - b[3], "gap_lo": b[6] - b[3], "text": b[1],
                "delta": str(b[2]), "delta_ceil": b[3], "ub": b[4], "packing": b[5],
                "lb": b[6], "attractor": b[7]}

    return {"n": n, "lo": lo, "hi": hi, "checked": checked, "hist": hist,
            "best": _row(best_ub), "best_lb": _row(best_lb),
            "top": sorted(top, reverse=True)[:8],
            "seconds": round(time.monotonic() - t0, 2)}


# --------------------------------------------------------------------------
# driver: single writer, incremental JSON
# --------------------------------------------------------------------------


def _write_json(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(obj, fh, indent=1, sort_keys=True)
        fh.write("\n")
    os.replace(tmp, path)


def _append_jsonl(path, row):
    with open(path, "a") as fh:
        fh.write(json.dumps(row, sort_keys=True) + "\n")


def _load(path):
    if os.path.exists(path):
        with open(path) as fh:
            return json.load(fh)
    return {"rows": [], "best": {}, "exhaustive": {}, "tasks": []}


def _merge_into(state, other):
    """Union another driver's state into this one (rows, per-length best, sweeps)."""
    for row in other.get("rows", []):
        _absorb(state, row)
    for key, cur in other.get("exhaustive", {}).items():
        mine = state["exhaustive"].get(key)
        if mine is None:
            state["exhaustive"][key] = cur
            continue
        mine["checked"] = max(mine.get("checked", 0), cur.get("checked", 0))
        mine["seconds"] = round(mine.get("seconds", 0.0) + cur.get("seconds", 0.0), 1)
        for k, v in cur.get("hist", {}).items():
            mine["hist"][k] = max(mine["hist"].get(k, 0), v)
        if cur.get("best") and (mine.get("best") is None
                                or cur["best"]["gap_hi"] > mine["best"]["gap_hi"]):
            mine["best"] = cur["best"]
        if mine["checked"] == (1 << int(key)):
            mine["max_gap_ub"] = max(int(k) for k in mine["hist"])
        mine["certified"] = mine.get("certified") or cur.get("certified")


def _best_key(row):
    return (row["gap_lo"], row["gap_hi"], -row["n"])


def _absorb(state, row):
    """Insert a row into the merged state; return True if it is a new per-n record."""
    state["rows"].append(row)
    cur = state["best"].get(str(row["n"]))
    new = cur is None or _best_key(row) > _best_key(cur)
    if new:
        state["best"][str(row["n"])] = row
    return new


def _parse_ns(text):
    out = []
    for part in text.split(","):
        part = part.strip()
        if not part:
            continue
        if part.startswith("range:"):
            a, b, step = part[6:].split(":")
            out.extend(range(int(a), int(b) + 1, int(step)))
        else:
            out.append(int(part))
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description="certified measurement of gamma - ceil(delta) "
                                             "on binary text")
    ap.add_argument("--exhaustive", help="lengths to sweep exhaustively, e.g. 20,21,22")
    ap.add_argument("--search", action="store_true", help="family + hill-climb search")
    ap.add_argument("--sample", action="store_true", help="draw many family samples, bracket best")
    ap.add_argument("--label", help="family label for --sample rows")
    ap.add_argument("--local", action="store_true", help="local search from stored witnesses")
    ap.add_argument("--bracket", action="store_true", help="re-bracket the stored texts")
    ap.add_argument("--report", action="store_true", help="print the curve from --json")
    ap.add_argument("--ns", help="lengths for --search/--local, e.g. 20,24,32 or range:20:64:4")
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--iters", type=int, default=400, help="climb iterations per start")
    ap.add_argument("--seeds", type=int, default=1, help="independent tasks per length")
    ap.add_argument("--secret-seed", type=int, default=0, help="offset of the seed sequence")
    ap.add_argument("--budget", type=float, default=300.0, help="wall-clock bound per task")
    ap.add_argument("--node-cap", type=int, default=400000)
    ap.add_argument("--min-report", type=int, default=2000,
                    help="report rows whose score exceeds this (1000*gap_lb + gap_ub)")
    ap.add_argument("--only", help="use only the seed families whose label contains this")
    ap.add_argument("--delta-max", type=int,
                    help="hill-climb inside one delta class: reject ceil(delta) above this")
    ap.add_argument("--top", type=int, default=2, help="climbs per search task")
    ap.add_argument("--samples", type=int, default=0,
                    help="DeltaWalk samples per task when --delta-max is given (default 40)")
    ap.add_argument("--json", default=os.path.join(_HERE, "results.json"))
    ap.add_argument("--merge", action="append", default=[],
                    help="union these state files into --json before running")
    ap.add_argument("--jsonl", default=os.path.join(_HERE, "results.jsonl"))
    args = ap.parse_args(argv)

    state = _load(args.json)
    for extra in args.merge:
        _merge_into(state, _load(extra))
    t0 = time.monotonic()

    if args.report:
        report(state)
        return 0

    if args.exhaustive:
        ns = _parse_ns(args.exhaustive)
        tasks = []
        for n in ns:
            total = 1 << n
            chunks = args.workers * 4
            step = (total + chunks - 1) // chunks
            for lo in range(0, total, step):
                tasks.append((n, lo, min(lo + step, total), 48))
        with Pool(args.workers, initializer=_init_worker) as pool:
            done = 0
            for res in pool.imap_unordered(task_exhaustive, tasks):
                done += 1
                key = str(res["n"])
                cur = state["exhaustive"].get(key, {"checked": 0, "hist": {}, "best": None,
                                                    "best_lb": None, "seconds": 0.0})
                cur.setdefault("best_lb", None)
                cur["checked"] += res["checked"]
                cur["seconds"] = round(cur["seconds"] + res["seconds"], 1)
                for k, v in res["hist"].items():
                    cur["hist"][str(k)] = cur["hist"].get(str(k), 0) + v
                if res["best"] is not None and (
                        cur["best"] is None or res["best"]["gap_hi"] > cur["best"]["gap_hi"]):
                    cur["best"] = res["best"]
                if res.get("best_lb") is not None and (
                        cur["best_lb"] is None
                        or res["best_lb"]["gap_lo"] > cur["best_lb"]["gap_lo"]):
                    cur["best_lb"] = res["best_lb"]
                cur.setdefault("top", [])
                cur["top"] = sorted(cur["top"] + [list(t) for t in res.get("top", [])],
                                    reverse=True)[:32]
                state["exhaustive"][key] = cur
                if cur["checked"] == (1 << res["n"]):
                    cur["max_gap_ub"] = max(int(k) for k in cur["hist"])
                    cur["max_gap_lb"] = cur["best_lb"]["gap_lo"] if cur["best_lb"] else 0
                _write_json(args.json, state)
                print("[%6.1fs] exhaustive n=%d %d/%d texts, gap in [%s, %s]"
                      % (time.monotonic() - t0, res["n"], cur["checked"], 1 << res["n"],
                         cur["max_gap_lb"] if cur["checked"] == (1 << res["n"]) else "?",
                         cur["max_gap_ub"] if cur["checked"] == (1 << res["n"]) else "?"),
                      flush=True)
                if done == len(tasks):
                    print("exhaustive sweep complete", flush=True)
        # certify each exhaustive argmax with a real bracket
        for key, cur in sorted(state["exhaustive"].items(), key=lambda kv: int(kv[0])):
            if cur.get("best") is None or cur.get("certified"):
                continue
            texts = [cur["best"]["text"]]
            if cur.get("best_lb") and cur["best_lb"]["text"] not in texts:
                texts.append(cur["best_lb"]["text"])
            for _gap, text in cur.get("top", []):        # every candidate argmax
                if text not in texts and _gap >= cur.get("max_gap_ub", 0):
                    texts.append(text)
            rows = []
            for text in texts[:64]:
                res = task_bracket((text, 120.0, args.node_cap, "exhaustive-best", 0))
                for row in res["rows"]:
                    _absorb(state, row)
                    _append_jsonl(args.jsonl, row)
                    rows.append(row)
            cur["certified"] = True
            # the upper end of the sweep's interval is now the *best* attractor found for the
            # candidate argmax texts; it is final once every text with the maximum
            # ub-gap has been bracketed.
            if rows:
                top_ub = cur.get("max_gap_ub", 0)
                cand = sum(1 for _g, _t in cur.get("top", []) if _g >= top_ub)
                need = max(cand, int(cur["hist"].get(str(top_ub), 0)))
                cur["argmax_texts"] = len(rows)
                if len(rows) >= need:
                    cur["max_gap_ub"] = max(r["gap_hi"] for r in rows)
            _write_json(args.json, state)
            row = state["best"].get(key)
            print("[%6.1fs] exhaustive n=%s argmax bracketed: gap in [%s, %s]"
                  % (time.monotonic() - t0, key,
                     "?" if row is None else row["gap_lo"],
                     "?" if row is None else row["gap_hi"]), flush=True)

    if args.sample:
        ns = _parse_ns(args.ns or "20,24,28,32,40,48,64")
        tasks = []
        for n in ns:
            for s in range(args.seeds):
                tasks.append({"n": n, "seed": args.secret_seed + s, "budget": args.budget,
                              "node_cap": args.node_cap, "min_report": args.min_report,
                              "samples": args.samples, "only": args.only,
                              "delta_max": args.delta_max, "label": args.label})
        with Pool(args.workers, initializer=_init_worker) as pool:
            for res in pool.imap_unordered(task_sample, tasks):
                rec = False
                for row in res["rows"]:
                    if _absorb(state, row):
                        rec = True
                    _append_jsonl(args.jsonl, row)
                _write_json(args.json, state)
                print("[%6.1fs] sample n=%2d seed=%d draws=%d %5.1fs rows=%d%s"
                      % (time.monotonic() - t0, res["n"], res["seed"], res["evaluated"],
                         res["seconds"], len(res["rows"]), "  NEW BEST" if rec else ""),
                      flush=True)

    if args.search or args.local:
        ns = _parse_ns(args.ns or "20,24,28,32,40,48,64")
        starts = []
        if args.local:
            for key in sorted(state["best"], key=int):
                if state["best"][key].get("closed"):
                    starts.append(state["best"][key]["text"])
        tasks = []
        for n in ns:
            for s in range(args.seeds):
                tasks.append({"n": n, "seed": args.secret_seed + s, "iters": args.iters,
                              "budget": args.budget, "node_cap": args.node_cap,
                              "min_report": args.min_report, "starts": starts,
                              "only": args.only, "delta_max": args.delta_max,
                              "top": args.top, "samples": args.samples})
        fn = task_local if args.local else task_search
        with Pool(args.workers, initializer=_init_worker) as pool:
            for res in pool.imap_unordered(fn, tasks):
                rec = False
                for row in res["rows"]:
                    if _absorb(state, row):
                        rec = True
                    _append_jsonl(args.jsonl, row)
                _write_json(args.json, state)
                print("[%6.1fs] n=%2d seed=%d evaluated=%d %5.1fs rows=%d%s"
                      % (time.monotonic() - t0, res["n"], res["seed"], res["evaluated"],
                         res["seconds"], len(res["rows"]), "  NEW BEST" if rec else ""),
                      flush=True)

    if args.bracket:
        # re-bracket every per-length record, and every stored row whose bracket is open
        todo = {}
        for key, row in state["best"].items():
            todo[row["text"]] = (row["n"], "bracket-" + row["family"])
        for row in state["rows"]:
            if not row["closed"]:
                todo[row["text"]] = (row["n"], "bracket-" + row["family"])
        tasks = [(text, args.budget, args.node_cap, fam, 0)
                 for text, (n, fam) in todo.items()]
        print("re-bracketing %d texts" % len(tasks), flush=True)
        with Pool(args.workers, initializer=_init_worker) as pool:
            for res in pool.imap_unordered(task_bracket, tasks):
                for row in res["rows"]:
                    _absorb(state, row)
                    _append_jsonl(args.jsonl, row)
                _write_json(args.json, state)
                print("[%6.1fs] bracket n=%d gap in [%d, %d] closed=%s"
                      % (time.monotonic() - t0, res["n"], res["rows"][0]["gap_lo"],
                         res["rows"][0]["gap_hi"], res["rows"][0]["closed"]), flush=True)

    _write_json(args.json, state)
    report(state)
    return 0


def report(state):
    print("\n=== curve: max certified gap per length ===")
    print("%3s %-6s %-14s %-10s %-4s %-4s %-4s %-4s %s"
          % ("n", "how", "family", "delta", "ceil", "lb", "ub", "gap", "text"))
    for key in sorted(state["best"], key=int):
        row = state["best"][key]
        print("%3d %-6s %-14s %-10s %-4d %-4d %-4d %-4s %s"
              % (row["n"], "closed" if row["closed"] else "OPEN", row["family"][:14],
                 row["delta"], row["delta_ceil"], row["lb"], row["ub"],
                 "%d" % row["gap_lo"] if row["closed"]
                 else "[%d,%d]" % (row["gap_lo"], row["gap_hi"]),
                 row["text"][:70]))
    if state["exhaustive"]:
        print("\n=== exhaustive: every text of that length ===")
        for key in sorted(state["exhaustive"], key=int):
            cur = state["exhaustive"][key]
            print("n=%s checked=%d/%d max gap in [%s, %s]  hist=%s"
                  % (key, cur["checked"], 1 << int(key), cur.get("max_gap_lb"),
                     cur.get("max_gap_ub"),
                     dict(sorted(((k, v) for k, v in cur["hist"].items()),
                                 key=lambda kv: int(kv[0])))))


if __name__ == "__main__":
    sys.exit(main())
