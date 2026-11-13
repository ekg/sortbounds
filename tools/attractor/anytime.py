"""anytime.py -- an anytime search for small string attractors.

`search(inst, budget_s, seed)` is a generator of improvements:

    for step in search(inst, budget_s=60.0):
        print(step["t"], step["ub"], step["lb"], step["gamma"])

Each yield carries a *verified* attractor (a strict improvement over every
previously yielded one), the current upper bound ub = |gamma|, and the current
certified lower bound lb.  Nothing is yielded that `Instance.verify` rejects, and
`ub` never increases (asserted inside the generator).

The schedule (each phase only ever accepts a strictly smaller gamma):

  1 G, greedy max-coverage: repeatedly add the position that covers the most
    still-uncovered nodes; deterministic, |Gamma| = O(n) worst case but O(log)
    rounds in practice.  Cost O(n) mask popcounts per round.
  2 P, irredundant prune: drop every position whose removal keeps the cover.
  3 L, local search: 2->1 replacements (two positions replaced by one) and
    1->1 swaps followed by a prune; a move is accepted only when the size after
    the move is strictly smaller, so every accepted iteration is progress.
  4 X, exact tail: iterative deepening k = lb, lb+1, ... < ub deciding "is there
    an attractor of size <= k" by a bounded DFS over the set-cover instance.
    A completed DFS that fails *raises* the lower bound to k+1; a DFS that runs
    out of its node budget concludes nothing and the bound is left alone.
  5 Restarts: randomized greedy (GRASP) + prune + local search, budget
    permitting, keeping the best.

Lower bound: lb = max(ceil(delta), packing), both certified and independent of
the search -- see Instance.delta and Instance.packing_bound.  The DFS may raise
lb further; nothing else may.

Every loop asserts progress: the greedy raises if a round does not uncover a new
node, the local search raises if an iteration does not shrink gamma, and the
iterative deepening raises if k does not increase.  Deadlines are checked at the
top of each loop, so a run terminates at budget_s (a greedy round is a bounded
amount of work, so the deadline is respected to within one round).
"""

import argparse
import json
import random
import sys
import time
from math import ceil

from instance import Instance, factor_str

try:                                    # gen_text lives in ../repmeter
    from measure import gen_text
except ImportError:                     # pragma: no cover - path handled in instance
    gen_text = None


class _Stop(Exception):
    """Raised internally when the deadline or a node budget is reached."""


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------


def _popcount(x):
    return bin(x).count("1")


def _deadline(budget_s):
    return None if budget_s is None else time.monotonic() + budget_s


def _past(deadline):
    return deadline is not None and time.monotonic() > deadline


def _covered(inst, gamma):
    mask = 0
    for p in gamma:
        mask |= inst.cover_masks[p]
    return mask


# --------------------------------------------------------------------------
# 1 / 2: greedy cover, then irredundant prune
# --------------------------------------------------------------------------


def greedy(inst, deadline=None, rng=None, top=1):
    """Max-coverage greedy over the node universe.  Deterministic when top == 1.

    Each round scores every position by how many still-uncovered nodes it covers
    and adds the best one (with top > 1, a uniformly random one among the `top`
    best -- the GRASP restart used by search).  Raises if a round cannot strictly
    decrease the number of uncovered nodes, so it cannot spin.
    """
    full = inst.full_mask
    covered = 0
    gamma = []
    rounds = 0
    while covered != full:
        rounds += 1
        if rounds > inst.n + 1:
            raise RuntimeError("greedy did not terminate in n+1 rounds")
        if _past(deadline):
            raise _Stop()
        best_gain = 0
        cand = []
        cm = inst.cover_masks
        for p in range(inst.n):
            g = _popcount(cm[p] & ~covered)
            if g > best_gain:
                best_gain = g
                cand = [p]
            elif g == best_gain and g > 0:
                cand.append(p)
        if best_gain == 0:
            raise RuntimeError("greedy stalled with %d uncovered nodes"
                               % _popcount(full & ~covered))
        if top <= 1 or len(cand) == 1:
            p = cand[0]
        else:
            p = rng.choice(cand[:top])
        gamma.append(p)
        covered |= cm[p]
    return gamma


def prune(inst, gamma):
    """Drop every position whose removal keeps the cover.  |gamma| never grows."""
    full = inst.full_mask
    gamma = list(gamma)
    assert _covered(inst, gamma) == full, "prune given a non-attractor"
    changed = True
    while changed:
        changed = False
        for p in sorted(gamma, key=lambda p: _popcount(inst.cover_masks[p])):
            rest = [q for q in gamma if q != p]
            if _covered(inst, rest) == full:
                gamma = rest
                changed = True
    return sorted(gamma)


# --------------------------------------------------------------------------
# 3: local search (2->1 and swap+prune); only strict improvements
# --------------------------------------------------------------------------


def local_search(inst, gamma, deadline=None, rng=None, max_rounds=1000):
    """Improve gamma by 2->1 replacements and 1->1 swaps followed by a prune.

    Every accepted round strictly decreases len(gamma); the loop raises if a
    round that claims an improvement does not.
    """
    full = inst.full_mask
    cm = inst.cover_masks
    gamma = list(gamma)
    for _ in range(max_rounds):
        if _past(deadline):
            break
        before = len(gamma)
        nxt = _two_to_one(inst, gamma, full, cm)
        if nxt is None:
            nxt = _swap_then_prune(inst, gamma, full, cm, deadline, rng)
        if nxt is None:
            break
        gamma = nxt
        if len(gamma) >= before:
            raise RuntimeError("local search accepted a non-improvement: %d -> %d"
                               % (before, len(gamma)))
    return sorted(gamma)


def _two_to_one(inst, gamma, full, cm):
    """Replace two positions by one if the cover survives; then prune."""
    g = sorted(gamma)
    for i in range(len(g)):
        for j in range(i + 1, len(g)):
            rest = [q for q in g if q != g[i] and q != g[j]]
            need = full & ~_covered(inst, rest)
            if need == 0:
                return prune(inst, rest)
            for p in range(inst.n):
                if cm[p] & need == need:
                    return prune(inst, rest + [p])
    return None


def _swap_then_prune(inst, gamma, full, cm, deadline, rng):
    """1->1 swap that unlocks a prune.  Returns the pruned attractor or None."""
    g = sorted(gamma)
    order = list(g)
    if rng is not None:
        rng.shuffle(order)
    for a in order:
        if _past(deadline):
            return None
        rest = [q for q in g if q != a]
        rest_cov = _covered(inst, rest)
        need = full & ~rest_cov
        if need == 0:
            return prune(inst, rest)
        for p in range(inst.n):
            if p in g:
                continue
            if cm[p] & need == need:
                cand = prune(inst, rest + [p])
                if len(cand) < len(g):
                    return cand
    return None


# --------------------------------------------------------------------------
# 4: exact tail -- iterative deepening over the set-cover instance
# --------------------------------------------------------------------------


def decision(inst, k, deadline=None, node_cap=200000, coverers=None):
    """Is there an attractor of size <= k?  Bounded DFS over the node universe.

    Returns (solution_or_None, status) with status in
      "found"      a verified-size-<=k candidate (caller still verifies),
      "infeasible" the DFS finished: no attractor of size <= k exists,
      "budget"     the DFS was cut short: nothing is concluded.

    Completeness: every element u left uncovered forces at least one position of
    C(shortest factor of u) into the answer, so branching over C of one chosen
    element covers all solutions.  Two positions with the same effect on the
    uncovered set are tried once, and a failed (uncovered-set, slots) state is
    memoized, so the DFS tree is smaller than the naive one but still complete.
    """
    full = inst.full_mask
    if full == 0:
        return [], "found"
    cm = inst.cover_masks
    if coverers is None:
        coverers = _coverers(inst)
    # elements ordered by how many positions could cover them: branching on the
    # earliest such element that is still uncovered keeps the fan-out small.
    order = sorted(range(len(inst.nodes)), key=lambda v: len(coverers[v]))
    max_gain = max(_popcount(m) for m in cm)
    if max_gain == 0:
        return None, "budget"
    memo = set()
    nodes_visited = [0]
    chosen = []

    def rec(uncovered, slots):
        if uncovered == 0:
            return True
        if slots == 0:
            return False
        nodes_visited[0] += 1
        if nodes_visited[0] > node_cap:
            raise _Stop()
        if _past(deadline):
            raise _Stop()
        size = _popcount(uncovered)
        if size > slots * max_gain:
            return False
        key = (uncovered, slots)
        if key in memo:
            return False
        branch_elem = -1
        for v in order:
            if (uncovered >> v) & 1:
                branch_elem = v
                break
        assert branch_elem >= 0
        tried = {}
        for p in coverers[branch_elem]:
            piece = cm[p] & uncovered
            if piece in tried:
                continue
            tried[piece] = p
            chosen.append(p)
            if rec(uncovered & ~cm[p], slots - 1):
                return True
            chosen.pop()
        memo.add(key)
        return False

    try:
        ok = rec(full, k)
    except _Stop:
        return None, "budget"
    if ok:
        return list(chosen), "found"
    return None, "infeasible"


def _coverers(inst):
    """coverers[v] = positions p whose cover contains node v (transpose of cover_masks)."""
    coverers = [[] for _ in inst.nodes]
    for p, mask in enumerate(inst.cover_masks):
        u = mask
        while u:
            b = u & -u
            coverers[b.bit_length() - 1].append(p)
            u ^= b
    return coverers


def exact_gamma(inst, deadline=None, node_cap=200000, lb=1):
    """Smallest attractor by iterative deepening, or (None, extra_lb) if cut short.

    Raises the lower bound as it goes: a completed infeasible DFS at k proves
    gamma > k.  The k loop asserts that k increases, so it terminates.
    """
    k = max(1, lb)
    lb_proved = lb
    while True:
        if _past(deadline):
            return None, lb_proved
        sol, status = decision(inst, k, deadline=deadline, node_cap=node_cap)
        if status == "found":
            return sol, k
        if status == "budget":
            return None, lb_proved
        k += 1
        lb_proved = k
        if k > inst.n:
            raise RuntimeError("iterative deepening passed n without a solution")


# --------------------------------------------------------------------------
# the generator
# --------------------------------------------------------------------------


def search(inst, budget_s=60.0, seed=0, node_cap=200000, verbose=False):
    """Yield dicts {"t", "gamma", "ub", "lb", ...} on every improvement and at the end.

    Monotone: ub strictly decreases at every yield, and the final record repeats
    the best attractor found.  Every yielded gamma has passed Instance.verify.
    """
    t0 = time.monotonic()
    deadline = _deadline(budget_s)
    rng = random.Random(seed)
    n = inst.n
    log = [] if verbose else None

    delta = inst.delta()
    delta_int = int(ceil(delta))
    pack_k, pack_w = inst.packing_bound(seed=seed, restarts=32,
                                        deadline=None if deadline is None
                                        else t0 + 0.25 * budget_s)
    ok_pack, _ = inst.certify_packing(pack_w)
    if not ok_pack:
        raise AssertionError("packing certificate failed to re-check")
    lb = max(delta_int, pack_k)
    lb_why = []
    if delta_int >= lb:
        lb_why.append("delta")
    if pack_k >= lb:
        lb_why.append("packing")

    state = {"t": round(time.monotonic() - t0, 3), "gamma": [], "ub": n,
             "lb": lb, "phase": "start", "delta": str(delta),
             "packing": pack_k}
    if n == 0:
        state.update({"ub": 0, "lb": 0, "phase": "done", "done": True,
                      "certified_exact": True})
        yield state
        return

    best = [None]                       # boxed so consider() can rebind it

    def consider(cand, phase):
        """Verify cand; return an improvement record, or None if it is not smaller."""
        cand = sorted(set(cand))
        if best[0] is not None and len(cand) >= len(best[0]):
            return None
        wit = inst.witness(cand)
        if wit is not None:
            raise AssertionError("search produced a non-attractor at phase %r: %r"
                                 % (phase, wit))
        best[0] = cand
        out = dict(state)
        out.update({"t": round(time.monotonic() - t0, 3), "gamma": list(cand),
                    "ub": len(cand), "phase": phase, "lb": lb})
        return out

    # 1 greedy, 2 prune ------------------------------------------------------
    g = greedy(inst, deadline=None, rng=rng)   # one full greedy; always terminates
    rec = consider(g, "greedy")
    if rec is not None:
        yield rec
    rec = consider(prune(inst, best[0]), "prune")
    if rec is not None:
        yield rec

    # 3 local search ---------------------------------------------------------
    if not _past(deadline):
        rec = consider(local_search(inst, best[0], deadline=deadline, rng=rng),
                       "local-search")
        if rec is not None:
            yield rec

    # 5 GRASP restarts (before the exact tail: cheap upper-bound work first)
    restart = 0
    while not _past(deadline) and restart < 64:
        restart += 1
        try:
            g = greedy(inst, deadline=deadline, rng=rng, top=3)
        except _Stop:
            break
        cand = prune(inst, g)
        try:
            cand = local_search(inst, cand, deadline=deadline, rng=rng)
        except _Stop:
            pass
        rec = consider(cand, "restart-%d" % restart)
        if rec is not None:
            yield rec
            restart = 0

    # 4 exact tail -----------------------------------------------------------
    if not _past(deadline):
        coverers = _coverers(inst)
        k = max(lb, 1)
        while k < len(best[0]):
            if _past(deadline):
                break
            sol, status = decision(inst, k, deadline=deadline, node_cap=node_cap,
                                   coverers=coverers)
            if status == "found":
                rec = consider(sol, "exact")
                if rec is not None:
                    yield rec
                break
            if status == "infeasible":
                lb = k + 1                    # certified: no attractor of size <= k
                if "exact" not in lb_why:
                    lb_why.append("exact")
                k = lb
                if k > len(best[0]):
                    raise RuntimeError("exact tail proved lb > ub")
            else:                             # node budget exhausted: conclude nothing
                break

    final = dict(state)
    final.update({"t": round(time.monotonic() - t0, 3),
                  "gamma": list(best[0]) if best[0] is not None else [],
                  "ub": len(best[0]) if best[0] is not None else n,
                  "lb": lb, "phase": "done", "done": True,
                  "lb_sources": lb_why, "restarts": restart,
                  "certified_exact": best[0] is not None and len(best[0]) == lb,
                  "elapsed": round(time.monotonic() - t0, 3)})
    if log is not None:
        final["log"] = log
    yield final


# --------------------------------------------------------------------------
# command line
# --------------------------------------------------------------------------


def _read_input(args):
    if args.gen:
        return "gen:" + args.gen, gen_text(args.gen)
    if args.text is not None:
        return "text %r" % args.text, list(args.text.encode("utf-8"))
    if args.file:
        with open(args.file, "rb") as fh:
            return args.file, list(fh.read())
    data = sys.stdin.buffer.read()
    return "<stdin>", list(data)


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Anytime search for a small string attractor: certified "
                    "bracket [lb, ub] on gamma, improving with budget.")
    src = ap.add_mutually_exclusive_group()
    src.add_argument("file", nargs="?", help="file, read as raw bytes")
    src.add_argument("--text", help="literal text (UTF-8)")
    src.add_argument("--gen", help="fibonacci:K | thue-morse:K | random-binary:N:SEED")
    ap.add_argument("--budget", type=float, default=60.0, metavar="S",
                    help="wall-clock budget in seconds (default 60)")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--node-cap", type=int, default=200000,
                    help="DFS node budget per exact k (default 200000)")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)

    label, sym = _read_input(args)
    inst = Instance(sym)
    rows = []
    for step in search(inst, budget_s=args.budget, seed=args.seed,
                       node_cap=args.node_cap):
        rows.append(step)
        if not args.json:
            print("%7.3fs  ub=%s  lb=%s  phase=%-10s gamma=%s"
                  % (step["t"], step["ub"], step["lb"], step["phase"],
                     step["gamma"] if len(step["gamma"]) <= 40 else "<%d positions>"
                     % len(step["gamma"])))
    if args.json:
        json.dump({"input": label, "n": inst.n, "steps": rows}, sys.stdout, indent=2)
        sys.stdout.write("\n")
        return 0
    last = rows[-1]
    print("input       : %s" % label)
    print("n           : %d" % inst.n)
    print("delta       : %s" % last.get("delta"))
    print("packing     : %d  (certified lower bound: %d pairwise disjoint factors)"
          % (last.get("packing", 0), last.get("packing", 0)))
    print("bracket     : %d <= gamma <= %d%s"
          % (last["lb"], last["ub"],
             "   ==> gamma = %d exactly" % last["ub"] if last["lb"] >= last["ub"] else ""))
    if not last.get("certified_exact"):
        print("              (the bracket is not closed; gamma may be smaller than %d)"
              % last["ub"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
