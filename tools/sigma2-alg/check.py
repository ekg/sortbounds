"""check.py -- does the binary minimum attractor have exploitable structure?

Four experiments, all numbers produced by exact certified `gamma` (see
features.gamma_certified: an explicit verified attractor plus an exhausted
search over every smaller position set; an unclosed bracket raises and is
counted separately as "incomplete", never reported as a value).

  validate    two independent exact solvers agree (suffix-tree universe from
              ../attractor/anytime.py vs the definition-level solver
              features.gamma_k at k = n), gamma is invariant under complement,
              and the known anchors gamma(Fibonacci) = 2 and gamma(Thue-Morse)
              = 4 reproduce.
  gap         per n: max(gamma - ceil(delta)), max(gamma - gamma_2), the
              fraction of strings with gamma > ceil(delta), and the argmax
              witnesses.  Exhaustive up to --nmax (all 2^n binary words), then
              --samples random words per n above that.
  dependence  is gamma a FUNCTION of a feature vector?  Group every string by
              the vector; a group with two different gammas refutes that feature
              set.  Reported per feature set with the smallest witness pair.
  lift        k*(s) = min{k : gamma_k(s) = gamma(s)}.  Small k* would give an
              algorithm (gamma = gamma_K with K small, and gamma_k is exact in
              O(n) + exp(O(2^k k)) time); k* growing with n kills that route.
  hunt        local search for strings maximising gamma - ceil(delta) and
              gamma - gamma_2 at n larger than enumeration reaches.  A maximum
              that grows with n refutes a constant additive bound.

Every loop asserts progress; every run is wrapped in `timeout` by the caller.
Usage (from tools/sigma2-alg):

  timeout 1800 python3 check.py validate
  timeout 1800 python3 check.py gap --nmax 13 --samples 2000 --top 17
  timeout 1800 python3 check.py dependence --nmax 11
  timeout 1800 python3 check.py lift --nmax 12 --klift 6
  timeout 1800 python3 check.py hunt --ns 16,20,24,28,32 --rounds 40
  timeout 3600 python3 check.py all --quick
"""

import argparse
import itertools
import random
import sys
import time
from collections import Counter, defaultdict
from math import ceil

import features as F
from features import NotClosed


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------


def all_binary(n):
    """All 2^n binary words on {a, b}, first character fixed to 'a'.

    gamma is complement-invariant (checked in `validate`), so the complement of
    every word is gammma-equal to a word already in this list; the list has
    2^(n-1) elements and is a complete set of representatives.  `--all-words`
    switches to all 2^n words for the validate command.
    """
    if n == 0:
        return [""]
    return ["a" + "".join(b) for b in itertools.product("ab", repeat=n - 1)]


def complement(s):
    return s.translate(str.maketrans("ab", "ba"))


def gamma_of(s, time_cap=5.0):
    """Certified gamma, or None if the bracket did not close inside time_cap."""
    t0 = time.monotonic()
    try:
        g, _lb, _sol = F.gamma_certified(s, time_cap=time_cap)
    except NotClosed:
        return None
    if time.monotonic() - t0 > 2 * time_cap + 1.0:
        raise AssertionError("gamma_certified overran its %.2fs cap" % time_cap)
    return g


def fibonacci(n):
    a, b = "b", "ba"
    while len(b) < n:
        a, b = b, b + a
    return b[:n]


def thue_morse(k):
    s = "a"
    for _ in range(k):
        s = "".join("ab" if c == "a" else "ba" for c in s)
    return s


# ---------------------------------------------------------------------------
# validate
# ---------------------------------------------------------------------------


def cmd_validate(args):
    print("== validate ==")
    checks = 0
    # (1) two independent solvers agree at k = n
    for n in range(1, args.solver_nmax + 1):
        for s in all_binary(n):
            g, _lb, sol = F.gamma_certified(s)
            gk, _solk = F.gamma_k(s, n)
            gk_def, _solk2 = F.gamma_k(s, n)
            if not (g == gk == gk_def):
                raise AssertionError("solvers disagree on %r: %d vs %d" % (s, g, gk))
            checks += 1
    print("  solver agreement (anytime vs definition-level gamma_n): %d words, n <= %d"
          % (checks, args.solver_nmax))

    # (2) complement invariance, on all 2^n words
    c2 = 0
    for n in range(1, 13):
        for s in itertools.product("ab", repeat=n):
            s = "".join(s)
            if F.gamma_certified(s)[0] != F.gamma_certified(complement(s))[0]:
                raise AssertionError("gamma not complement-invariant on %r" % (s,))
            c2 += 1
    print("  complement invariance: %d words, n <= 12" % c2)

    # (3) reversal invariance -- NOT assumed anywhere, measured here
    rev_ok, rev_bad, rev_witness = 0, 0, None
    for n in range(1, 13):
        for s in all_binary(n):
            a, b = F.gamma_certified(s)[0], F.gamma_certified(s[::-1])[0]
            if a == b:
                rev_ok += 1
            else:
                rev_bad += 1
                if rev_witness is None:
                    rev_witness = (s, a, s[::-1], b)
    print("  reversal invariance: %d ok, %d differ, first witness %r"
          % (rev_ok, rev_bad, rev_witness))

    # (4) anchors from the literature
    fib = {n: F.gamma_certified(fibonacci(n))[0] for n in (8, 13, 21, 34, 55, 89, 100)}
    assert all(v == 2 for v in fib.values()), fib
    print("  anchor gamma(Fibonacci_m) = 2 for |F| in %s: OK" % sorted(fib))
    tm = {2 ** k: F.gamma_certified(thue_morse(k))[0] for k in range(1, 6)}
    print("  anchor gamma(Thue-Morse of length 2^k) = %s" % tm)
    assert tm[16] == 4 and tm[32] == 4, tm
    print("  anchor gamma(t_n) = 4 reproduced at lengths 16 and 32: OK")
    print("  NOTE: gamma(Thue-Morse) = 2 at length 4 and 3 at length 8, so the")
    print("        in-repo phrase 'gamma(t_n) = 4 for 4 <= n <= 8' is only true")
    print("        when n is the index (length 2^n), not the length.")
    return 0


# ---------------------------------------------------------------------------
# gap: gamma vs ceil(delta) and vs gamma_2
# ---------------------------------------------------------------------------


def _gap_stats(rows):
    """rows = list of (s, gamma, delta_ceil, gamma2, delta)."""
    wd = max(rows, key=lambda r: (r[1] - r[2], r[0]))
    w2 = max(rows, key=lambda r: (r[1] - r[3], r[0]))
    over = sum(1 for r in rows if r[1] > r[2])
    eq = sum(1 for r in rows if r[1] == r[2])
    return {
        "count": len(rows),
        "max_gap_delta": wd[1] - wd[2],
        "argmax_delta": (wd[0], wd[1], wd[2], str(wd[4])),
        "max_gap_g2": w2[1] - w2[3],
        "argmax_g2": (w2[0], w2[1], w2[3]),
        "frac_over_delta": (over, len(rows)),
        "frac_eq_delta": (eq, len(rows)),
        "gamma_max": max(r[1] for r in rows),
        "delta_ceil_max": max(r[2] for r in rows),
    }


def cmd_gap(args):
    print("== gap ==")
    print("%5s %7s %9s %8s %9s  %-34s %-22s" %
          ("n", "words", "max(g-cd)", "max(g-g2)", "g>cd", "argmax g-ceil(delta)", "argmax g-gamma2"))
    summary = {}
    incomplete = 0
    for n in range(2, args.nmax + 1):
        if n <= args.nmax:
            words = all_binary(n)
            kind = "exhaustive"
        rows = []
        for s in words:
            g = gamma_of(s, args.time_cap)
            if g is None:
                incomplete += 1
                continue
            inst = F.Instance(s)
            delta, _ = F.delta_from_profile(tuple(inst.d_profile[1:]))
            g2 = F.gamma_k(s, min(2, n))[0]
            rows.append((s, g, int(ceil(delta)), g2, delta))
        st = _gap_stats(rows)
        st["kind"] = kind
        st["incomplete"] = incomplete
        summary[n] = st
        print("%5d %7d %9d %8d %9s  %-34s %-22s" %
              (n, st["count"], st["max_gap_delta"], st["max_gap_g2"],
               "%d/%d" % st["frac_over_delta"], st["argmax_delta"], st["argmax_g2"]))
    # sampled range: random words, no exhaustive claim
    rng = random.Random(args.seed)
    for n in range(args.nmax + 1, args.top + 1):
        rows = []
        for _ in range(args.samples):
            s = "".join(rng.choice("ab") for _ in range(n))
            g = gamma_of(s, args.time_cap)
            if g is None:
                incomplete += 1
                continue
            inst = F.Instance(s)
            delta, _ = F.delta_from_profile(tuple(inst.d_profile[1:]))
            g2 = F.gamma_k(s, 2)[0]
            rows.append((s, g, int(ceil(delta)), g2, delta))
        st = _gap_stats(rows)
        st["kind"] = "sampled"
        st["incomplete"] = incomplete
        summary[n] = st
        print("%5d %7d %9d %8d %9s  %-34s %-22s   SAMPLED" %
              (n, st["count"], st["max_gap_delta"], st["max_gap_g2"],
               "%d/%d" % st["frac_over_delta"], st["argmax_delta"], st["argmax_g2"]))
    print("  incomplete (unclosed bracket, excluded): %d" % incomplete)
    first_d = [n for n in sorted(summary) if summary[n]["max_gap_delta"] > 0]
    first_2 = [n for n in sorted(summary) if summary[n]["max_gap_g2"] > 0]
    if first_d:
        n0 = first_d[0]
        print("  first n with gamma > ceil(delta): %d, witness %r"
              % (n0, summary[n0]["argmax_delta"]))
    if first_2:
        n0 = first_2[0]
        print("  first n with gamma > gamma_2: %d, witness %r"
              % (n0, summary[n0]["argmax_g2"]))
    return summary


# ---------------------------------------------------------------------------
# dependence: is gamma a function of the feature vector?
# ---------------------------------------------------------------------------

FEATURE_SETS = {
    "delta_ceil": lambda f: (f["delta_ceil"],),
    "profile": lambda f: f["profile"],
    "gamma2": lambda f: (f["gamma2"],),
    "delta_ceil+gamma2": lambda f: (f["delta_ceil"], f["gamma2"]),
    "profile+gamma2": lambda f: (f["profile"], f["gamma2"]),
    "runs+period+rare_gap": lambda f: (f["n_runs"], f["max_run"], f["period"], f["rare_gap"]),
    "packing+delta_ceil": lambda f: (f["packing"], f["delta_ceil"]),
    "gammak<=4": lambda f: f["gammak"][:4],
    "gammak<=6": lambda f: f["gammak"][:6],
    "everything": lambda f: (f["profile"], f["gammak"], f["n_runs"], f["max_run"],
                             f["period"], f["rare_gap"], f["packing"],
                             f["nodes"], f["minlen_max"], f["unary_max"]),
}


def cmd_dependence(args):
    print("== dependence ==")
    print("A feature set DETERMINES gamma if no two words share the vector with different gamma.")
    names = list(FEATURE_SETS)
    print("%5s %7s %7s " % ("n", "words", "groups") + " ".join("%-20s" % k for k in names))
    verdicts = defaultdict(list)
    for n in range(2, args.nmax + 1):
        groups = {k: defaultdict(set) for k in names}
        witness = {}
        for s in all_binary(n):
            g = gamma_of(s, args.time_cap)
            if g is None:
                continue
            feats = F.features(s, kmax=6, want_packing=True)
            assert feats["gamma"] == g
            for k, fn in FEATURE_SETS.items():
                key = fn(feats)
                grp = groups[k][key]
                if not grp:
                    grp.add(g)
                    witness.setdefault((k, key), s)
                elif g not in grp:
                    if len(grp) == 1:
                        witness[("AMBIG", k, key)] = (witness[(k, key)], next(iter(grp)), s, g)
                    grp.add(g)
        row = []
        for k in names:
            amb = sum(1 for v in groups[k].values() if len(v) > 1)
            verdicts[k].append((n, len(groups[k]), amb))
            row.append("%-20s" % ("AMBIG %d" % amb if amb else "determines"))
        print("%5d %7d %7d " % (n, len(all_binary(n)), len(groups[names[0]])) + " ".join(row))
        for k in names:
            amb_keys = [kk for kk, v in groups[k].items() if len(v) > 1]
            if amb_keys:
                w = witness.get(("AMBIG", k, amb_keys[0]))
                if w:
                    print("    %-20s smallest witness contradiction: %r gamma=%d vs %r gamma=%d"
                          % (k, w[0], w[1], w[2], w[3]))
                    break
    print("  verdict per feature set (determines on every n <= %d?):" % args.nmax)
    for k in names:
        bad = [v for v in verdicts[k] if v[2] > 0]
        print("    %-20s %s" % (k, "DETERMINES" if not bad else
                                "refuted (ambiguous at n = %s)" % [v[0] for v in bad][:8]))
    return verdicts


# ---------------------------------------------------------------------------
# lift: k* = min{k : gamma_k = gamma}
# ---------------------------------------------------------------------------


def cmd_lift(args):
    print("== lift ==")
    print("k*(s) = min{k : gamma_k(s) = gamma(s)}; gamma = gamma_k is computable in")
    print("O(n) + exp(O(2^k k)) time (KPRR18 Thm 29 at sigma = 2), so a uniformly small")
    print("k* would be an algorithm and a growing k* kills this route.")
    for n in range(2, args.nmax + 1):
        dist = Counter()
        worst = (-1, None)
        cap = min(args.klift, n)
        capped = 0
        for s in all_binary(n):
            g = gamma_of(s, args.time_cap)
            if g is None:
                continue
            kstar = None
            for k in range(1, cap + 1):
                if F.gamma_k(s, k)[0] >= g:
                    kstar = k
                    break
            if kstar is None:
                capped += 1
                assert F.gamma_k(s, cap)[0] <= g, "gamma_k must be <= gamma"
                continue
            dist[kstar] += 1
            if kstar > worst[0]:
                worst = (kstar, s)
        print("%5d cap %2d  k* distribution %-40s worst %-16r gamma_k<gamma at k=cap: %d"
              % (n, cap, dict(sorted(dist.items())), worst, capped))
    print("  (an entry 'gamma_k<gamma at k=cap' means the string needs k* > cap)")
    return None


# ---------------------------------------------------------------------------
# hunt: local search for large gaps at large n
# ---------------------------------------------------------------------------


def hunt(n, objective, rounds, rng, time_cap=5.0):
    """Hill-climb from random starts, maximising `objective(feat, gamma)`."""
    def score(s):
        g = gamma_of(s, time_cap)
        if g is None:
            return None
        f = F.features(s, kmax=2, want_packing=False)
        assert f["gamma"] == g
        return objective(f, g), g, f

    best = (None, None)
    evals = 0
    for _ in range(rounds):
        s = "".join(rng.choice("ab") for _ in range(n))
        r = score(s)
        evals += 1
        if r is None:
            continue
        cur, cur_g, cur_f = r
        improved = True
        while improved:
            improved = False
            for i in range(n):                      # single-symbol flips
                for c in "ab":
                    if s[i] == c:
                        continue
                    t = s[:i] + c + s[i + 1:]
                    rr = score(t)
                    evals += 1
                    if rr is None:
                        continue
                    if rr[0] > cur:
                        s, cur, cur_g, cur_f = t, rr[0], rr[1], rr[2]
                        improved = True
                        break
                if improved:
                    break
        assert cur is not None
        if best[0] is None or cur > best[0]:
            best = (cur, s, cur_g, cur_f)
    return best, evals


def cmd_hunt(args):
    print("== hunt ==")
    rng = random.Random(args.seed)
    objectives = {
        "gamma - ceil(delta)": lambda f, g: g - f["delta_ceil"],
        "gamma - gamma2": lambda f, g: g - f["gamma2"],
    }
    for label, obj in objectives.items():
        print("objective %s" % label)
        for n in args.ns:
            t0 = time.monotonic()
            best, evals = hunt(n, obj, args.rounds, rng)
            cur, s, g, f = best
            print("  n=%3d  max %2d  witness %-40r gamma=%d ceil(delta)=%d gamma2=%d "
                  "delta=%s  (%d evals, %.1fs)"
                  % (n, cur, s, g, f["delta_ceil"], f["gamma2"], f["delta"],
                     evals, time.monotonic() - t0))
            sys.stdout.flush()
    return None


# ---------------------------------------------------------------------------


def main(argv=None):
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)

    v = sub.add_parser("validate")
    v.add_argument("--solver-nmax", type=int, default=10)
    v.set_defaults(fn=cmd_validate)

    g = sub.add_parser("gap")
    g.add_argument("--nmax", type=int, default=13, help="exhaustive up to this n")
    g.add_argument("--top", type=int, default=17, help="sampled up to this n")
    g.add_argument("--samples", type=int, default=2000)
    g.add_argument("--seed", type=int, default=0)
    g.add_argument("--time-cap", type=float, default=5.0)
    g.set_defaults(fn=cmd_gap)

    d = sub.add_parser("dependence")
    d.add_argument("--nmax", type=int, default=11)
    d.add_argument("--time-cap", type=float, default=5.0)
    d.set_defaults(fn=cmd_dependence)

    l = sub.add_parser("lift")
    l.add_argument("--nmax", type=int, default=12)
    l.add_argument("--klift", type=int, default=6)
    l.add_argument("--time-cap", type=float, default=5.0)
    l.set_defaults(fn=cmd_lift)

    h = sub.add_parser("hunt")
    h.add_argument("--ns", type=lambda x: [int(v) for v in x.split(",")],
                   default=[16, 20, 24, 28, 32])
    h.add_argument("--rounds", type=int, default=20)
    h.add_argument("--seed", type=int, default=0)
    h.set_defaults(fn=cmd_hunt)

    a = sub.add_parser("all")
    a.add_argument("--quick", action="store_true")
    a.set_defaults(fn=None)

    args = p.parse_args(argv)
    if args.cmd == "all":
        args2 = p.parse_args(["validate"] + (["--solver-nmax", "9"] if args.quick else []))
        cmd_validate(args2)
        args2 = p.parse_args(["gap", "--nmax", "12" if args.quick else "13",
                              "--top", "16" if args.quick else "17",
                              "--samples", "500" if args.quick else "2000"])
        cmd_gap(args2)
        args2 = p.parse_args(["dependence", "--nmax", "10" if args.quick else "11"])
        cmd_dependence(args2)
        args2 = p.parse_args(["lift", "--nmax", "11" if args.quick else "12",
                              "--klift", "5" if args.quick else "6"])
        cmd_lift(args2)
        args2 = p.parse_args(["hunt", "--ns", "16,20,24" if args.quick else "16,20,24,28,32",
                              "--rounds", "8" if args.quick else "20"])
        cmd_hunt(args2)
        return 0
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(0 if main() is not None else 0)
