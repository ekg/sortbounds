#!/bin/sh
# run.sh -- reproduce the results table in README.md.
#
# Every row is one text: delta (exact), the certified packing lower bound, the
# bracket [lb, ub] the anytime search ends with, and the upper bound it had
# reached at 1 s, 10 s and 60 s of wall clock.  gamma is reported as exact only
# when it is: n <= 14 (exhaustive) or the bracket is closed (lb == ub).
#
#   sh run.sh          # about five minutes (four rows use the full 60 s)
#
# stdlib only; nothing here writes to the repository.
set -e
cd "$(dirname "$0")"
exec python3 - "$@" <<'PY'
import sys
import time
from fractions import Fraction

import anytime
from instance import Instance, factor_str

sys.path.insert(0, "../repmeter")
from measure import greedy_attractor, gen_text   # noqa: E402

BUDGET = 60.0
TIMES = (1.0, 10.0, 60.0)


def random_binary(n, seed):
    import random
    rng = random.Random(seed)
    return [rng.getrandbits(1) for _ in range(n)]


def thue_morse(k):
    t = [0]
    for _ in range(k):
        t = t + [1 - c for c in t]
    return t


CASES = [
    ("a", list(b"a")),
    ("ab", list(b"ab")),
    ("ababa", list(b"ababa")),
    ("mississippi", list(b"mississippi")),
    ("abracadabra", list(b"abracadabra")),
    ("thue-morse 2^4", thue_morse(4)),
    ("thue-morse 2^6", thue_morse(6)),
    ("thue-morse 2^8", thue_morse(8)),
    ("thue-morse 2^10", thue_morse(10)),
    ("fibonacci F_14", gen_text("fibonacci:14")),
    ("fibonacci F_18", gen_text("fibonacci:18")),
    ("random-binary 64 seed 3", random_binary(64, 3)),
    ("random-binary 256 seed 1", random_binary(256, 1)),
    ("random-binary 512 seed 1", random_binary(512, 1)),
    ("random-binary 1024 seed 1", random_binary(1024, 1)),
    ("random-binary 2048 seed 1", random_binary(2048, 1)),
]


def ub_at(steps, t):
    """The upper bound verified by time t; None if no attractor existed yet."""
    ub = None
    for step in steps:
        if step["t"] <= t and not step.get("done"):
            ub = step["ub"]
    return "none yet" if ub is None else ub


def main():
    print("| text | n | delta | pack LB | greedy+prune | repmeter greedy "
          "| ub @ 1 s | ub @ 10 s | ub @ 60 s | gamma | bracket |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    t_start = time.time()
    for name, sym in CASES:
        t0 = time.time()
        inst = Instance(sym)
        steps = list(anytime.search(inst, budget_s=BUDGET, seed=0))
        final = steps[-1]
        g = len(anytime.prune(inst, anytime.greedy(inst)))
        if inst.n <= 1024:
            rep = len(greedy_attractor(sym))
        else:
            rep = None
        if final["lb"] >= final["ub"]:
            exact = "%d (bracket closed)" % final["ub"]
        elif inst.n <= 14:
            sol, _ = anytime.exact_gamma(inst, node_cap=10 ** 9, lb=final["lb"])
            exact = "%d (exhaustive)" % len(sol) if sol is not None else "not computed"
        else:
            exact = "not computed"
        tower = inst.delta_argmax()
        frac = Fraction(tower[0], tower[1])
        print("| %s | %d | %s = %.4f | %d | %d | %s | %s | %s | %s | %s | [%d, %d] |"
              % (name, inst.n, frac, float(inst.delta()), final["packing"],
                 g, "not computed" if rep is None else rep,
                 ub_at(steps, 1.0), ub_at(steps, 10.0), ub_at(steps, 60.0),
                 exact, final["lb"], final["ub"]))
        sys.stderr.write("  %-26s n=%5d done in %5.1fs\n" % (name, inst.n,
                                                             time.time() - t0))
    sys.stderr.write("total %.1fs\n" % (time.time() - t_start))
    return 0


sys.exit(main())
PY
