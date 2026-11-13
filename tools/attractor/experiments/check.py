#!/usr/bin/env python3
"""check.py -- independent re-verification of every row in results.json.  Non-zero on failure.

The claim this file defends is narrow and checkable:

  every bracket in the results table has BOTH endpoints certified, re-derived here from
  the text alone, and every "gamma = k" claim is the exact answer, not an upper bound.

What is re-derived, and how (nothing here trusts run_families.py's numbers):

  * the text is rebuilt from its spec, so the row is about the text it says it is -- and
    each family's defining property is asserted (a de Bruijn word really contains every
    length-k word once cyclically; a Fibonacci word really has factor complexity k+1; a
    mechanical word of slope p/q really is q-periodic with p ones per period; S S^R really
    is the reverse square);
  * delta is recomputed exactly and compared as a rational, not as a float;
  * the upper bound is checked by `Instance.verify`, the definition-level attractor test
    (every distinct factor has an occurrence crossing a position of the reported set), and
    the reported set's size must equal the reported ub;
  * the lower bound is checked from three independent certificates: ceil(delta), the
    recorded packing family (re-certified from the text by `certify_packing`), a freshly
    rebuilt packing family, and -- whenever lb exceeds both -- a fresh complete DFS at
    lb-1 that must report *infeasible* (that is the only way lb may exceed ceil(delta));
  * a row that claims gamma exactly is rechecked: a closed bracket must have lb == ub, and
    a row under the complete-DFS limit must reproduce the same size from a fresh DFS;
  * the counts quoted in results.json's summary are recomputed;
  * the three tables in docs/research/gamma-delta-table.md must appear VERBATIM in the
    generated output, so a hand-edited number would fail here.  (A row may not quietly
    vanish from the note either: the row count in the note is checked.)

Run:  timeout 1800 python3 check.py           (about a minute)
      timeout 1800 python3 check.py --quick   (skip the DFS re-proofs)
"""

import argparse
import faulthandler
import json
import os
import sys
import time
from fractions import Fraction
from math import ceil

import run_families as RF          # sets up sys.path for the two tools below
import anytime                    # noqa: E402
from instance import Instance     # noqa: E402

FAILURES = []
CHECKS = [0]
DOC_PATH = os.path.normpath(os.path.join(RF._HERE, os.pardir, os.pardir, os.pardir,
                                         "docs", "research", "gamma-delta-table.md"))


def check(cond, msg):
    CHECKS[0] += 1
    if not cond:
        FAILURES.append(msg)
        print("FAIL  %s" % msg)
    return cond


# --------------------------------------------------------------------------
# [1] the families are the families they claim to be
# --------------------------------------------------------------------------


def test_family_definitions(rows):
    print("[1] every row's text has the property its family name asserts")
    seen = set()
    t0 = time.time()
    for row in rows:
        spec = row["spec"]
        key = json.dumps(spec, sort_keys=True)
        if key in seen:                     # one check per distinct text
            continue
        seen.add(key)
        sym = RF.build_text(spec)
        kind = spec["kind"]
        if kind == "unary":
            check(set(sym) == {0}, "unary text has more than one symbol")
            check(len(sym) == spec["n"], "unary text has the wrong length")
        elif kind == "periodic":
            check(all(sym[i] == i % 2 for i in range(len(sym))),
                  "periodic (ab)^m text is not 'abab...'")
        elif kind == "fibonacci":
            # A finite prefix is not the infinite Sturmian word: p(k) = k+1 must fail
            # eventually (d_k <= n-k+1 near the end).  What is asserted is the part the
            # note uses: d_1 = 2, the Sturmian complexity k+1 on the band k <= n/3, and
            # d_k <= 2k everywhere -- the last two give delta = 2 exactly.
            inst = Instance(sym)
            prof = inst.d_profile
            n = inst.n
            check(prof[1] == 2, "Fibonacci word F_%d has d_1 = %d, want 2"
                  % (spec["k"], prof[1]))
            bad = [k for k in range(1, n // 3 + 1) if prof[k] != k + 1]
            check(not bad, "Fibonacci word F_%d breaks d_k = k+1 at k = %s (n/3 = %d)"
                  % (spec["k"], bad[:1], n // 3))
            heavy = [k for k in range(1, n + 1) if prof[k] > 2 * k]
            check(not heavy, "Fibonacci word F_%d has d_k > 2k at k = %s"
                  % (spec["k"], heavy[:1]))
        elif kind == "thue-morse":
            k = spec["k"]
            want = RF.thue_morse_word(k)
            check(sym == want, "thue-morse:%d is not t_{k-1} complement(t_{k-1})" % k)
            check(len(sym) == 1 << k, "thue-morse:%d has length %d, want %d"
                  % (k, len(sym), 1 << k))
        elif kind == "debruijn":
            k, sigma = spec["k"], spec.get("sigma", 2)
            check(len(sym) == sigma ** k, "de Bruijn text has length %d, want %d"
                  % (len(sym), sigma ** k))
            grams = {tuple(sym[(i + j) % len(sym)] for j in range(k))
                     for i in range(len(sym))}
            check(len(grams) == sigma ** k,
                  "de Bruijn k=%d sigma=%d has %d distinct cyclic k-grams, want %d"
                  % (k, sigma, len(grams), sigma ** k))
        elif kind == "mechanical":
            p, q, n = spec["p"], spec["q"], spec["n"]
            check(all(sym[i] == sym[i + q] for i in range(n - q)),
                  "mechanical word of slope %d/%d is not %d-periodic" % (p, q, q))
            check(sum(sym[:q]) == p, "mechanical word has %d ones per period, want %d"
                  % (sum(sym[:q]), p))
            check(len(sym) == n, "mechanical word has the wrong length")
        elif kind == "random":
            check(len(sym) == spec["n"], "random text has the wrong length")
            check(set(sym) <= set(range(spec.get("sigma", 2))),
                  "random text uses symbols outside its alphabet")
            again = RF.random_word(spec["n"], spec["seed"], spec.get("sigma", 2))
            check(sym == again, "random text is not reproducible from its seed")
        elif kind == "runs":
            L, periods = spec["L"], spec["periods"]
            check(len(sym) == 2 * L * periods, "run-length text has the wrong length")
            ok = True
            for j in range(periods):
                base = 2 * L * j
                ok = ok and len(set(sym[base:base + L])) == 1
                ok = ok and len(set(sym[base + L:base + 2 * L])) == 1
                ok = ok and sym[base] != sym[base + L]
            check(ok, "run-length text is not a^L b^L repeated")
        elif kind == "square":
            m = spec["m"]
            head, tail = sym[:m], sym[m:]
            if spec.get("reverse"):
                check(tail == head[::-1], "S S^R text's second half is not S reversed")
            else:
                check(tail == head, "S S text's second half is not S")
        else:                               # pragma: no cover - defensive
            check(False, "unknown spec kind %r" % (kind,))
    print("    %d distinct texts, %d checks, %.1fs"
          % (len(seen), CHECKS[0], time.time() - t0))


# --------------------------------------------------------------------------
# [2] the bracket endpoints, re-derived from the text
# --------------------------------------------------------------------------


def rederive_lb(inst, row, quick):
    """(lb, provenance list) recomputed from scratch; asserts every step."""
    delta = inst.delta()
    delta_ceil = int(ceil(delta))
    pack_k, pack_w = inst.packing_bound(seed=0, restarts=32)
    ok_fresh, _ = inst.certify_packing(pack_w)
    check(ok_fresh, "%s: a freshly built packing family does not re-certify" % row["label"])
    base = max(delta_ceil, pack_k)
    provenance = ["ceil(delta) = %d" % delta_ceil, "packing = %d" % pack_k]
    lb = base
    if row["lb"] > base:
        if quick:
            provenance.append("exact tail (not re-proved: --quick)")
            lb = row["lb"]
        else:
            # the same prune the search used: a certified packing family is a free
            # lower bound at every DFS node, and without it the tree can be enormous.
            packing_mask = 0
            for v in row.get("packing_nodes") or []:
                packing_mask |= 1 << int(v)
            sol, status = anytime.decision(inst, row["lb"] - 1, node_cap=10 ** 7,
                                           packing_mask=packing_mask)
            check(status == "infeasible",
                  "%s: lb=%d was not supported by a completed DFS at k=%d (status %r)"
                  % (row["label"], row["lb"], row["lb"] - 1, status))
            check(sol is None, "%s: the DFS at k=%d found a smaller attractor"
                  % (row["label"], row["lb"] - 1))
            if status == "infeasible":
                lb = row["lb"]
                provenance.append("DFS proved k=%d infeasible" % (row["lb"] - 1))
    return lb, provenance, delta


def test_row_endpoints(rows, quick):
    print("[2] every row: delta exact, ub verified, lb re-certified")
    t0 = time.time()
    for row in rows:
        check(row["status"] in ("computed", "not computed"),
              "%s: unknown status %r" % (row["label"], row["status"]))
        if row["status"] != "computed":
            check(bool(row.get("reason")), "%s: 'not computed' without a reason"
                  % row["label"])
            continue
        sym = RF.build_text(row["spec"])
        inst = Instance(sym)
        check(inst.n == row["n"], "%s: n %d != %d" % (row["label"], row["n"], inst.n))
        # delta: exact rational comparison
        lb, provenance, delta = rederive_lb(inst, row, quick)
        check(delta == Fraction(row["delta_num"], row["delta_den"]),
              "%s: delta %s != recorded %d/%d"
              % (row["label"], delta, row["delta_num"], row["delta_den"]))
        check(row["delta_ceil"] == int(ceil(delta)),
              "%s: ceil(delta) %d != %d" % (row["label"], row["delta_ceil"],
                                            int(ceil(delta))))
        # ub: the definition-level attractor test, on the reported positions
        gamma = row["gamma"]
        check(inst.verify(gamma), "%s: the reported attractor fails the definition"
              % row["label"])
        check(all(0 <= p < inst.n for p in gamma),
              "%s: an attractor position is out of range" % row["label"])
        check(len(set(gamma)) == len(gamma), "%s: repeated attractor position"
              % row["label"])
        check(len(gamma) == row["ub"], "%s: ub %d != |gamma| %d"
              % (row["label"], row["ub"], len(gamma)))
        # lb: certified, and not weaker than the re-derivation
        check(lb <= row["lb"], "%s: re-derived lb %d < recorded %d"
              % (row["label"], lb, row["lb"]))
        check(row["lb"] <= row["ub"], "%s: lb %d > ub %d"
              % (row["label"], row["lb"], row["ub"]))
        # the recorded packing family must itself re-certify (independent witness)
        nodes = row["packing_factors"]
        if nodes:
            # certify_packing only reads the factor out of each triple; the node index is
            # not part of the certificate, so 0 stands in for it.
            witnesses = [(0, [int(c) for c in f], RF.factor_str(inst.sym, f))
                         for f in nodes]
            ok, detail = inst.certify_packing(witnesses)
            check(ok, "%s: recorded packing family does not re-certify: %s"
                  % (row["label"], detail))
            check(len(nodes) <= row["lb"],
                  "%s: recorded packing has %d factors but lb is %d"
                  % (row["label"], len(nodes), row["lb"]))
        # the gap fields are what the table says they are
        check(row["gap_lo"] == row["lb"] - row["delta_ceil"],
              "%s: gap_lo is inconsistent with lb and ceil(delta)" % row["label"])
        check(row["gap_hi"] == row["ub"] - row["delta_ceil"],
              "%s: gap_hi is inconsistent with ub and ceil(delta)" % row["label"])
        check(row["gap_lo"] >= 0,
              "%s: gamma >= ceil(delta) violated (lb %d < ceil(delta) %d)"
              % (row["label"], row["lb"], row["delta_ceil"]))
        if row["closed"]:
            check(row["lb"] == row["ub"],
                  "%s: row claims a closed bracket with lb %d != ub %d"
                  % (row["label"], row["lb"], row["ub"]))
        if row["gamma_exact"] is not None:
            check(row["gamma_exact"] == row["ub"],
                  "%s: gamma_exact %d != ub %d" % (row["label"], row["gamma_exact"],
                                                   row["ub"]))
            check(row["gamma_exact"] >= row["lb"],
                  "%s: gamma_exact %d < lb %d" % (row["label"], row["gamma_exact"],
                                                  row["lb"]))
            if "closed" in row["gamma_exact_how"]:
                check(row["closed"], "%s: 'bracket closed' on an open row"
                      % row["label"])
            else:
                check(inst.n <= RF.EXACT_GAMMA_N,
                      "%s: gamma claimed exact for n > %d without a closed bracket"
                      % (row["label"], RF.EXACT_GAMMA_N))
        elif inst.n <= RF.EXACT_GAMMA_N:
            check(False, "%s: n <= %d but gamma was not computed exactly"
                  % (row["label"], RF.EXACT_GAMMA_N))
        if row["path"] != "search":
            check(bool(row["path_note"]),
                  "%s: fallback path without a recorded reason" % row["label"])
        print("    %-30s n=%5d delta=%-9s lb=%4d (%s) ub=%4d %s"
              % (row["label"], inst.n, delta, row["lb"], provenance[-1], row["ub"],
                 "CLOSED" if row["closed"] else "open"))
    print("    %d checks, %.1fs" % (CHECKS[0], time.time() - t0))


# --------------------------------------------------------------------------
# [3] an exhaustive gamma is the exhaustive gamma
# --------------------------------------------------------------------------


def test_exhaustive_rows(rows, quick):
    print("[3] rows with gamma exact from a complete DFS reproduce the same size")
    if quick:
        print("    skipped (--quick)")
        return
    t0 = time.time()
    for row in rows:
        if row["status"] != "computed" or row["gamma_exact"] is None:
            continue
        if "complete DFS" not in row["gamma_exact_how"]:
            continue
        inst = Instance(RF.build_text(row["spec"]))
        sol, _proved = anytime.exact_gamma(inst, node_cap=RF.BIG_NODE_CAP,
                                          lb=row["lb"])
        check(sol is not None, "%s: the complete DFS did not finish"
              % row["label"])
        if sol is not None:
            check(inst.verify(sol), "%s: DFS solution fails the definition"
                  % row["label"])
            check(len(sol) == row["gamma_exact"],
                  "%s: DFS gamma %d != recorded %d"
                  % (row["label"], len(sol), row["gamma_exact"]))
    print("    %d checks, %.1fs" % (CHECKS[0], time.time() - t0))


# --------------------------------------------------------------------------
# [4] the note's tables are the generated ones, byte for byte
# --------------------------------------------------------------------------


def test_note_matches_results(rows, payload, allow_doc_drift=False):
    print("[4] docs/research/gamma-delta-table.md carries the generated tables verbatim")
    blocks = {"table": RF.render_table(rows),
              "verdicts": RF.render_verdicts(rows),
              "trends": RF.render_trends(rows),
              "rates": RF.render_rates(rows),
              "summary": RF.render_summary(rows)}
    for name, text in blocks.items():
        path = os.path.join(RF._HERE, "%s.md" % name)
        check(os.path.exists(path), "%s.md is missing from the experiments directory"
              % name)
        if os.path.exists(path):
            with open(path) as fh:
                on_disk = fh.read().rstrip("\n")
            check(on_disk == text,
                  "%s.md does not match what this run's results.json renders to" % name)
    if not os.path.exists(DOC_PATH):
        if allow_doc_drift:
            print("    NOTE: %s is absent; the note check is skipped (--allow-doc-drift)"
                  % DOC_PATH)
        else:
            check(False, "%s is missing; the note must carry the tables" % DOC_PATH)
        return
    with open(DOC_PATH) as fh:
        doc = fh.read()
    for name in ("verdicts", "table", "trends", "rates"):
        if allow_doc_drift and blocks[name] not in doc:
            print("    NOTE: the note's %r table is stale (--allow-doc-drift): "
                  "regenerate it from results.json" % name)
            continue
        check(blocks[name] in doc,
              "%s does not contain the generated %r table verbatim" % (DOC_PATH, name))
    for line in blocks["summary"].splitlines():
        check(line in doc, "%s does not contain the generated summary line %r"
              % (DOC_PATH, line))
    # every computed row must be visible in the note with its own numbers
    missing = [row["label"] for row in rows
               if row["status"] == "computed"
               and "| %s |" % row["label"] not in doc]
    check(not missing, "%d rows are in results.json but not in the note: %s"
          % (len(missing), missing[:5]))
    print("    %d checks" % CHECKS[0])


# --------------------------------------------------------------------------
# [5] the summary counts are recomputed, not trusted
# --------------------------------------------------------------------------


def test_summary_counts(rows, payload):
    print("[5] the summary counts are recomputed")
    computed = [r for r in rows if r["status"] == "computed"]
    closed = [r for r in computed if r["closed"]]
    exact = [r for r in computed if r["gamma_exact"] is not None]
    eq = [r for r in exact if r["gamma_exact"] == r["delta_ceil"]]
    gt = [r for r in exact if r["gamma_exact"] > r["delta_ceil"]]
    summary = RF.render_summary(rows)
    check(summary == payload["summary"], "the recorded summary is not this run's")
    check("computed: %d" % len(computed) in summary, "computed count is not in summary")
    check("CLOSED: %d of %d" % (len(closed), len(computed)) in summary,
          "closed count is not in summary")
    check("gamma == ceil(delta): %d" % len(eq) in summary,
          "equality count is not in summary")
    check("gamma > ceil(delta): %d" % len(gt) in summary,
          "strict-gap count is not in summary")
    check(len(eq) + len(gt) == len(exact), "every exact gamma is either = or > ceil(delta)")
    print("    %d checks" % CHECKS[0])


def main(argv=None):
    faulthandler.dump_traceback_later(1800, exit=True)     # never hang
    ap = argparse.ArgumentParser(description="re-verify every bracket in results.json")
    ap.add_argument("--results", default=os.path.join(RF._HERE, "results.json"))
    ap.add_argument("--allow-doc-drift", action="store_true",
                    help="treat a stale/absent note as a warning (numbers on "
                         "open-bracket rows move between machines)")
    ap.add_argument("--quick", action="store_true",
                    help="skip the DFS re-proofs of lb (much faster, weaker)")
    args = ap.parse_args(argv)

    t0 = time.time()
    check(os.path.exists(args.results), "results.json is missing: run run_families.py")
    if not os.path.exists(args.results):
        return 1
    with open(args.results) as fh:
        payload = json.load(fh)
    rows = payload["rows"]
    check(bool(rows), "results.json has no rows")
    check(payload["exact_gamma_n"] == RF.EXACT_GAMMA_N,
          "results.json was produced with a different EXACT_GAMMA_N")

    test_family_definitions(rows)
    test_row_endpoints(rows, args.quick)
    test_exhaustive_rows(rows, args.quick)
    test_note_matches_results(rows, payload, args.allow_doc_drift)
    test_summary_counts(rows, payload)

    print("\n%d checks, %d failures, %.1fs" % (CHECKS[0], len(FAILURES),
                                              time.time() - t0))
    if FAILURES:
        print("FAILED")
        for f in FAILURES[:20]:
            print("  %s" % f)
        return 1
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
