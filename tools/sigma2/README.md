# tools/sigma2 — a binary-alphabet reduction to the minimum attractor: attempt and refutation

**Status: closed negative result.** Three explicit polynomial reductions from
VERTEX COVER to "minimum full attractor (`k = n`) of a binary word" are stated and
tested exhaustively with exact `γ`; all three are refuted, and refuted for *every*
threshold function, not just for the threshold they were designed around. The full
account, with the lemmas and the scope of what remains unproved, is
`sigma2-gadget.md` (written to the run's artifact directory; the lane's contract is
the section headings of that file).

The question being attacked is **open** — see `docs/research/hardness-attractor.md`
§3–4 and `docs/research/hardness-related-binary.md` §6–7: every published hardness
reduction for the minimum attractor uses an alphabet that grows with `n`. Nothing in
this directory claims NP-hardness, and nothing here refutes hardness either.

## Files

| file | what it is |
|---|---|
| `reduce.py` | the source problem (vertex cover, brute-force `τ`), the three text constructions (`tags`, `tags_sep`, `hubs`), their size bounds, the ledger's prescribed charge pattern, and the isomorphism-class enumerator |
| `check.py` | two independent exact `γ` solvers (suffix-tree node universe + definition level, required to agree), definition-level attractor verification, exhaustive enumeration over graphs, the four claim tests, and `ledger_breakdown` (which cell holds which charge, and which factor classes tie two blocks together) |
| `sigma2-gadget.md` | the report: claims with PROVED / COMPUTATIONALLY-CHECKED labels, the failure witnesses, the nest-or-cross dichotomy (Cor. 8.3), and §9 "what remains unproved" |

Nothing here writes outside `tools/sigma2/`; both modules are stdlib-only and read
`../attractor/instance.py` and `../repmeter/measure.py` for suffix arrays.

## The claim that is tested

For every graph `G` on `n` vertices with `m` edges:

```
gamma(T_G) <= m + q      <=>      tau(G) <= q        (CLAIM, threshold form)
```

equivalent, since both sides are integers, to the identity `gamma(T_G) = m + tau(G)`.
The **ledger** that would make it true is in `reduce.py`'s module docstring and is
proved arithmetically in `sigma2-gadget.md` §4. The construction sizes are `O((n+m)
log n)` and are asserted per instance by `check.py`.

## What the check does (and why the numbers can be trusted)

* `gamma_exact` searches the suffix-tree node universe (`../attractor/instance.py`,
  rule R1) by iterative deepening under a greedy upper bound, so the result is a
  certificate: an explicit attractor of that size plus an exhausted search below it.
* Every returned attractor is re-verified from the definition, and every text with
  `|T| ≤ 40` is also solved by `gamma_exact_definition`, which knows nothing about
  suffix trees; a disagreement **raises**, it is never reported.
* A node/time cap raises `SearchIncomplete`; `check.py` counts those instances in a
  separate `incomplete` bucket. An incomplete instance is never counted as a pass.

## Commands

```
cd tools/sigma2
python3 check.py --variant tags     --nmax 4 --quiet                       # 75 graphs, ~4 s
python3 check.py --variant tags_sep --nmax 4 --quiet                       # 75 graphs, ~51 s
python3 check.py --variant hubs     --nmax 3 --time-cap 10 --node-cap 2000000
python3 check.py --variant hubs     --nmax 4 --mmax 2 --time-cap 10 --node-cap 2000000
python3 check.py --variant tags --labels --relabels 0 --nmax 4 --quiet     # label variance
python3 check.py --variant tags --correlate --nmax 4 --quiet                # gamma vs delta/|T|/m/tau
python3 check.py --variant tags --nmax 1 --ledger-check 5 --quiet           # Lemma 4.1 arithmetic
python3 check.py --variant tags --witness 3 0-1,0-2,1-2                    # ledger breakdown
```

`--json FILE` dumps the per-instance rows (edges, `τ`, `γ`, attractor, excess) so a
reviewer can re-verify any single instance. Each run prints a JSON summary with the
instance count, the `τ`/`γ`/excess histograms, the `incomplete` count, and the
failure rows.

Options: `--nmax` (vertex count), `--mmax` (edge-count cap, the lever that keeps
texts short enough for exact `γ`), `--node-cap`, `--time-cap`, `--relabels 0` (all
permutations) or `k` (k random ones), `--monotone` (subgraph scan),
`--correlate` (Pearson of `γ` against `δ`, `|T|`, `m`, `τ`), `--witness N e1,e2,…`.

## Results in one line each

* `tags`: 56/75 instances violate the ledger (`γ` ranges from `m+τ−2` to `m+τ+3`),
  and the text is not isomorphism-invariant: `10` of the `11` graph classes on 4
  vertices take two or more `γ` values across labelings.
* `tags_sep`: 43/75 violate it; still not isomorphism-invariant.
* `hubs`: 22/22 decided instances have `γ = m + τ + {2…7}` — the hub region is never
  inert, so the payment is never optional (Corollary 8.3 of the report).
* The refutation that does not depend on the threshold: `τ=1` graphs with `γ=5` next
  to a `τ=2` graph with `γ=3` in the same `tags` family (`n=4`, `m=2`, `|T|=24`).
