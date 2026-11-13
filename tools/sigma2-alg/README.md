# tools/sigma2-alg — is the minimum attractor computable at `σ = 2`?

**Status: open, with two of the four questions about it settled.** This lane takes the *opposite*
bet to `../sigma2/` (which tried to reduce hardness *into* the binary case): it asks whether
`γ` has exploitable structure at `σ = 2`. The verdict is **no structure found that yields an
algorithm**, plus two sharp results: `γ ≤ γ₂ + c` is **refuted for every constant `c`** (proved, via
binary de Bruijn words), and `γ ≤ ⌈δ⌉ + 3` survives every test I ran while `γ ≤ ⌈δ⌉ + 2` is false.
The report with every number, witness and label is `sigma2-algorithm.md`.

Nothing here claims NP-hardness, and nothing here refutes hardness. See
`docs/research/hardness-attractor.md` §3–5 for why `σ = 2, k = n` is OPEN in the literature.

## Files

| file | what it is |
|---|---|
| `features.py` | exact structural features of a binary word (`d_k` profile, exact `δ`, `γ_k` for small `k`, runs, shortest period, rare-symbol gap, certified packing, suffix-tree node statistics); `gamma_certified` (returns `γ` only when the bracket is **closed**, else raises `NotClosed`); `gamma_k` (an independent, definition-level exact `k`-attractor solver) |
| `check.py` | seven experiments: `validate`, `gap`, `dependence`, `lift`, `bruijn`, `families`, `hunt` |
| `sigma2-algorithm.md` | the report: gap tables by `n`, what determines `γ` and what does not, the proof that `γ − γ₂` is unbounded, the `k*` route that dies, and the surviving conjecture |

Both modules are stdlib-only Python 3 and read `../attractor/{instance,anytime}.py` (suffix array,
suffix-tree set-cover model, the anytime search) and `../repmeter/measure.py` (SA/LCP/`d_k`) without
modifying them. Nothing is written outside `tools/sigma2-alg/`.

## The model (identical to `../attractor`)

`Γ ⊆ {0..n−1}` is an attractor iff every **distinct** factor has *some* occurrence crossed by `Γ`.
Note the quantifier: a 1-attractor has size `σ`, not `n`. `γ` is the minimum size; `γ_k` the minimum
over factors of length `≤ k`, so `γ_1 ≤ γ_2 ≤ … ≤ γ_n = γ`, and at `σ = 2` every **fixed** `k` is
polynomial (KPRR18 Thm 29), which is why `γ_k` is worth attacking.

## Trust

* `γ` is never guessed: `features.gamma_certified` needs (i) a position set that passes the
  definition-level `Instance.witness`, (ii) an exhausted DFS over every smaller position set,
  (iii) `|Γ| ≥ ⌈δ⌉`. It is also capped in nodes *and* wall-clock (5 s in the sweeps) and raises
  instead of returning when the bracket stays open; `check.py` counts those separately.
* Two independent solvers are cross-checked (`gamma_k(s, n)` builds the factor universe from scratch
  and agrees with the suffix-tree route on all 1023 words with `n ≤ 10`).
* Literature anchors reproduce: `γ(Fibonacci) = 2`, `γ(Thue–Morse of length 16, 32) = 4`. The
  repo phrase "`γ(t_n) = 4` for `4 ≤ n ≤ 8`" holds only with `n` the *index*; measured values are
  `2, 2, 3, 4, 4` at lengths `2, 4, 8, 16, 32`.
* Every loop asserts progress (exhausted node caps raise; `k` loops assert monotone increase).

## Commands

```
cd tools/sigma2-alg
timeout  600 python3 check.py validate   --solver-nmax 10
timeout 1500 python3 check.py gap        --nmax 13 --samples 2000 --top 17
timeout  500 python3 check.py dependence --nmax 10
timeout  420 python3 check.py lift       --nmax 12 --klift 5
timeout 1200 python3 check.py bruijn     --kmax 6
timeout  550 python3 check.py families   --maxlen 64
timeout  600 python3 check.py hunt       --ns 28,32,40 --rounds 10
timeout 1800 python3 check.py all --quick        # smoke test, a couple of minutes
```

## The four answers, one line each

1. **Is `γ` a function of a few cheap features?** No. `⌈δ⌉`, the `d_k` profile, `γ₂`, run structure,
   period, rare-symbol gap and packing are each refuted by an explicit pair of words with the same
   feature vector and different `γ` — the smallest: `aaabba` (`γ=2`) vs `aababb` (`γ=3`), **same
   profile `(2,4,4,3,2,1)`**.
2. **Is `γ ≤ γ₂ + c`?** No, for every `c` (PROVED): `γ₂ ≤ 6` always while `γ ≥ δ ≥ 2^k/k` on the
   binary de Bruijn word of order `k`; measured `γ − γ₂ = 9` already at `n = 69`.
3. **Is `γ ≤ ⌈δ⌉ + c`?** `c = 0` fails at `n = 6`, `c = 1` at `n = 12`, `c = 2` at `n = 32`
   (`γ = 6 = 2δ`). `c = 3` was not refuted up to `n = 48`. On de Bruijn words `γ = ⌈δ⌉` exactly.
4. **Does an exact algorithm fall out (e.g. `γ = γ_K` for small `K`)?** No: `k*(s) = min{k : γ_k = γ}`
   has maximum `1, 2, 3, 4, 5` at `n = 5, 6, 8, 10, 12` — it grows with `n`, so the polynomial
   `γ_k` machinery cannot reach `γ`.
