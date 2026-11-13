# Is the attractor LP gap bounded? — evidence past `n = 16`

**Verdict up front.** `15/11` is **not** the maximum.  A search to `n = 40` found instances with
gap `7/5 = 1.4` (`n = 31`), `25/18 = 1.3889` (`n = 30`) and `18/13 = 1.3846` (`n = 21`, `n = 27`).  The exhaustive claim still stands **only** for `n ≤ 16` (`lp-gap.md`); everything
above is *searched, not exhausted*, and this note says so on every row.

This note was assembled by the supervisor from the search log (`/tmp/nested.log`) after the
worker assigned to it timed out; every number below was **re-verified independently** with
`tools/gap/instance.py` (`Cover.exact_min_cover` + `Cover.lp`, exact `Fraction`s) and the
attractor re-checked at the definition level by `Instance.verify`.

## 1. Verified records

All three pass: exact `γ`, exact `LP*`, attractor verified independently of the solver.

| n | text | γ | LP* | gap | δ | γ/δ |
| --- | --- | --- | --- | --- | --- | --- |
| 21 | `011010101101011011010` | 3 | 13/6 | **18/13 = 1.3846** | 2 | 1.5 |
| 27 | `101010110101011011101010110` | 3 | 13/6 | **18/13 = 1.3846** | 2 | 1.5 |
| 30 | `010101001010100110101100101100` | 5 | 18/5 | **25/18 = 1.3889** | 3 | 1.667 |
| 31 | `0010101001010100110101100101100` | 5 | 25/7 | **7/5 = 1.4** | 3 | 1.667 |

Reproduce:

```
cd tools/gap && python3 - <<'EOF'
from instance import TextInstance
for t in ["010101001010100110101100101100"]:
    ti = TextInstance(t); g, lp, gap = ti.nodes.gap()
    print(len(t), g, lp, gap, ti.delta(), ti.inst.verify(list(ti.nodes.exact_min_cover()[1])))
EOF
```

The trend in `LP*` is the interesting part: with `γ = 3` fixed, `LP*` goes `9/4` (n=12) →
`11/5` (n=13) → `13/6` (n=21, 27), drifting **down toward `δ = 2`**, which is a hard floor.

## 2. The search, `n = 17 … 40` (searched, **not** exhaustive)

Best gap per length found by the beam arm (all instances above `15/11` are listed; the beam keeps
the top-`w` candidates per level, so a `max` below `15/11` at some `n` means *the beam* lost them,
not that none exist):

| n | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| max gap | 4/3 | 15/11 | 15/11 | 15/11 | **18/13** | 15/11 | 15/11 | 15/11 | 15/11 | 15/11 | **18/13** | 15/11 |

| n | 29 | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| max gap | 15/11 | **25/18** | 7/5 | 7/5 | 4/3 | 4/3 | 4/3 | 4/3 | 4/3 | 4/3 | 4/3 | 4/3 |

`7/5 = 1.4` at `n = 31` **is** verified (§1, fourth row): `γ = 5`, `LP* = 25/7`, attractor
re-checked at the definition level.  The `n = 32` row comes from one-symbol extensions of the same
instance and is *not* separately verified.

## 3. What the numbers say

* `15/11` is beaten, so **"the gap is maximised at `15/11` for all `n`" is dead**.  The exhaustive
  maximum to `n = 16` remains a theorem-shaped fact about `n ≤ 16` only.
* The best values cluster at `1.38 – 1.40`, up from `1.36`; over `13 → 32` the maximum moved
  by less than `0.04`.  A reading consistent with the data: slow growth (polylogarithmic), or a
  limit near `1.4–3/2`.  **The data do not distinguish these**, and this is not evidence of
  boundedness — a beam search that loses candidates at larger `n` (as it visibly does at
  `n ≥ 33`) cannot establish a maximum.
* `γ` takes the values `3`, `4`, `5`; the instances with `γ = 3, δ = 2` are the ones that reach
  `18/13`.  Since `LP* ≥ δ` is a theorem (`δ` is a lower bound for the LP, KNP's counting
  argument applies to any fractional cover), **`γ/LP* ≤ γ/δ` always**.  So the LP gap can only
  grow by growing `γ/δ`; the measured `γ − ⌈δ⌉ ≤ 3` regime would force the LP gap `→ 1` at scale.

## 4. What must be run next (and what would settle it)

1. **Exhaustive `n = 17`** — was *not* completed (the lane timed out).  `2^17 = 131 072` texts;
   the per-instance cost in the `n ≤ 16` sweep suggests this is a few hours single-threaded and
   well under an hour at `--jobs 14`.  Until that runs, the only exhaustive statement is `n ≤ 16`.
2. ~~Re-verify the `7/5` row~~ — done: `n = 31`, `γ = 5`, `LP* = 25/7`, gap `7/5`, attractor
   independently verified (§1).  Still to do: the `n = 32` extension.
3. **Minimise `LP*` subject to `γ = 3`, `δ = 2`** — the sharp experiment.  `LP*` is rational and
   floor-bounded by `2`; the observed drift `9/4 → 11/5 → 13/6` suggests the supremum of the gap
   in that family is `3/2`, attained in the limit.  If `LP*` reaches `2` exactly, the gap is
   `3/2`; if it stalls at `> 2 + c`, the family saturates below `3/2`.
4. **A proof either way** is a different matter: boundedness needs a rounding argument, and
   unboundedness needs a construction with `γ/δ → ∞` on binary text (`γ − δ` bounded in every
   measurement so far, so this would contradict the current picture and be a major result).

## 5. Status of the claims in `lp-gap.md` after this note

| claim | status |
| --- | --- |
| max `γ/LP* = 15/11` **for `n ≤ 16`**, exhaustive | stands |
| `15/11` is the maximum **over all lengths** | **refuted** (`7/5` at `n = 31`, `25/18` at `n = 30`, `18/13` at `n = 21, 27`) |
| `LP* = 11/5`, `γ = 3`, gap `15/11` on `0110101101110` | kernel-checked, `SortBounds/Projects/AttractorLP/` |
| the gap is bounded | **open**, and the data neither establishes nor refutes it |
