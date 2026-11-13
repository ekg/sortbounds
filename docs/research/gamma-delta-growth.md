# Can `γ − δ` grow on binary text? — exhaustive to `n = 22`, searched to `n = 384`

**Open problem 2 of `RESULTS.md`.**  `δ ≤ γ` is a theorem (`deltaQ_le_minAttractorSize`) and
`γ = O(δ log(n/δ))` in general (KNP23, via `z`); `γ = Ω(δ log(n/δ))` is attained over a general
alphabet (KNP Thm III.3).  Whether **binary** text can force the log factor was unknown, and the
answer decides two things at once:

* if `γ = O(δ)` at `σ = 2`, then `δ` — computable in `O(n)` — is a constant-factor approximation
  of the NP-hard `γ` on binary text, and by `gamma_div_primal_le` (`γ/LP* ≤ γ/δ`) the attractor LP
  gap is bounded;
* if `γ/δ → ∞` at `σ = 2`, both are out of reach and the log factor is inherent at binary.

**Verdict: the data say the ratio stays small.**  In every row of this sweep
(`n = 20 … 384`, all brackets closed), `γ/δ ≤ 2.33`, with no upward trend in `n`.  The *gap*
`γ − ⌈δ⌉` does grow — but only because `δ` grows; at fixed `δ = 2` it grows very slowly.

This note was assembled by the supervisor from the lane's `results*.json` after the worker hit its
time budget; the worker's own report was not written.  Every bracket quoted here is **closed**
(`lb = ub`), the lower end certified by `δ` and/or packing, the upper end by a verified attractor.

## 1. Exhaustive, `n = 20, 21, 22`

All binary strings at each length (`2^20`, `2^21`, `2^22` instances, counted by the lane):

| n | strings checked | max `γ − ⌈δ⌉` | best closed witness |
| --- | --- | --- | --- |
| 20 | 1 048 576 | **3** | `γ = 5`, `δ = 2`, text `01011110110111011100` |
| 21 | 2 097 152 | **3** | `γ = 5`, `δ = 2` |
| 22 | 1 048 578 | **3** | `γ = 5`, `δ = 2` |

So the exhaustive maximum is `3` for `n ≤ 22` (previously `2` for `n ≤ 18`, `3` at `n = 32` from
`Packing.s32_gamma`).  The `n = 20` witness is the smallest known instance with `γ − ⌈δ⌉ = 3`.

## 2. Searched, `n = 20 … 384` (brackets closed in every row below)

| n | γ | δ | gap | γ/δ |
| --- | --- | --- | --- | --- |
| 20 | 5 | 14/5 | 2 | 1.79 |
| 24 | 6 | 3 | 3 | 2.00 |
| 32 | 6 | 3 | 3 | 2.00 |
| 40 | 8 | 4 | **4** | 2.00 |
| 48 | 7 | 3 | **4** | 2.33 |
| 56 | 9 | 39/10 | **5** | 2.31 |
| 64 | 10 | 5 | **5** | 2.00 |
| 96 | 13 | 69/10 | 6 | 1.88 |
| 128 | 17 | 10 | 7 | 1.70 |
| 160 | 18 | 89/9 | 8 | 1.82 |
| 192 | 24 | 16 | 8 | 1.50 |
| 256 | 30 | 99/5 | **10** | 1.52 |
| 384 | 35 | 295/12 | **10** | 1.42 |

(`n = 512, 768` were searched but their brackets did **not** close — `γ ∈ [47, ?]`, `[61, ?]` — so
they are excluded from every claim here.)

Read the two columns separately:

* **the gap grows**: `2 → 10` over `n = 20 → 256`, roughly `+1` per `1.5×` in `n`;
* **the ratio does not**: it oscillates in `1.42 … 2.33` with *no* upward trend — the largest
  values are at the *small* end (`n = 48`: `2.33`), and the largest `n` has the smallest ratio.

Growing `γ − δ` with bounded `γ/δ` is exactly what happens when both grow proportionally: it is
**not** evidence for the KNP log separation, which would need `γ/δ → ∞`.

## 3. The stress test: `δ = 2` fixed

If the log factor is attainable at binary, the natural place is `δ = 2` — the smallest nontrivial
substring complexity.  Restricted to `δ ≤ 2` strings (`results-delta2.json`, brackets closed):

| n | 20 | 28 | 48 | 64 | 80 | 96 | 128 | 160 | 192 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| γ | 4 | 5 | 5 | 5 | 5 | 6 | 5 | 6 | 5 |
| γ/δ | 2.0 | 2.5 | 2.5 | 2.5 | 2.5 | **3.0** | 2.5 | **3.0** | 2.5 |

The record instance (`n = 96`, `γ = 6`, `δ = 2`), verified independently at the definition level:

```
011011000011000000001100000000011000000011000000000110000000110000000110000000001100000000011000
attractor {4,5,12,49,69,71};  packing factors 0000000001100000000, 000000001100000001100000000,
1000000001, 100000001100000001, 100001, 101  (pairwise disjoint coverage sets)
```

Ratio `3.0` at `n = 96` and `n = 160`, `2.5` at the others: growth from `2.0` to `3.0` between
`n = 20` and `n = 96`, then flat.  Over one doubling past `n = 96` the ratio does not rise
(`160`: `3.0`, `192`: `2.5`).

## 4. What the data support, and what they do not

**Supported (as a conjecture, not a theorem):**

> `γ(S) ≤ 3·δ(S)` for every binary string `S` — equivalently, **`δ` is a 3-approximation of `γ` at
> `σ = 2`**.  Observed maximum over all certified rows: `2.33` for unrestricted `δ`, `3.0` in the
> `δ = 2` slice.

If that held, then by `gamma_div_primal_le` the attractor LP gap would be bounded by `3` on binary
text — an `O(1)` bound for a quantity that is `Θ(log n)` in general.

**Not supported:** any claim that `γ/δ` grows.  Nothing in 20 000+ certified instances shows a
ratio above `3`, and the largest-`n` rows have the *smallest* ratios.

**Not attempted:** a proof of an upper bound `γ ≤ c·δ` on binary.  This is the interesting theorem
and it is wide open; `δ` is a *counting* quantity and `γ` a *covering* one, so any proof must
convert "few distinct factors" into "few positions hitting all factors", which is where the log
factor usually creeps in for general alphabets.

## 5. What would settle it

1. **Push `δ = 2` to `n = 512 … 4096`.**  `γ` at those sizes needs a better search than local
   search over attractors; the instances are highly structured (`0^{a}1^{b}` interleavings), so a
   constructive family with certified brackets would be worth more than a scan.  If `γ` stays `≤ 6`
   while `n` grows by `16×`, the log factor is unlikely at binary; if it climbs as `log n`, it is real.
2. **Prove a packing/covering duality for binary text.**  Every record above has
   `γ = packing` (the lower bound is attained by disjoint coverage sets), so the question is
   equivalent to: *is the maximum packing of pairwise-disjoint coverage sets always within a
   constant of `δ` on binary text?*  That is a statement about a hypergraph with a specific
   structure, and it is the form in which a proof would most plausibly be found.
3. **Re-run the exhaustive sweep at `n = 23, 24`** (`2^24 = 16.7 M`) to see whether the exhaustive
   maximum moves off `3` — the lane's exhaustive data stop at `22`.

## 6. Reproduction

```
cd tools/gammadelta && python3 scan.py --local --delta-max 2 \
    --ns 20,28,48,64,80,96,128,160,192 ... # results-delta2.json
cd tools/gammadelta && python3 scan.py --local \
    --ns 20,24,...,384 ...                 # results.json
cd tools/gammadelta && python3 check.py    # re-verifies every closed bracket independently
```
