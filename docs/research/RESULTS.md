# Results

What this repository proves, what it measured, and what is still open.  Every theorem below is
Lean 4, kernel-checked, and in the `make trust` audit (147 theorems, all on
`propext`/`Classical.choice`/`Quot.sound`; no `sorry`, `axiom` or `native_decide`).  Every number
is reproducible from `tools/`.

Notation: `γ` = minimum string attractor size (Kempa–Prezza), `γ_k` = minimum `k`-attractor
size (all factors of length `≤ k`), `δ = max_k d_k/k` (Kociumaka–Navarro–Prezza substring
complexity), `LP*` = optimum of the attractor set-cover LP, `d_k` = number of distinct length-`k`
factors.

## Part 1 — Sorting lower bounds (the original programme)

| result | statement |
| --- | --- |
| worst case | `Ω(n log n)` comparisons for any correct comparison tree |
| average case | exact `≥ log₂ n!` for the average depth |
| randomised | `≥ log₂ n!` expected depth for any distribution-free correct algorithm |
| value types | the bound holds for any linearly ordered value type (`orderEmb`) |
| exact `S(n)` | `S n = ⌈log₂ n!⌉` for `4 ≤ n ≤ 11`, and for `n = 20, 21`; within 1 for `n ≤ 22` |
| best case | `n − 1` on every injective input, and attained |
| one model, Θ | `⌈log₂ n!⌉ ≤ S n ≤ n(⌈log₂ n⌉+1)` |
| networks | comparator bound, **0–1 principle**, network→tree embedding |
| SAIS | linear-time verification, Kasai `≤ 2n`, the LCP cost model (with its counterexample) |
| domain | word-RAM probes: `log_b U` necessary **and** sufficient |

Details: `docs/PROGRESS.md`, `docs/MODELS.md`, `SortBounds/`.

## Part 2 — Compressed indexing: the six theorems about attractors

### T1 `δ ≤ γ` against the minimum

`Repetitiveness.deltaQ_le_minAttractorSize : deltaQ s ≤ (minAttractorSize s : ℚ)`

The published `δ ≤ γ` (KNP23 Lemma II.4) was in the repo only against a *given* attractor's size;
every claim about `γ` itself needs the version against the minimum, which follows because some
attractor attains `minAttractorSize`.  Unfloored (rational), so no ceiling artefacts.

### T2 the `k`-attractor hierarchy is unbounded

`DeBruijn.gamma_ge_of_isDeBruijn`, `DeBruijn.deltaQ_isDeBruijn`,
`AttractorK.gamma_ratio_ge_isDeBruijn`, `AttractorK.dk_div_le_minAttractorKSize`,
`AttractorK.minAttractorKSize_bracket_isDeBruijn`

For a binary de Bruijn word `B_m` of order `m` and any `1 ≤ k ≤ m`:

```
2^k/k  ≤  γ_k(B_m)  ≤  2^k            (so γ_k = Θ(2^k/k))
γ(B_m)  ≥  2^m/m
γ(B_m)/γ_k(B_m)  ≥  2^m/(m·2^k)  →  ∞    for every FIXED k
```

`IsAttractorK` is the standard object (factors of length `≤ k`; `isAttractorK_self_iff` shows it is
`IsAttractor` at `k = n`).  The upper bound needs an "extends right" side condition — without it
the claim is false (`"ab"` at `k = 2`: `d₂ = 1` but `γ₂ = 2`), which the formalization records.

**Consequence.** No bounded-length attractor approximates `γ` within any factor, at any fixed `k`.
The `k`-attractor family — the only obviously polynomial-time object at `σ = 2` — is exponentially
far below `γ`, which is why the hardness question can only live at `k = n`.  (As far as our
surveys go this ratio statement is not in the literature.)

### T3 the attractor LP is not integral

`AttractorLP.weak_duality`, `lp13_gamma`, `lp13_primal`, `lp13_dual`, `lp13_gap`

On `s = 0110101101110` (`n = 13`): `γ = 3`, `LP* = 11/5`, gap `γ/LP* = 15/11`.
`LP* = 11/5` is pinned two-sided without any simplex: an exhibited pair `(x, y)` with equal value,
plus weak duality (`Σy ≤ Σx`, elementary — swap the two sums and use the two load constraints).

**Consequence.** An `O(1)`-ratio algorithm for `γ` cannot rest on the LP being near-integral: the
relaxation genuinely falls below the integer optimum, so rounding is the remaining problem.

### T4 `γ ≤ ⌈δ⌉ + 2` is false, and the packing certificate is formal

`Packing.card_le_minAttractorSize_of_pairwiseDisjoint`, `s32_gamma`, `s32_delta`,
`gamma_delta_add_two_false`

For `s32 = bbbaaaabbabbaaabbaaaabbaabbaabaa` (`n = 32`): `γ = 6`, `δ = 3`.  Six factors with
pairwise disjoint coverage sets give `γ ≥ 6`; a 6-position attractor gives `γ ≤ 6`.

The packing lemma is general: if the coverage sets of a factor set `F` are pairwise disjoint then
`|F| ≤ γ`.  That is the certificate every closed bracket in `tools/attractor` rests on — it is now
a theorem rather than a Python routine.

### T5 `LP* ≥ δ`, hence `γ/LP* ≤ γ/δ`

`AttractorLP.deltaQ_le_primalValue`, `gamma_div_primal_le`, `card_filter_coverageSet_le`,
`sum_distinctFactors_coverage`, `factor_card_le_primal_sum`

Every **fractional** cover has value at least `δ` (weighted counting: `d_j ≤ j·Σx`).  So the LP
optimum is floor-bounded by KNP's bound, and the LP gap is capped by the `δ`-gap.

**Consequence.** The LP gap is not an independent quantity: it is capped by the `δ`-gap.  It does
**not** follow that the LP gap is bounded — that would need a bound on `γ/δ` over binary text, which
is open.  (An earlier version of this note claimed the measured `γ − ⌈δ⌉ ≤ 3` "forces the LP gap to
`1` at scale"; that is withdrawn, since those measurements are exhaustive only to `n = 18` and a
binary family with `γ/δ → ∞` would carry the LP gap with it.)

### T6 the certified bracket brackets `LP*` too

`Packing.card_le_primalValue_of_pairwiseDisjoint`, `Packing.exists_primalValue_le_minAttractorSize`

```
max(δ, |F|)  ≤  LP*  ≤  γ
```

so the interval `tools/attractor` reports is a valid bracket for the LP optimum as well, not merely
an integer bound.  (`LP* ≤ γ` is an *existence* statement — some feasible `x` attains at most `γ`;
the universal form is false, the all-ones vector refutes it.)

## Part 3 — Measurements (not theorems)

| measurement | value | scope |
| --- | --- | --- |
| LP gap, exhaustive | `1` (n≤6), `6/5` (7), `9/7` (8–11), `4/3` (12), `15/11` (13), `4/3` (14–16), 89–92 % integral | **all** binary strings, `n ≤ 16` |
| LP gap, searched | `7/5 = 1.4` at `n = 31`; `25/18` (n=30); `18/13` (n=21, 27) | beam/structured search to `n = 40`, **not** exhaustive |
| `γ − ⌈δ⌉` | max `2` for all binary `n ≤ 18`; `3` exhaustive at `n = 20, 21, 22`; `4` at `n = 40, 48`; `10` at `n = 256` | exhaustive to 22, searched (closed brackets) above |
| `γ/δ` (binary) | **`≤ 2.33` over `n = 20 … 384`**, no upward trend; `3.0` in the `δ = 2` slice | searched, all brackets closed, 49/49 re-verified |
| `γ − γ₂` | `3` at `n = 17` | exhaustive to 17 |
| `γ` vs `d`-profile | not a function of it (41 of 123 classes split) | exhaustive, binary `n ≤ 12` |
| Σ=2 gadget attempts | 3 explicit polynomial reductions, all **refuted** | exhaustive equivalence checks |

The LP-gap figures are exact rationals with primal/dual certificates; the toolling re-verifies each
independently (`tools/gap/check.py`: 142 347 checks; `tools/attractor/check.py`: 283 545;
`tools/approx/check.py`: 651 627; all green).

## Part 4 — Open problems, with the sharpest available form

1. **Is `γ` NP-hard at `σ = 2`, `k = n`?**  Open in the literature (KP18 harden for growing
   alphabets; SLP is NP-complete only for fixed alphabets `≥ 17`, and open at `σ = 2` — see
   `hardness-related-binary.md`, including one **UNVERIFIED** 2026 preprint claiming binary SLP
   hardness).  Surviving necessary condition for any reduction: `γ(T_G)` must depend only on the
   isomorphism class of `G` (`sigma2-gadget.md`).
2. **Is `γ/δ` bounded on binary text?**  The evidence now points *yes*: `γ/δ ≤ 2.33` across
   `n = 20 … 384` with no upward trend (`gamma-delta-growth.md`), while the *gap* grows only because
   `δ` does.  The conjecture this supports is `γ ≤ 3δ` at `σ = 2` — which, with T5
   (`γ/LP* ≤ γ/δ`), would bound the LP gap by `3`.  A proof is wide open: it would have to turn
   "few distinct factors" into "few hitting positions" without paying a log factor.
3. **Round the attractor LP with ratio `O(1)`.**  T3 says the LP is not integral, T5 says its gap
   is capped by the `δ`-gap, T6 says the bracket is valid for `LP*`.  What is missing is a
   rounding rule, and no integrality argument can supply it.

## What this programme did *not* establish

* Nothing about the r-index beyond `docs/research/SYNTHESIS.md`'s survey (the user's judgement:
  r-index is trivial; the work moved to `γ`).
* No boundedness result for the LP gap, in either direction.
* No hardness result at `σ = 2`, and no algorithm for `k = n` at `σ = 2` better than exhaustive.
* `γ = ⌈δ⌉` is not a theorem in general; it holds for specific families (Thue–Morse `n ≥ 6`,
  unary/Sturmian/Fibonacci trivially) and fails for others (`gamma-equals-delta.md`).
