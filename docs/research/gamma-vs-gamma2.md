# The `k`-attractor hierarchy has unbounded ratios: `γ / γ₂` is not bounded

**A theorem, not a measurement.** It is short, elementary, and — as far as the surveys in
`space.md` and `attractor-approx.md` go — nobody states it: the literature studies `δ`, `γ`,
`z`, `g`, `r`, but not the relation between the *bounded-length* attractors `γ_k`.

## The statement

For `k ≥ 1` let `γ_k(S)` be the minimum size of a subset `Γ ⊆ {0..n−1}` such that every
distinct factor of `S` of length **at most** `k` has an occurrence crossing a position of `Γ`
(so `γ_n = γ`, and `γ_1 = σ` when `n ≥ 1`).

> **Theorem.** There are binary strings `B_k` (`k = 2, 3, …`) with
> `γ(B_k) ≥ 2^k / k` and `γ₂(B_k) ≤ 4`.
> Hence `γ(B_k) / γ₂(B_k) ≥ 2^k/(4k) → ∞`: **no constant `c` satisfies `γ ≤ c·γ₂`**, and
> `γ₂` is not a constant-factor approximation of `γ` on binary text.
> (Computed exactly: `γ₂(B_k) = 2` for every `k ≤ 7`, so the true ratio is `≥ 2^{k-1}/k`.)

## Proof

Let `B_k` be a **de Bruijn word** of order `k` over `{0,1}`: a string of length `2^k + k − 1`
in which every binary `k`-gram occurs exactly once.

1. **Every shorter `i`-gram occurs, `i ≤ k`.** Each binary `i`-gram `u` with `i ≤ k` is a
   prefix of some binary `k`-gram (pad `u` on the right); that `k`-gram occurs in `B_k`, so `u`
   does. Since there are exactly `2^i` binary `i`-grams and they are all distinct,
   `d_i(B_k) = 2^i` for every `1 ≤ i ≤ k`.
2. **Therefore `δ(B_k) = 2^k/k`.** By definition `δ = max_{1≤i≤n} d_i/i`; here `d_i/i = 2^i/i`,
   and `2^i/i` is nondecreasing for `i ≥ 1` (for `i ≥ 1`, `2^{i+1}/(i+1) ≥ 2^i/i ⟺ 2i ≥ i+1
   ⟺ i ≥ 1`), so the maximum is attained at `i = k`.
3. **`δ ≤ γ`** (Kociumaka–Navarro–Prezza, Lemma II.4; machine-checked in this repository as
   `Attractor.substringComplexity_le_card_attractor` and, unfloored,
   `Attractor.deltaQ_le_card_attractor`). Hence `γ(B_k) ≥ 2^k/k`.
4. **`γ₂(B_k) ≤ 4`.** There are at most `2² = 4` distinct binary 2-grams. Choose, for each
   distinct 2-gram `u` that occurs in `B_k`, one position inside one occurrence of `u`; that is
   at most 4 positions, and every factor of length ≤ 2 has an occurrence crossing one of them
   (a 1-gram occurs inside some occurring 2-gram). So `γ₂ ≤ d₂ ≤ 4`.
5. Dividing, `γ/γ₂ ≥ 2^k/(4k) → ∞`. ∎

Nothing here needs the exact value of `γ`; only `δ ≤ γ` (a published theorem, formalized here)
and two trivial counting facts. That is why the statement is provable while `γ` itself is not.

## Checked values

`δ` computed exactly from the suffix array, `γ₂` computed exactly by the definition-level
solver (`tools/sigma2-alg/features.py::gamma_k`); `d₂` is the count of distinct 2-grams.

| k | n = 2^k+k−1 | δ = 2^k/k | γ₂ | γ/γ₂ ≥ |
| --- | --- | --- | --- | --- |
| 2 | 5 | 2 | 2 | 1 |
| 3 | 10 | 8/3 | 2 | 4/3 |
| 4 | 19 | 4 | 2 | 2 |
| 5 | 36 | 32/5 | 2 | 16/5 |
| 6 | 69 | 32/3 | 2 | 16/3 |
| 7 | 134 | 128/7 | 2 | 64/7 ≈ 9.1 |
| 8 | 263 | 32 | — | ≥ 8 |
| 10 | 1033 | 512/5 | — | ≥ 25.6 |
| 13 | 8204 | 8192/13 | — | ≥ 157.5 |

(`γ₂ = 2` is exact for `k ≤ 7`; beyond that the solver is not needed, since `γ₂ ≤ 4` is the
trivial bound. The `γ/γ₂ ≥` column uses `δ/4`.)

## Why this is the "novel result" that was missing

The earlier lanes produced *measurements* (`γ` for `n ≤ 32`, the LP gap `15/11`): facts about
finite instances of an NP-hard quantity, which is not a theorem. This one has a two-line proof
whose ingredients are a published inequality and counting. It also **closes a research
direction**: "compute `γ₂` (polynomial at `σ = 2`) and you are within a constant of `γ`" was
the most promising structural route in `sigma2-algorithm.md`; the theorem refutes it outright,
and it explains *why* the `k*`-growth (`k*(s) ≈ n/2`) that lane measured is not an artefact.

## What would be the next theorem of this shape

* `γ / γ_k` unbounded for every fixed `k`: same proof, since `γ_k(B_k) ≤ d_k = 2^k`… this only
  gives `γ_k ≤ 2^k`, which grows. A sharper construction (a family where `γ_k` stays
  polynomial while `γ ≥ 2^k/k`) would give `γ/γ_k → ∞` for **every** fixed `k`. Candidate: the
  family in `space.md`'s separation (`S_n = b a^{2^j-1} b` at powers of two), where `δ ≤ 2`
  but `γ ≥ ½⌊log n⌋` — a *logarithmic* gap only.
* `γ / δ ≥ log n` on a **binary** family: the KNP separation is stated for `γ` vs `δ` on
  general strings; instantiating it on binary would answer whether `δ` is a `Θ(log n)`
  approximation there (the LP data suggests the *LP* is not, but `δ` and `LP*` are different).
