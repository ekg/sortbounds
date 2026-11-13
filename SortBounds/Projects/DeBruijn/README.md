# Lane: DeBruijn — a machine-checked separation `γ ≥ 2^k/k`

**Why.** `docs/research/gamma-vs-gamma2.md` proves: for a binary de Bruijn word `B_k` of order
`k`, `γ(B_k) ≥ 2^k/k` while `γ₂(B_k) ≤ 4`; hence `γ/γ₂` is unbounded and the "`γ₂` is within a
constant of `γ`" route to an algorithm is dead. The proof is: `d_i = 2^i` for `i ≤ k` ⇒
`δ = 2^k/k` ⇒ `γ ≥ δ`. All three steps are formalizable, and `δ ≤ γ` is already machine-checked
(`Repetitiveness.deltaQ_le_minAttractorSize`).

This lane makes the *inequality* a theorem. It deliberately does **not** construct de Bruijn
sequences (that is a separate, well-known combinatorial existence result — cite it as a
hypothesis and discharge it for small `k` by `decide`).

## Contract (exact target signatures)

```lean
namespace SortBounds.Projects.DeBruijn

open SortBounds

/-- Every binary word of length `k` occurs as a factor of `s`. -/
def CoversAllWords (s : List Bool) (k : ℕ) : Prop

/-- A de Bruijn word of order `k`: length `2^k + k - 1` and every `k`-gram occurs. -/
def IsDeBruijn (s : List Bool) (k : ℕ) : Prop

/-- **The counting core**: if every binary word of length `i ≤ k` occurs, then `s` has
exactly `2^i` distinct factors of length `i`. -/
theorem card_distinctFactors_of_coversAllWords {s : List Bool} {i : ℕ}
    (h : CoversAllWords s i) : (distinctFactors s i).card = 2 ^ i

/-- **`δ = 2^k/k`** for a de Bruijn word of order `k ≥ 2`. -/
theorem deltaQ_isDeBruijn {s : List Bool} {k : ℕ} (hk : 2 ≤ k) (h : IsDeBruijn s k) :
    deltaQ s = (2 ^ k : ℚ) / k

/-- **The separation**: `γ ≥ 2^k/k` for a binary de Bruijn word. -/
theorem gamma_ge_of_isDeBruijn {s : List Bool} {k : ℕ} (hk : 2 ≤ k) (h : IsDeBruijn s k) :
    (2 ^ k : ℚ) / k ≤ (minAttractorSize s : ℚ)

/-- Non-vacuity: `IsDeBruijn` is satisfiable for the smallest two orders. -/
theorem isDeBruijn_two : IsDeBruijn (['0','0','1','1','0'].map (· = '1')) 2
theorem isDeBruijn_three : IsDeBruijn (<de Bruijn word of order 3 over Bool>) 3

end SortBounds.Projects.DeBruijn
```

## Milestones

* **M0** `CoversAllWords`, `IsDeBruijn`, `card_distinctFactors_of_coversAllWords`
  (`distinctFactors s i` is the image of `Fin i → Bool` under `List.ofFn`; use
  `Finset.card_image_of_injective` and `Fintype.card_fun`; `List.ofFn_injective` is in
  Mathlib).
* **M1** `deltaQ_isDeBruijn`: `deltaQ` is the `sup'` over `1 ≤ i ≤ n` of `d_i/i`; with
  `d_i = 2^i` it is `max_i 2^i/i`, attained at `i = k` because `2^i/i` is nondecreasing for
  `i ≥ 1`. (Careful: `deltaQ` uses `ℚ` division and `Finset.sup'`; you may need the `Icc`
  membership and `sup'_le`/`le_sup'`.  If the `sup'` rewriting is painful, prove the two
  inequalities separately: `∀ i ∈ Icc 1 n, 2^i/i ≤ 2^k/k` and `2^k/k` is attained at `k`.)
* **M2** `gamma_ge_of_isDeBruijn` — one line from M1 and
  `Repetitiveness.deltaQ_le_minAttractorSize`.
* **M3** the two `decide` instances (order 2: `00110`; order 3: `0001011100`), each by
  `decide` over all `2^k` words of length `k`. This is what makes the theorem non-vacuous.

## Rules

Own only `SortBounds/Projects/DeBruijn/`.  `lake env lean`, no `lake build`, no git, oleans in
`/tmp`.  No `sorry`/`admit`/`axiom`/`native_decide`.  Do **not** claim existence of de Bruijn
words for all `k` in Lean — it is a hypothesis of the main theorems and the two instances are
witnesses.  If a statement is false as written (e.g. a length condition), state the true one and
report.

## Prior art

De Bruijn sequences: de Bruijn 1946; the greedy/FKM construction; van Aardenne-Ehrenfest &
de Bruijn 1951.  `γ ≥ δ` is KNP23 Lemma II.4 (machine-checked here).  The separation
`γ/γ₂ → ∞` is, as far as our surveys go, unstated in the literature.

## Log

* (empty)
