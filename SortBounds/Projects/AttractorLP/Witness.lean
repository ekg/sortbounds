/-
SortBounds/Projects/AttractorLP/Witness.lean

**The finite certificate for the integrality gap `15/11` at `n = 13`.**

The instance is `s = 0110101101110` — the text that attains the *measured* maximum
`15/11` over all binary texts with `n ≤ 16` (`docs/research/lp-gap.md` §3.1; that maximality is
a computation, not a theorem of this file).  Three facts pin the gap down without any LP
solver:

* `γ = 3` — `{3, 8, 9}` is an attractor (`lp13_attractor`), and **no two positions** are, so
  `minAttractorSize lp13 = 3` (`lp13_gamma`);
* a primal feasible `x` with `Σ x = 11/5` (`lp13_primal`);
* a dual feasible `y` with `Σ y = 11/5` (`lp13_dual`).

Weak duality (`weak_duality`) then gives `LP* = 11/5` on this instance (`lp13_lpValue`), and
`γ/LP* = 3/(11/5) = 15/11` (`lp13_gap`).

**How the arithmetic is checked.**  `decide` cannot evaluate `ℚ`: `Rat.add`/`Rat.decEq` do not
reduce in the kernel, so no rational identity is decidable.  Every numeric fact here is
therefore decided **over `ℕ`**, at `5 · x` and `5 · y` (`lp13X`, `lp13Y`, both natural-valued,
so `decide` works), and transported to `ℚ` by the general lemmas `sum_lp13x`, `sum_lp13y`.
That is the fallback the lane contract anticipated ("verify each position's dual load as a
separate lemma and combine"), taken for the whole computation, and it keeps the file free of
61 hand-written rows.

**How `γ ≥ 3` is proved.**  A packing of 3 pairwise disjoint coverage sets does **not** exist
for this text — no three of the 61 factors have pairwise disjoint coverage sets (enumerated
over all triples; the largest packing has size `2`, namely `C("0")` and `C("11")`), so the
contract's first M3 fallback is unavailable.  Instead `lp13Hard` is a certificate of 6 factors
that no two positions jointly cover (`lp13_no_two_positions`, a finite check over the
`13 × 13` pairs of positions); an attractor of size `≤ 2` would have to cover all six of them,
which is impossible.  That proves `γ ≥ 3` without enumerating any of the `2^13` position sets.
-/
import Mathlib
import SortBounds.Projects.AttractorLP.Gap

-- The `decide`-checked row conditions evaluate `coverageSet` for every factor of the text,
-- which is deep enough to need a larger recursion budget than the default.
set_option maxRecDepth 100000

namespace SortBounds.Projects.AttractorLP

open SortBounds.Projects.Repetitiveness

/-! ### The instance -/

/-- The witness text `0110101101110` (`n = 13`). -/
def lp13 : List Bool :=
  [false, true, true, false, true, false, true, true, false, true, true, true, false]

/-- The integral attractor `{3, 8, 9}` of `lp13`. -/
def lp13Attractor : Finset (Fin lp13.length) :=
  {⟨3, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩}

theorem lp13Attractor_card : lp13Attractor.card = 3 := by decide

/-- **An attractor of size `3`**: positions `3, 8, 9` cover every factor of `lp13`.  (A finite
check: `isAttractor_iff_check` turns the definition into a search over `Fin (n+1)` twice.) -/
theorem lp13_attractor : IsAttractor lp13 lp13Attractor := by
  rw [isAttractor_iff_check]
  decide

/-! ### The primal witness: `x` -/

/-- `5 · x`, so that the primal weights are natural numbers (`x p = lp13X p / 5`).

`x: 3 ↦ 1/5, 4 ↦ 1/5, 5 ↦ 3/5, 8 ↦ 1/5, 9 ↦ 2/5, 10 ↦ 3/5, x p = 0` otherwise. -/
def lp13X (p : Fin lp13.length) : ℕ :=
  match (p : ℕ) with
  | 3 => 1
  | 4 => 1
  | 5 => 3
  | 8 => 1
  | 9 => 2
  | 10 => 3
  | _ => 0

/-- The primal witness `x` of `lp-gap.md`. -/
def lp13x (p : Fin lp13.length) : ℚ := (lp13X p : ℚ) / 5

/-- The primal witness, on its support. -/
theorem lp13x_values :
    lp13x ⟨3, by decide⟩ = 1 / 5 ∧ lp13x ⟨4, by decide⟩ = 1 / 5 ∧
      lp13x ⟨5, by decide⟩ = 3 / 5 ∧ lp13x ⟨8, by decide⟩ = 1 / 5 ∧
      lp13x ⟨9, by decide⟩ = 2 / 5 ∧ lp13x ⟨10, by decide⟩ = 3 / 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [lp13x, lp13X]

/-- Scaling a rational sum back by `5`: the bridge from the decidable `ℕ`-valued check to the
`ℚ`-valued feasible region. -/
theorem sum_lp13x (s : Finset (Fin lp13.length)) :
    ∑ p ∈ s, lp13x p = ((∑ p ∈ s, lp13X p : ℕ) : ℚ) / 5 := by
  simp [lp13x, Finset.sum_div]

/-! ### The dual witness: `y` -/

/-- `5 · y`, so that the dual weights are natural numbers (`y f = lp13Y f / 5`).

`y: "0" ↦ 1/5, "11" ↦ 1/5, "110" ↦ 1/5, "1101" ↦ 1/5, "011010" ↦ 2/5, "10110" ↦ 2/5,
"111" ↦ 3/5, y f = 0` otherwise. -/
def lp13Y : List Bool → ℕ
  | [false] => 1
  | [true, true] => 1
  | [true, true, false] => 1
  | [true, true, false, true] => 1
  | [false, true, true, false, true, false] => 2
  | [true, false, true, true, false] => 2
  | [true, true, true] => 3
  | _ => 0

/-- The dual witness `y` of `lp-gap.md`. -/
def lp13y (f : List Bool) : ℚ := (lp13Y f : ℚ) / 5

/-- The dual witness, on its support. -/
theorem lp13y_values :
    lp13y [false] = 1 / 5 ∧ lp13y [true, true] = 1 / 5 ∧ lp13y [true, true, false] = 1 / 5 ∧
      lp13y [true, true, false, true] = 1 / 5 ∧
      lp13y [false, true, true, false, true, false] = 2 / 5 ∧
      lp13y [true, false, true, true, false] = 2 / 5 ∧ lp13y [true, true, true] = 3 / 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [lp13y, lp13Y]

/-- Scaling a rational sum back by `5` (dual side). -/
theorem sum_lp13y (s : Finset (List Bool)) :
    ∑ f ∈ s, lp13y f = ((∑ f ∈ s, lp13Y f : ℕ) : ℚ) / 5 := by
  simp [lp13y, Finset.sum_div]

/-! ### M4: both witnesses are feasible, with value `11/5` -/

/-- Every factor of `lp13` is covered with weight at least `1` by `x` — checked at `5 · x`, so
decidably: `5 ≤ Σ_{p ∈ C(f)} 5·x_p` for all 61 factors of the text. -/
theorem lp13_primalRows :
    ∀ f ∈ factorUniverse lp13, 5 ≤ ∑ p ∈ coverageSet lp13 f, lp13X p := by
  decide

/-- Every position carries dual load at most `1` — checked at `5 · y`. -/
theorem lp13_dualRows :
    ∀ p : Fin lp13.length,
      ∑ f ∈ (factorUniverse lp13).filter (fun f => p ∈ coverageSet lp13 f), lp13Y f ≤ 5 := by
  decide

theorem lp13_primal_total : ∑ p : Fin lp13.length, lp13X p = 11 := by decide

theorem lp13_dual_total : ∑ f ∈ factorUniverse lp13, lp13Y f = 11 := by decide

/-- **`x` is primal feasible, with `Σ x = 11/5`.** -/
theorem lp13_primal : ∃ x : Fin lp13.length → ℚ, PrimalFeasible lp13 x ∧ ∑ p, x p = 11 / 5 := by
  refine ⟨lp13x, ⟨fun p => ?_, fun f hf => ?_⟩, ?_⟩
  · unfold lp13x
    positivity
  · have hnat := lp13_primalRows f hf
    have hcast : (5 : ℚ) ≤ ((∑ p ∈ coverageSet lp13 f, lp13X p : ℕ) : ℚ) := by
      exact_mod_cast hnat
    rw [sum_lp13x]
    linarith
  · rw [sum_lp13x, lp13_primal_total]
    norm_num

/-- **`y` is dual feasible, with `Σ y = 11/5`.** -/
theorem lp13_dual :
    ∃ y : List Bool → ℚ, DualFeasible lp13 y ∧ ∑ f ∈ factorUniverse lp13, y f = 11 / 5 := by
  refine ⟨lp13y, ⟨fun f _ => ?_, fun p => ?_⟩, ?_⟩
  · unfold lp13y
    positivity
  · have hnat := lp13_dualRows p
    have hcast : ((∑ f ∈ (factorUniverse lp13).filter
        (fun f => p ∈ coverageSet lp13 f), lp13Y f : ℕ) : ℚ) ≤ 5 := by
      exact_mod_cast hnat
    rw [sum_lp13y]
    rw [div_le_one (by norm_num : (0 : ℚ) < 5)]
    exact hcast
  · rw [sum_lp13y, lp13_dual_total]
    norm_num

/-! ### M3: `γ = 3` -/

/-- **The lower-bound certificate for `γ ≥ 3`**: six factors no two positions can jointly
cover.  Each row is the factor, read as a binary word: `0`, `110`, `111`, `1101`, `01011`,
`10110`.  (`lp13Hard ⊆ factorUniverse lp13`, so each of them is a row of the LP.) -/
def lp13Hard : Finset (List Bool) :=
  {[false], [true, true, false], [true, true, true], [true, true, false, true],
    [false, true, false, true, true], [true, false, true, true, false]}

theorem lp13Hard_subset : lp13Hard ⊆ factorUniverse lp13 := by decide

/-- **No two positions cover all six hard factors** — the finite check behind `γ ≥ 3`
(`13 × 13 = 169` pairs of positions, `6` coverage sets each).  Since in fact no three of the 61
factors of `lp13` have pairwise disjoint coverage sets (enumerated over the triples in Python;
not a Lean statement), this is strictly stronger than a packing — that is the fallback the lane
contract offered and it is unavailable here. -/
theorem lp13_no_two_positions :
    ∀ p q : Fin lp13.length,
      ¬ (∀ t ∈ lp13Hard, p ∈ coverageSet lp13 t ∨ q ∈ coverageSet lp13 t) := by
  decide

/-- **Every attractor of `lp13` has at least three positions.**  An attractor covers each of the
six hard factors (`isAttractor_iff_coverageSet`), and by `lp13_no_two_positions` no two
positions can do that — so a `≤ 2`-element attractor does not exist. -/
theorem three_le_card_of_isAttractor {Γ : Finset (Fin lp13.length)}
    (hΓ : IsAttractor lp13 Γ) : 3 ≤ Γ.card := by
  have hcover : ∀ t ∈ lp13Hard, ∃ p ∈ Γ, p ∈ coverageSet lp13 t := by
    intro t ht
    obtain ⟨p, hp⟩ := (isAttractor_iff_coverageSet Γ).mp hΓ t (lp13Hard_subset ht)
    exact ⟨p, (Finset.mem_inter.mp hp).2, (Finset.mem_inter.mp hp).1⟩
  by_contra hcon
  -- two positions would have to cover all six hard factors
  obtain ⟨p, q, hpq⟩ : ∃ p q : Fin lp13.length, Γ ⊆ {p, q} := by
    have hle : Γ.card ≤ 2 := by omega
    interval_cases h : Γ.card
    · refine ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ?_⟩
      rw [Finset.card_eq_zero.mp h]
      simp
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
      exact ⟨a, a, by simp⟩
    · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h
      exact ⟨a, b, subset_rfl⟩
  refine lp13_no_two_positions p q fun t ht => ?_
  obtain ⟨r, hrΓ, hrt⟩ := hcover t ht
  rcases Finset.mem_insert.mp (hpq hrΓ) with rfl | hr
  · exact Or.inl hrt
  · rw [Finset.mem_singleton] at hr
    exact Or.inr (hr ▸ hrt)

/-- **`γ = 3`** for the witness text: `{3, 8, 9}` is an attractor and no smaller set is. -/
theorem lp13_gamma : minAttractorSize lp13 = 3 := by
  refine le_antisymm ?_ ?_
  · calc minAttractorSize lp13 ≤ lp13Attractor.card := minAttractorSize_le lp13_attractor
      _ = 3 := lp13Attractor_card
  · obtain ⟨Γ, hΓ, hcard⟩ := exists_attractor_card_eq_minAttractorSize lp13
    rw [← hcard]
    exact three_le_card_of_isAttractor hΓ

/-! ### M5: the gap -/

/-- **The LP optimum of the instance is `11/5`**, two-sided: `x` attains `11/5`
(`lp13_primal`), and weak duality against the fixed dual witness `y` rules out anything smaller
(`lp13_dual`).  No simplex, no LP theory — an exhibited pair of equal value. -/
theorem lp13_lpValue {x : Fin lp13.length → ℚ} (hx : PrimalFeasible lp13 x) :
    11 / 5 ≤ ∑ p, x p := by
  obtain ⟨y, hy, hyval⟩ := lp13_dual
  have hwd := weak_duality hx hy
  rw [hyval] at hwd
  exact hwd

/-- **The integrality gap of `15/11`, as a theorem**: the minimum attractor of `lp13` has
`3` positions, the LP relaxation is `11/5 < 3`, and `3/(11/5) = 15/11`.  This is a *lower bound*
`15/11` on the ratio for the whole class plus the exact ratio on this instance; it is not a
supremum over all strings (the maximum over `n ≤ 16` is a computation, `lp-gap.md`). -/
theorem lp13_gap :
    minAttractorSize lp13 = 3 ∧ (11 / 5 : ℚ) < 3 ∧ (3 : ℚ) / (11 / 5) = 15 / 11 :=
  ⟨lp13_gamma, by norm_num, by norm_num⟩

end SortBounds.Projects.AttractorLP
