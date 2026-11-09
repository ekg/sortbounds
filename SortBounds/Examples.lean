/-
SortBounds/Examples.lean

Sanity checks that the model is not vacuous.

* `n = 2`: one comparison sorts two elements, and `log₂ 2! = 1` says one is
  necessary — the bound is attained.
* `n = 3`: `6 > 2^2`, so no comparison tree of depth 2 sorts three elements
  (`⌈log₂ 3!⌉ = 3`).
-/
import SortBounds.WorstCase

namespace SortBounds

/-- One comparison sorts two elements: compare `x 0` with `x 1`. -/
def tree2 : Tree 2 :=
  Tree.node 0 1 (Tree.leaf 1) (Tree.leaf (Equiv.swap 0 1))

theorem tree2_run (x : Fin 2 → ℕ) :
    run tree2 x = if x 0 < x 1 then 1 else Equiv.swap 0 1 := rfl

theorem tree2_correct : Correct (α := ℕ) tree2 := by
  intro x hx
  rw [tree2_run]
  intro a b hab
  have h01 : x 0 ≠ x 1 := by
    intro h; exact absurd (hx h) (by decide)
  by_cases h : x 0 < x 1
  · rw [ite_eq_left h]
    have ha : a = 0 := by omega
    have hb : b = 1 := by omega
    simpa [ha, hb] using h
  · rw [ite_eq_right h]
    have hgt : x 1 < x 0 := by omega
    have ha : a = 0 := by omega
    have hb : b = 1 := by omega
    subst ha; subst hb
    simpa using hgt

theorem tree2_depth : depth tree2 = 1 := by decide

/-- The `log₂(n!)` bound is attained for two elements. -/
theorem tree2_sharp : depth tree2 = 1 ∧ Real.logb 2 (Nat.factorial 2) = 1 := by
  refine ⟨tree2_depth, ?_⟩
  norm_num

/-- Two comparisons cannot sort three elements, so `⌈log₂ 3!⌉ = 3` is the true
worst case.  This is the counting bound `n! ≤ 2^depth` at `n = 3`. -/
theorem three_needs_three_comparisons :
    ¬ ∃ t : Tree 3, Correct (α := ℕ) t ∧ depth t ≤ 2 := by
  rintro ⟨t, ht, hd⟩
  have h := factorial_le_two_pow_depth ht
  have h2 : 2 ^ depth t ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hd
  have h3 : 2 ^ 2 = 4 := by norm_num
  rw [h3] at h2
  norm_num at h
  omega

end SortBounds
