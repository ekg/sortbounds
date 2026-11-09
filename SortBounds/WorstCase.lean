/-
SortBounds/WorstCase.lean

The worst case is attained by an actual input: some injective input makes at
least `log₂(n!)` comparisons.  This is stronger than the depth bound of
`Tree.lean` (the depth of a decision tree may be inflated by branches no input
can follow); here the bound is on `max over inputs of cost`.
-/
import SortBounds.Aggregate

namespace SortBounds

open Finset

variable {n : ℕ}

/-- The worst-case number of comparisons, as a maximum over the canonical
inputs (one for each of the `n!` orderings). -/
def worstCase (t : Tree n) : ℕ :=
  Finset.univ.sup (fun p : Equiv.Perm (Fin n) => cost t (xOfPerm p))

theorem le_worstCase (t : Tree n) (p : Equiv.Perm (Fin n)) :
    cost t (xOfPerm p) ≤ worstCase t :=
  Finset.le_sup (f := fun p : Equiv.Perm (Fin n) => cost t (xOfPerm p)) (Finset.mem_univ p)

theorem worstCase_le_depth (t : Tree n) : worstCase t ≤ depth t := by
  apply Finset.sup_le
  intro p _
  exact cost_le_depth t (xOfPerm p)

/-- **Worst-case comparison lower bound.**  Some ordering of `n` distinct keys
makes a correct comparison sort do at least `2^c > n!`-forcing work: the
worst case is at least `log₂(n!)`. -/
theorem factorial_le_two_pow_worstCase {t : Tree n} (h : Correct (α := ℕ) t) :
    Nat.factorial n ≤ 2 ^ worstCase t := by
  have hsep : Separated t Finset.univ := separated_of_correct h
  have hcost : ∀ p ∈ Finset.univ, cost t (xOfPerm p) ≤ worstCase t :=
    fun p _ => le_worstCase t p
  have hcard := card_le_pow_of_cost_le t Finset.univ (worstCase t) hsep hcost
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rwa [huniv] at hcard

theorem logb_factorial_le_worstCase {t : Tree n} (h : Correct (α := ℕ) t) :
    Real.logb 2 (Nat.factorial n) ≤ (worstCase t : ℝ) := by
  have hnat := factorial_le_two_pow_worstCase h
  have hcast : (Nat.factorial n : ℝ) ≤ (2 : ℝ) ^ (worstCase t) := by
    exact_mod_cast hnat
  have hpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) hpos]
  simpa using hcast

/-- The bound is attained by a single, explicitly existing input. -/
theorem exists_input_cost_ge {t : Tree n} (h : Correct (α := ℕ) t) :
    ∃ x : Fin n → ℕ, Function.Injective x ∧
      Real.logb 2 (Nat.factorial n) ≤ (cost t x : ℝ) := by
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (f := fun p : Equiv.Perm (Fin n) => cost t (xOfPerm p)) Finset.univ_nonempty
  refine ⟨xOfPerm p, xOfPerm_injective p, ?_⟩
  rw [← hp]
  exact logb_factorial_le_worstCase h

end SortBounds
