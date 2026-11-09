/-
SortBounds/LowerBound.lean

The headline results: any correct comparison-based sorting algorithm needs
`log₂(n!)` comparisons in the worst case (on a real input), and hence
`Ω(n log n)` comparisons.  Both a "tree-depth" form and a "there exists an
input" form are given, plus the elementary `n/4 · log₂ n` corollary obtained
from `n! ≥ (n/2)^(n/2)`.
-/
import SortBounds.WorstCase
import SortBounds.Stirling

namespace SortBounds

open Finset

variable {n : ℕ}

/-- **Worst-case depth bound.**  The decision tree of a correct comparison sort
on `n` distinct keys has depth at least `log₂(n!)`. -/
theorem depth_ge_log2_factorial {t : Tree n} (h : Correct (α := ℕ) t) :
    Real.logb 2 (Nat.factorial n) ≤ (depth t : ℝ) :=
  le_trans (logb_factorial_le_worstCase h) (by
    have := worstCase_le_depth t
    exact_mod_cast this)

/-- **The `Ω(n log n)` lower bound, on actual inputs.**  For `n ≥ 64` there is
an input with pairwise distinct keys on which any correct comparison sort makes
at least `n/4 · log₂ n` comparisons. -/
theorem exists_input_cost_ge_quarter (hn : 64 ≤ n) {t : Tree n}
    (h : Correct (α := ℕ) t) :
    ∃ x : Fin n → ℕ, Function.Injective x ∧
      (n : ℝ) * Real.logb 2 n / 4 ≤ (cost t x : ℝ) := by
  obtain ⟨x, hx, hcost⟩ := exists_input_cost_ge h
  exact ⟨x, hx, le_trans (logb_factorial_ge_quarter n hn) hcost⟩

/-- **The `Ω(n log n)` lower bound, tree form.** -/
theorem depth_ge_quarter (hn : 64 ≤ n) {t : Tree n} (h : Correct (α := ℕ) t) :
    (n : ℝ) * Real.logb 2 n / 4 ≤ (depth t : ℝ) :=
  le_trans (logb_factorial_ge_quarter n hn) (depth_ge_log2_factorial h)

/-- **The `Ω(n log n)` lower bound, worst-case form.** -/
theorem worstCase_ge_quarter (hn : 64 ≤ n) {t : Tree n} (h : Correct (α := ℕ) t) :
    (n : ℝ) * Real.logb 2 n / 4 ≤ (worstCase t : ℝ) :=
  le_trans (logb_factorial_ge_quarter n hn) (logb_factorial_le_worstCase h)

/-- Reformulation: no correct comparison sort beats `n/4 · log₂ n` comparisons
on every input. -/
theorem not_forall_cost_lt_quarter (hn : 64 ≤ n) {t : Tree n}
    (h : Correct (α := ℕ) t) :
    ¬ ∀ x : Fin n → ℕ, Function.Injective x →
        (cost t x : ℝ) < (n : ℝ) * Real.logb 2 n / 4 := by
  intro hall
  obtain ⟨x, hx, hge⟩ := exists_input_cost_ge_quarter hn h
  have := hall x hx
  linarith

end SortBounds
