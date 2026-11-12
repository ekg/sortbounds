/-
SortBounds/Projects/BestCase/General.lean

`pred_le_cost` is stated for `ℕ`-valued inputs.  As everywhere else in this
repository, the value type is a convenience, not a restriction: `run` and `cost`
depend only on the *comparison pattern* (`Comparison.Tree.cost_eq_of_pattern`), so the
best-case bound transfers to any linear order containing `n` values in increasing order.
-/
import SortBounds.Projects.BestCase.Main
import SortBounds.Comparison.General

namespace SortBounds.Projects.BestCase

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- **The best-case bound for any value type**: every correct comparison sort makes at
least `n − 1` comparisons on every injective `α`-valued input, for any linear order `α`
with `n` values in increasing order. -/
theorem pred_le_cost_of_orderEmb (a : Fin n ↪o α) {t : Tree n} (h : Correct (α := α) t)
    {x : Fin n → α} (hx : Function.Injective x) : n - 1 ≤ cost t x := by
  rw [cost_eq_of_pattern t (pattern_rankPerm hx)]
  exact pred_le_cost (correct_of_orderEmb a h) (xOfPerm_injective _)

end SortBounds.Projects.BestCase
