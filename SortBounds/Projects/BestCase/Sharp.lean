/-
SortBounds/Projects/BestCase/Sharp.lean

**The best case is exactly `n - 1`, unconditionally.**

`Attain.lean` builds a correct tree of best-case cost `n - 1` from *any* correct tree.
A correct tree exists on every `n` positions (`Projects/SN.exists_correct_tree` — the
compare-everything tree), so the hypothesis can be discharged: for every `n` there is
a correct comparison sort whose cost on the sorted input is exactly `n - 1`.

Together with `pred_le_cost` (`n - 1 ≤ cost t x` for every correct `t` and every
injective `x`) this pins the best case of comparison sorting at `n - 1`.
-/
import SortBounds.Projects.BestCase.Attain
import SortBounds.Projects.SN.Basic

namespace SortBounds.Projects.BestCase

open SortBounds

/-- **`n - 1` is attained and not merely a lower bound**: for every `n` there is a
correct comparison tree whose cost on the already-sorted input is exactly `n - 1`. -/
theorem exists_correct_cost_id_eq' (n : ℕ) :
    ∃ t : Tree n, Correct (α := ℕ) t ∧ cost t (fun i : Fin n => (i : ℕ)) = n - 1 := by
  obtain ⟨T, hT⟩ := SortBounds.Projects.SN.exists_correct_tree n
  exact exists_correct_cost_id_eq (n := n) hT

end SortBounds.Projects.BestCase
