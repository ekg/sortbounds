/-
Print the axioms each headline theorem depends on.  Expected: only Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`); in particular no
`sorryAx` and no `Lean.ofReduceBool` (which `native_decide` would introduce).

Run with:  lake env lean scripts/axioms.lean
-/
import SortBounds

open SortBounds

#print axioms SortBounds.Sorts.unique
#print axioms SortBounds.factorial_le_two_pow_depth
#print axioms SortBounds.factorial_le_two_pow_worstCase
#print axioms SortBounds.exists_input_cost_ge
#print axioms SortBounds.depth_ge_log2_factorial
#print axioms SortBounds.depth_ge_quarter
#print axioms SortBounds.exists_input_cost_ge_quarter
#print axioms SortBounds.not_forall_cost_lt_quarter
#print axioms SortBounds.avg_cost_ge_log2_factorial
#print axioms SortBounds.max_cost_ge_log2_factorial
#print axioms SortBounds.half_pow_le_factorial
#print axioms SortBounds.logb_factorial_ge_quarter
#print axioms SortBounds.radixSort_sorted
#print axioms SortBounds.radixSort_perm
#print axioms SortBounds.countingSort_stable
#print axioms SortBounds.radixSort_ignores_comparison
