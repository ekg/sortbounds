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
#print axioms SortBounds.exists_input_cost_ge_of_orderEmb
#print axioms SortBounds.exists_input_cost_ge_quarter_of_orderEmb
#print axioms SortBounds.half_pow_le_factorial
#print axioms SortBounds.logb_factorial_ge_quarter
#print axioms SortBounds.radixSort_sorted
#print axioms SortBounds.radixSort_perm
#print axioms SortBounds.countingSort_stable
#print axioms SortBounds.radixSort_ignores_comparison
#print axioms SortBounds.msortCount_sorted
#print axioms SortBounds.msortCount_perm
#print axioms SortBounds.msortCount_le
#print axioms SortBounds.factorial_le_two_pow_length_of_sortsAll
#print axioms SortBounds.sorts_of_sortsAll
#print axioms SortBounds.sortsAll_of_sorts_zeroOne
#print axioms SortBounds.factorial_le_two_pow_length_of_sorts_zeroOne
#print axioms SortBounds.sorts_zeroOne_three_wire
#print axioms SortBounds.liftTree_correct
#print axioms SortBounds.liftTree_depth_le
-- lanes
#print axioms SortBounds.Projects.FordJohnson.insertCount_count
#print axioms SortBounds.Projects.FordJohnson.fjSort_count_le
#print axioms SortBounds.Projects.FordJohnson.fjSort_sorted
#print axioms SortBounds.Projects.FordJohnson.fjSort_perm
#print axioms SortBounds.Projects.FordJohnson.fjCount_le
#print axioms SortBounds.Projects.FordJohnson.fjSortJ_count_le
#print axioms SortBounds.Projects.FordJohnson.fjCountJ_table
#print axioms SortBounds.Projects.SN.exists_correct_tree
#print axioms SortBounds.Projects.SN.S_le_iff
#print axioms SortBounds.Projects.SN.S_lower
#print axioms SortBounds.Projects.SN.S_three
#print axioms SortBounds.Projects.SN.S_four
#print axioms SortBounds.Projects.SN.S_five
#print axioms SortBounds.Projects.SN.four_needs_five_comparisons
#print axioms SortBounds.Projects.SN.five_needs_seven_comparisons
#print axioms SortBounds.Projects.XY.pairSums_card_le
#print axioms SortBounds.Projects.XY.naivePairsSorted_perm
#print axioms SortBounds.Projects.XY.naivePairsSorted_count
#print axioms SortBounds.Projects.BenOr.ADT.card_cells_le
#print axioms SortBounds.Projects.BenOr.exists_decidesReal_distinct
#print axioms SortBounds.Projects.BenOr.halfLineTree_decidesReal
#print axioms SortBounds.Projects.SAIS.suffix_compare_eq_of_lcp
#print axioms SortBounds.Projects.SAIS.cmpFrom_lcp_advance
#print axioms SortBounds.Projects.SAIS.three_mul_naiveInspectSum
