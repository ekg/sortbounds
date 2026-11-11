/-
SortBounds/Projects/SN/Four.lean

`S 4 = 5`: five comparisons sort four elements, and counting forbids fewer
(`⌈log₂ 4!⌉ = ⌈log₂ 24⌉ = 5`).

The upper bound is the classical five-comparator sorting network
`(0,1), (2,3), (0,2), (1,3), (1,2)` — sort the two pairs, then merge with three
comparators — read as a comparison tree (`netTree`), so a five-comparator
sequence already has depth `5`.  Its correctness is reduced by
`correct_of_forall_run_xOfPerm` to the `4! = 24` canonical inputs, which is a
finite computation: the kernel checks it (`decide`), and no case analysis is
trusted on the side.

The network tree has `2 ^ 5 = 32` leaves, one per path through the five
comparators, but only `24` of them are reached by inputs with pairwise distinct
values; the rest carry labels that `Correct` never inspects, because `Correct`
quantifies over injective inputs only.
-/
import SortBounds.Projects.SN.Verify
import SortBounds.Projects.SN.Basic
import SortBounds.Comparison.LowerBound

namespace SortBounds.Projects.SN

open SortBounds

/-- The five comparators of the classical sorting network on four wires: sort
the two pairs, then `(0,2)`, `(1,3)`, `(1,2)` to merge them. -/
def net4 : List (Fin 4 × Fin 4) := [(0, 1), (2, 3), (0, 2), (1, 3), (1, 2)]

/-- The network `net4` as a comparison tree on four positions. -/
def tree4 : Tree 4 := netTree net4 1

/-- The network is a sequence of five comparators, so the tree has depth `5`. -/
theorem tree4_depth : depth tree4 = 5 := by
  rw [tree4, netTree_depth]
  decide

/-- One leaf per path through the five comparators. -/
theorem tree4_numLeaves : numLeaves tree4 = 32 := by decide

/-- The network sorts: on all `4! = 24` canonical inputs the tree outputs the
sorting permutation, hence on every `ℕ`-valued input with pairwise distinct
values (`Correct` quantifies over injective inputs only; other value types
transfer via `Comparison.General.correct_of_orderEmb`). -/
theorem tree4_correct : Correct (α := ℕ) tree4 :=
  correct_of_forall_run_xOfPerm (by decide)

/-- **`S 4 = 5`**: five comparisons sort four elements, and counting rules out
four. -/
theorem S_four : S 4 = 5 := by
  refine le_antisymm ?_ ?_
  · -- upper bound: the five-comparator network
    refine (S_le_iff 4 5).2 ⟨tree4, tree4_correct, ?_⟩
    rw [tree4_depth]
  · -- lower bound: `Nat.clog 2 4! = 5`
    have h := S_lower 4
    have h24 : Nat.clog 2 (Nat.factorial 4) = 5 := by decide
    omega

/-- **Five comparisons are necessary in the *comparison-count* reading too**, not
just the depth reading: no correct tree keeps every input at `≤ 4` comparisons.
(`S 4 = 5` bounds the least depth; this bounds the least worst-case `cost`, which
is the quantity "fewest comparisons that suffice" refers to.) -/
theorem four_needs_five_comparisons :
    ¬ ∃ t : Tree 4, Correct (α := ℕ) t ∧
      ∀ x : Fin 4 → ℕ, Function.Injective x → cost t x ≤ 4 := by
  rintro ⟨t, ht, hcost⟩
  have hwc : worstCase t ≤ 4 := by
    apply Finset.sup_le
    intro p _
    exact hcost (xOfPerm p) (xOfPerm_injective p)
  have hlb := logb_factorial_le_worstCase ht
  have h24 : (4 : ℝ) < Real.logb 2 (Nat.factorial 4) := by
    have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hfac]
    have hpow : (2 : ℝ) ^ 4 < 24 := by norm_num
    calc (4 : ℝ) = Real.logb 2 ((2 : ℝ) ^ 4) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
      _ < Real.logb 2 (24 : ℝ) := Real.logb_lt_logb (b := 2) (by norm_num : (1 : ℝ) < 2) (by positivity) hpow
  have : (worstCase t : ℝ) ≤ 4 := by exact_mod_cast hwc
  linarith

end SortBounds.Projects.SN
