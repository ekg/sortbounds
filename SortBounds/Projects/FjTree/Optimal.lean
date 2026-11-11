/-
SortBounds/Projects/FjTree/Optimal.lean

**The consequence for the least depth `S n`**: because `fjTree n` is a correct tree whose
depth is at most Ford–Johnson's comparison count `fjCountJ n` (`Correct.fjTree_correct`,
`Main.fjTree_depth_le`), the count is an upper bound on `S n`.  Combined with the counting
lower bound `SN.S_lower` and the arithmetic identity `fjCountJ n = ⌈log₂ n!⌉`
(`FordJohnson.fjCountJ_eq_clog_factorial`), this settles `S n` at the sizes where the count
meets the information-theoretic bound:

  `S n = ⌈log₂ n!⌉`  for `4 ≤ n ≤ 11`,  and for `n = 20, 21`.

That is *verified optimality of merge-insertion* at those sizes: not only does the
algorithm spend `⌈log₂ n!⌉` comparisons, but no comparison tree of smaller depth sorts `n`
elements.
-/
import SortBounds.Projects.FjTree.Correct

namespace SortBounds.Projects.FjTree

open SortBounds
open SortBounds.Projects.FordJohnson (fjCountJ fjCountJ_eq_clog_factorial
  fjCountJ_eq_clog_factorial_large)

/-- **The least depth is at most Ford–Johnson's count**: `fjTree n` is correct and its depth
is at most `fjCountJ n`, so `S n ≤ fjCountJ n`. -/
theorem S_le_fjCountJ (n : ℕ) : SortBounds.Projects.SN.S n ≤ fjCountJ n :=
  (SortBounds.Projects.SN.S_le_iff n (fjCountJ n)).2
    ⟨fjTree n, fjTree_correct n, fjTree_depth_le n⟩

/-- **Verified optimality of merge-insertion for `4 ≤ n ≤ 11`**: the least depth of a
correct comparison tree on `n` positions equals `⌈log₂ n!⌉`, attained by `fjTree n`. -/
theorem S_eq_clog (n : ℕ) (h4 : 4 ≤ n) (h11 : n ≤ 11) :
    SortBounds.Projects.SN.S n = Nat.clog 2 (Nat.factorial n) := by
  have hub : SortBounds.Projects.SN.S n ≤ Nat.clog 2 (Nat.factorial n) := by
    rw [← fjCountJ_eq_clog_factorial n h4 h11]
    exact S_le_fjCountJ n
  exact le_antisymm hub (SortBounds.Projects.SN.S_lower n)

/-- **Verified optimality of merge-insertion at `n = 20` and `n = 21`**, the two larger
sizes where Ford–Johnson's count meets `⌈log₂ n!⌉`. -/
theorem S_eq_clog_large :
    SortBounds.Projects.SN.S 20 = Nat.clog 2 (Nat.factorial 20) ∧
      SortBounds.Projects.SN.S 21 = Nat.clog 2 (Nat.factorial 21) := by
  have h20 := fjCountJ_eq_clog_factorial_large.1
  have h21 := fjCountJ_eq_clog_factorial_large.2
  have hub20 : SortBounds.Projects.SN.S 20 ≤ Nat.clog 2 (Nat.factorial 20) := by
    rw [← h20]; exact S_le_fjCountJ 20
  have hub21 : SortBounds.Projects.SN.S 21 ≤ Nat.clog 2 (Nat.factorial 21) := by
    rw [← h21]; exact S_le_fjCountJ 21
  exact ⟨le_antisymm hub20 (SortBounds.Projects.SN.S_lower 20),
    le_antisymm hub21 (SortBounds.Projects.SN.S_lower 21)⟩

/-- **Where the counting bound stops being tight**: at `n = 12` and `n = 22` Ford–Johnson's
count exceeds `⌈log₂ n!⌉`, so `S_eq_clog` cannot be extended there with this tree.  (It does
*not* exceed at `n = 20, 21`, which is `S_eq_clog_large`; see `S_gap_le_one` for the full
range `n ≤ 22`.) -/
theorem fjCountJ_not_attained :
    fjCountJ 12 = 30 ∧ Nat.clog 2 (Nat.factorial 12) = 29 ∧
      fjCountJ 22 = 71 ∧ Nat.clog 2 (Nat.factorial 22) = 70 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The gap is at most one up to `n = 22`**: Ford–Johnson's count is within one
comparison of the information-theoretic bound on that whole range (it meets it for
`n ≤ 11`, `20`, `21` and misses it by exactly one for `12 ≤ n ≤ 19`, `22`). -/
theorem S_gap_le_one (n : ℕ) (hn : n ≤ 22) :
    fjCountJ n ≤ Nat.clog 2 (Nat.factorial n) + 1 := by
  interval_cases n <;> decide

/-- **`S n` pinned to within one, for every `n ≤ 22`.**  This is the sharpest statement
that counting alone can reach: `12! < 2 ^ 29`, and Kraft realizes any `L ≤ 2 ^ d` as a
full binary tree of depth `≤ d`, so no leaf-counting argument can separate `S 12` from
`29`.  The exact value (`S 12 = 30`, Wells 1971) needs a pruned search. -/
theorem S_pin (n : ℕ) (hn : n ≤ 22) :
    Nat.clog 2 (Nat.factorial n) ≤ SN.S n ∧ SN.S n ≤ Nat.clog 2 (Nat.factorial n) + 1 :=
  ⟨SN.S_lower n, le_trans (S_le_fjCountJ n) (S_gap_le_one n hn)⟩

/-- **Transfer principle.**  Whoever shows that Ford–Johnson's count meets the bound at a
given `n` gets `S n = ⌈log₂ n!⌉` there: this is how `S_eq_clog` and `S_eq_clog_large` are
obtained, and it applies to any future size. -/
theorem S_eq_of_fjCountJ_eq (n : ℕ) (h : fjCountJ n = Nat.clog 2 (Nat.factorial n)) :
    SN.S n = Nat.clog 2 (Nat.factorial n) :=
  le_antisymm (h ▸ S_le_fjCountJ n) (SN.S_lower n)

/-- **Wells' 1965 construction, machine-checked**: 30 comparisons suffice to sort 12
elements (`S 12 ≤ 30`), while counting gives only `S 12 ≥ ⌈log₂ 12!⌉ = 29`.  So the
literature's `S 12 = 30` differs from what is proved here *only* in the lower bound. -/
theorem S_twelve_le : SN.S 12 ≤ 30 := by
  have h := S_le_fjCountJ 12
  have h30 : fjCountJ 12 = 30 := fjCountJ_not_attained.1
  omega

/-- **Peczarski's exact value at `n = 22` as a machine-checked upper bound**:
`S 22 ≤ 71`, while counting gives `S 22 ≥ ⌈log₂ 22!⌉ = 70`.  Again the gap to the
literature's `S 22 = 71` is exactly the lower bound. -/
theorem S_twenty_two_le : SN.S 22 ≤ 71 := by
  have h := S_le_fjCountJ 22
  have h71 : fjCountJ 22 = 71 := fjCountJ_not_attained.2.2.1
  omega

end SortBounds.Projects.FjTree
