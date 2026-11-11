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

/-- **The boundary of the lane's claim**: from `n = 12` on, Ford–Johnson's count exceeds
`⌈log₂ n!⌉` (and at `n = 22` again), so `S_eq_clog` cannot be extended with this tree. -/
theorem fjCountJ_not_attained :
    fjCountJ 12 = 30 ∧ Nat.clog 2 (Nat.factorial 12) = 29 ∧
      fjCountJ 22 = 71 ∧ Nat.clog 2 (Nat.factorial 22) = 70 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end SortBounds.Projects.FjTree
