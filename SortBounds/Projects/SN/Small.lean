/-
SortBounds/Projects/SN/Small.lean

Milestone M1 of the `SN` lane: the optimal counts for the small cases, where the
exact value can be certified by an explicit tree (upper bound) plus counting
(lower bound `S_lower`).

* `S 0 = 0`, `S 1 = 0`: no comparisons are needed for a single (or empty) input.
* `S 2 = 1`: `SortBounds.tree2` attains the information bound.
* `S 3 = 3`: `tree3` below sorts three elements with three comparisons, and
  `⌈log₂ 3!⌉ = 3 ≤ S 3` from counting.
-/
import SortBounds.Projects.SN.Basic
import SortBounds.Comparison.Examples

namespace SortBounds.Projects.SN

open SortBounds

/-! ### Degenerate sizes -/

theorem correct_leaf_zero (σ : Equiv.Perm (Fin 0)) : Correct (α := ℕ) (Tree.leaf σ) := by
  intro x _ a b _
  exact a.elim0

theorem correct_leaf_one (σ : Equiv.Perm (Fin 1)) : Correct (α := ℕ) (Tree.leaf σ) := by
  intro x _ a b hab
  rw [Subsingleton.elim a b] at hab
  exact absurd hab (lt_irrefl _)

theorem S_zero : S 0 = 0 := by
  have hle : S 0 ≤ 0 := (S_le_iff 0 0).2 ⟨Tree.leaf 1, correct_leaf_zero 1, Nat.zero_le 0⟩
  omega

theorem S_one : S 1 = 0 := by
  have hle : S 1 ≤ 0 := (S_le_iff 1 0).2 ⟨Tree.leaf 1, correct_leaf_one 1, Nat.zero_le 0⟩
  omega

/-! ### Three elements -/

/-- A depth-`3` sorting tree on three positions.  Compare `0` with `1`; for each
answer insert the third element with two more comparisons (the second comparison
of each inner pair can be skipped when the element is already the largest).  The
six leaves carry the six orders. -/
def tree3 : Tree 3 :=
  Tree.node 0 1
    (Tree.node 1 2
      (Tree.leaf 1)
      (Tree.node 0 2
        (Tree.leaf (Equiv.swap 1 2))
        (Tree.leaf (Equiv.swap 0 2 * Equiv.swap 1 2))))
    (Tree.node 0 2
      (Tree.leaf (Equiv.swap 0 1))
      (Tree.node 1 2
        (Tree.leaf (Equiv.swap 0 1 * Equiv.swap 1 2))
        (Tree.leaf (Equiv.swap 0 2))))

theorem tree3_depth : depth tree3 = 3 := by decide

theorem tree3_correct : Correct (α := ℕ) tree3 := by
  intro x hx
  have h01 : x 0 ≠ x 1 := hx.ne (by decide)
  have h02 : x 0 ≠ x 2 := hx.ne (by decide)
  have h12 : x 1 ≠ x 2 := hx.ne (by decide)
  by_cases c01 : x 0 < x 1
  · by_cases c12 : x 1 < x 2
    · have hr : run tree3 x = (1 : Equiv.Perm (Fin 3)) := by simp [tree3, run, c01, c12]
      rw [hr]
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
      all_goals omega
    · by_cases c02 : x 0 < x 2
      · have hr : run tree3 x = Equiv.swap 1 2 := by simp [tree3, run, c01, c12, c02]
        rw [hr]
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [Equiv.swap_apply_def]
        all_goals omega
      · have hr : run tree3 x = (Equiv.swap 0 2 * Equiv.swap 1 2) := by
          simp [tree3, run, c01, c12, c02]
        rw [hr]
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [Equiv.swap_apply_def]
        all_goals omega
  · by_cases c02 : x 0 < x 2
    · have hr : run tree3 x = Equiv.swap 0 1 := by simp [tree3, run, c01, c02]
      rw [hr]
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [Equiv.swap_apply_def]
      all_goals omega
    · by_cases c12 : x 1 < x 2
      · have hr : run tree3 x = (Equiv.swap 0 1 * Equiv.swap 1 2) := by
          simp [tree3, run, c01, c02, c12]
        rw [hr]
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [Equiv.swap_apply_def]
        all_goals omega
      · have hr : run tree3 x = Equiv.swap 0 2 := by simp [tree3, run, c01, c02, c12]
        rw [hr]
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [Equiv.swap_apply_def]
        all_goals omega

theorem S_two : S 2 = 1 := by
  have hle : S 2 ≤ 1 := (S_le_iff 2 1).2 ⟨tree2, tree2_correct, by simp [tree2_depth]⟩
  have hge : 1 ≤ S 2 := by
    have h := S_lower 2
    have hc : Nat.clog 2 (Nat.factorial 2) = 1 := by norm_num
    omega
  omega

theorem S_three : S 3 = 3 := by
  have hle : S 3 ≤ 3 := (S_le_iff 3 3).2 ⟨tree3, tree3_correct, by decide⟩
  have hge : 3 ≤ S 3 := by
    have h := S_lower 3
    have hc : Nat.clog 2 (Nat.factorial 3) = 3 := by norm_num
    omega
  omega

end SortBounds.Projects.SN
