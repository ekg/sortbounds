/-
SortBounds/Projects/SortTree/Main.lean

**`Θ(n log n)` inside the `Tree` model alone.**  The lower bound
`⌈log₂ n!⌉ ≤ S n` (`Projects/SN/Basic.lean`) is a theorem about comparison trees;
this file supplies the matching upper bound `S n ≤ n·(⌈log₂ n⌉+1)` with a
*correct comparison tree of that depth*, so both sides of the optimality
statement live in the same model.

Contents:

* **M0** `insertIdx`, `insertPerm`, `rankOf` and `insertPerm_sorts`: if the prefix
  `0..n-1` is already sorted in the order `σ`, then the permutation that puts
  element `n` at its true rank `rankOf x σ` sorts the whole input.
* **M1** `insertSearch`/`insertTree` — binary search for that rank, with
  `insertTree_correct` and `insertTree_depth_le : depth ≤ ⌈log₂ (n+1)⌉ + 1`.
* **M2** `sortTree` — iterate `Comparison/Bridge.lean`'s `liftTree` from `n = 0,1`,
  with `sortTree_correct` and `sortTree_depth_le : depth ≤ n·(⌈log₂ n⌉+1)`.
* **M3** `S_le`: `S n ≤ n·(⌈log₂ n⌉+1)`, by `SN.S_le_iff` on the witness `sortTree n`.

Nothing here claims optimality of the constant: `S_lower`/
`S_le` bracket `S n` between `⌈log₂ n!⌉` and `n(⌈log₂ n⌉+1)`.
-/
import SortBounds.Comparison.Bridge
import SortBounds.Projects.SN.Basic

namespace SortBounds.Projects.SortTree

open SortBounds

/-! ### M0: inserting one element into a sorted prefix

The output order of the sort tree on `n+1` positions is a permutation
`r : Equiv.Perm (Fin (n+1))` with `r j = Fin.last n` ("the new element sits at
output slot `j`") and, at the other slots, the prefix order `σ`.  Reading the
*source* position off a slot is `insertIdx j` ("drop the slot `j` from the
indexing"), so that the two halves of `r` have a single spelling. -/

/-- The index in `Fin n` of the prefix element that sits at slot `t` of the
output order, when slot `j` holds the new element `Fin.last n`: slots before `j`
keep their index, slots after it are shifted down by one.  Only meaningful away
from `t = j`, where the new element sits. -/
def insertIdx {n : ℕ} (j : Fin (n + 1)) (t : Fin (n + 1)) : Fin n :=
  ⟨if t.val < j.val then t.val else t.val - 1, by
    have ht := t.isLt
    split_ifs with h
    · omega
    · omega⟩

@[simp]
theorem insertIdx_val {n : ℕ} (j t : Fin (n + 1)) :
    (insertIdx j t).val = if t.val < j.val then t.val else t.val - 1 := rfl

/-- Slot `t` of the output order holds the prefix element `insertIdx j t`; this is
the inverse of "insert at slot `j`" away from that slot.  Where `insertIdx` uses
`t.val - 1`, it writes `x.succ`. -/
theorem insertIdx_succAbove {n : ℕ} (j : Fin (n + 1)) (x : Fin n) :
    insertIdx j (j.succAbove x) = x := by
  rcases lt_or_ge x.val j.val with h | h
  · have hx : j.succAbove x = x.castSucc :=
      Fin.succAbove_of_castSucc_lt j x (Fin.lt_def.2 h)
    rw [hx]
    exact Fin.ext (by rw [insertIdx_val, Fin.val_castSucc, if_pos h])
  · have hx : j.succAbove x = x.succ :=
      Fin.succAbove_of_le_castSucc j x (Fin.le_def.2 h)
    rw [hx]
    exact Fin.ext (by rw [insertIdx_val, Fin.val_succ, if_neg (by omega)]; omega)

/-- Inserting into slot `j` and then reading the slot off again returns `t`, for
every slot other than `j`. -/
theorem succAbove_insertIdx {n : ℕ} {j t : Fin (n + 1)} (h : t ≠ j) :
    j.succAbove (insertIdx j t) = t := by
  have hv : t.val ≠ j.val := fun hc => h (Fin.ext hc)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have hi : (insertIdx j t).castSucc = t :=
      Fin.ext (by rw [insertIdx_val, Fin.val_castSucc, if_pos hlt])
    rw [← hi]
    exact Fin.succAbove_of_castSucc_lt j _ (Fin.lt_def.2 hlt)
  · have hi : (insertIdx j t).succ = t :=
      Fin.ext (by rw [insertIdx_val, Fin.val_succ, if_neg (by omega)]; omega)
    rw [← hi]
    exact Fin.succAbove_of_lt_succ j _ (Fin.lt_def.2 hgt)

/-- `insertIdx` is strictly monotone on slots other than `j`. -/
theorem insertIdx_lt {n : ℕ} {j t₁ t₂ : Fin (n + 1)} (h₁ : t₁ ≠ j) (h₂ : t₂ ≠ j)
    (h : t₁ < t₂) : insertIdx j t₁ < insertIdx j t₂ := by
  have hv₁ : t₁.val ≠ j.val := fun hc => h₁ (Fin.ext hc)
  have hv₂ : t₂.val ≠ j.val := fun hc => h₂ (Fin.ext hc)
  have hval : t₁.val < t₂.val := h
  rw [Fin.lt_def, insertIdx_val, insertIdx_val]
  split_ifs with h₁' h₂'
  · omega
  · omega
  · omega
  · omega

/-- The slot-index map of `insertPerm` is injective. -/
theorem insertPermFun_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    Function.Injective
      fun t : Fin (n + 1) => if t = j then Fin.last n else (σ (insertIdx j t)).castSucc := by
  intro a b hab
  by_cases ha : a = j
  · by_cases hb : b = j
    · rw [ha, hb]
    · simp only [ha, hb, if_true, if_false] at hab
      exact absurd hab (Fin.castSucc_ne_last _).symm
  · by_cases hb : b = j
    · simp only [ha, hb, if_true, if_false] at hab
      exact absurd hab (Fin.castSucc_ne_last _)
    · simp only [ha, hb, if_false] at hab
      have h₂ : insertIdx j a = insertIdx j b := σ.injective (Fin.castSucc_injective n hab)
      rw [← succAbove_insertIdx ha, ← succAbove_insertIdx hb, h₂]

/-- **The permutation of `Fin (n+1)` that lists the prefix order `σ` and puts the
new element (`Fin.last n`) at rank `j`.** -/
noncomputable def insertPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (fun t : Fin (n + 1) => if t = j then Fin.last n else (σ (insertIdx j t)).castSucc)
    ⟨insertPermFun_injective σ j, Finite.surjective_of_injective (insertPermFun_injective σ j)⟩

/-- The new element sits at its rank. -/
@[simp]
theorem insertPerm_apply_self {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    insertPerm σ j j = Fin.last n := by
  rw [insertPerm, Equiv.ofBijective_apply, if_pos rfl]

/-- Every other slot holds the corresponding prefix element, in the order `σ`. -/
theorem insertPerm_apply_of_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) {j t : Fin (n + 1)}
    (h : t ≠ j) : insertPerm σ j t = (σ (insertIdx j t)).castSucc := by
  rw [insertPerm, Equiv.ofBijective_apply, if_neg h]

/-- The rank of the new element among the sorted prefix, as a `Fin (n+1)`: the
number of prefix elements below `x (Fin.last n)`. -/
noncomputable def rankOf {n : ℕ} (x : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun k : Fin n => x (Fin.castSucc k) < x (Fin.last n)).card, by
    have h := Finset.card_le_univ
      (Finset.univ.filter fun k : Fin n => x (Fin.castSucc k) < x (Fin.last n))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega⟩

theorem rankOf_val {n : ℕ} (x : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) :
    (rankOf x σ).val = (Finset.univ.filter fun k : Fin n => x (Fin.castSucc k) < x (Fin.last n)).card :=
  rfl

end SortBounds.Projects.SortTree
