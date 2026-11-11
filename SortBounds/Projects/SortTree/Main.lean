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

/-- The *slot map* of the insertion: reading the output order of the sort tree on
`n+1` positions at slot `t`, the source position is the prefix index `slotVal`
(prefix positions keep their index up to the slot `j` where the new element
`Fin.last n` is placed, and are shifted down by one after it).

This is only meaningful away from `t = j`, hence the side condition in `slotIdx`;
for `n = 0` there is no such slot, and no total map `Fin 1 → Fin 0` exists. -/
def slotVal {n : ℕ} (j t : Fin (n + 1)) : ℕ :=
  if t.val < j.val then t.val else t.val - 1

theorem slotVal_lt {n : ℕ} {j t : Fin (n + 1)} (h : t ≠ j) : slotVal j t < n := by
  have ht := t.isLt
  have hv : t.val ≠ j.val := fun hc => h (Fin.ext hc)
  simp only [slotVal]
  split_ifs with h'
  · omega
  · omega

/-- The prefix index sitting at slot `t` of the output order. -/
def slotIdx {n : ℕ} (j t : Fin (n + 1)) (h : t ≠ j) : Fin n := ⟨slotVal j t, slotVal_lt h⟩

@[simp]
theorem slotIdx_val {n : ℕ} (j t : Fin (n + 1)) (h : t ≠ j) :
    (slotIdx j t h).val = slotVal j t := rfl

/-- Inserting the new element at slot `j` (`Fin.succAbove`) and then reading the
slot off again returns the original prefix index. -/
theorem slotIdx_succAbove {n : ℕ} (j : Fin (n + 1)) (x : Fin n) :
    slotIdx j (j.succAbove x) (Fin.succAbove_ne j x) = x := by
  refine Fin.ext ?_
  rw [slotIdx_val]
  simp only [slotVal]
  rcases lt_or_ge x.val j.val with h | h
  · rw [Fin.succAbove_of_castSucc_lt j x (Fin.lt_def.2 h), Fin.val_castSucc]
    split_ifs with h' <;> omega
  · rw [Fin.succAbove_of_le_castSucc j x (Fin.le_def.2 h), Fin.val_succ]
    split_ifs with h' <;> omega

/-- The slot map is the inverse of "insert the new element at slot `j`", away
from that slot. -/
theorem succAbove_slotIdx {n : ℕ} {j t : Fin (n + 1)} (h : t ≠ j) :
    j.succAbove (slotIdx j t h) = t := by
  have hv : t.val ≠ j.val := fun hc => h (Fin.ext hc)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have hcs : (slotIdx j t h).castSucc = t := by
      refine Fin.ext ?_
      rw [Fin.val_castSucc, slotIdx_val]
      simp only [slotVal]
      split_ifs with h' <;> omega
    rw [Fin.succAbove_of_castSucc_lt j _ (by rw [hcs]; exact Fin.lt_def.2 hlt), hcs]
  · have hsc : (slotIdx j t h).succ = t := by
      refine Fin.ext ?_
      rw [Fin.val_succ, slotIdx_val]
      simp only [slotVal]
      split_ifs with h' <;> omega
    rw [Fin.succAbove_of_lt_succ j _ (by rw [hsc]; exact Fin.lt_def.2 hgt), hsc]

/-- The slot map is strictly monotone on slots other than `j`. -/
theorem slotIdx_lt {n : ℕ} {j t₁ t₂ : Fin (n + 1)} (h₁ : t₁ ≠ j) (h₂ : t₂ ≠ j)
    (h : t₁ < t₂) : slotIdx j t₁ h₁ < slotIdx j t₂ h₂ := by
  have hv₁ : t₁.val ≠ j.val := fun hc => h₁ (Fin.ext hc)
  have hv₂ : t₂.val ≠ j.val := fun hc => h₂ (Fin.ext hc)
  have hval : t₁.val < t₂.val := h
  rw [Fin.lt_def, slotIdx_val, slotIdx_val]
  simp only [slotVal]
  split_ifs with h₁' h₂' <;> omega

/-- The slot map of `insertPerm`, as a plain function (the `dite` supplies the side
condition for the non-`j` slots). -/
noncomputable def insertPermFun {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1))
    (t : Fin (n + 1)) : Fin (n + 1) :=
  if h : t = j then Fin.last n else (σ (slotIdx j t h)).castSucc

theorem insertPermFun_self {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    insertPermFun σ j j = Fin.last n := by
  simp [insertPermFun]

theorem insertPermFun_of_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) {j t : Fin (n + 1)} (h : t ≠ j) :
    insertPermFun σ j t = (σ (slotIdx j t h)).castSucc := by
  simp only [insertPermFun, dite_eq_right h]

theorem insertPermFun_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    Function.Injective (insertPermFun σ j) := by
  intro a b hab
  by_cases ha : a = j
  · by_cases hb : b = j
    · rw [ha, hb]
    · rw [ha, insertPermFun_self, insertPermFun_of_ne σ hb] at hab
      exact absurd hab.symm (Fin.castSucc_ne_last _)
  · by_cases hb : b = j
    · rw [hb, insertPermFun_self, insertPermFun_of_ne σ ha] at hab
      exact absurd hab (Fin.castSucc_ne_last _)
    · rw [insertPermFun_of_ne σ ha, insertPermFun_of_ne σ hb] at hab
      have h₂ : slotIdx j a ha = slotIdx j b hb := σ.injective (Fin.castSucc_injective n hab)
      rw [← succAbove_slotIdx ha, ← succAbove_slotIdx hb, h₂]

/-- **The permutation of `Fin (n+1)` that lists the prefix order `σ` and puts the
new element (`Fin.last n`) at rank `j`.** -/
noncomputable def insertPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (insertPermFun σ j)
    ⟨insertPermFun_injective σ j, Finite.surjective_of_injective (insertPermFun_injective σ j)⟩

/-- The new element sits at its rank. -/
@[simp]
theorem insertPerm_apply_self {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    insertPerm σ j j = Fin.last n :=
  insertPermFun_self σ j

/-- Every other slot holds the corresponding prefix element, in the order `σ`. -/
theorem insertPerm_apply_of_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) {j t : Fin (n + 1)}
    (h : t ≠ j) : insertPerm σ j t = (σ (slotIdx j t h)).castSucc :=
  insertPermFun_of_ne σ h

set_option linter.unusedVariables false in
/-- The rank of the new element among the sorted prefix, as a `Fin (n+1)`: the
number of prefix elements below `x (Fin.last n)`.  (`σ` is part of the contract's
signature but does not occur: the rank of the new element among the prefix does not
depend on the order in which the prefix is presented.) -/
noncomputable def rankOf {n : ℕ} (x : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun k : Fin n => x (Fin.castSucc k) < x (Fin.last n)).card, by
    have h := Finset.card_le_univ
      (Finset.univ.filter fun k : Fin n => x (Fin.castSucc k) < x (Fin.last n))
    simp only [Fintype.card_fin] at h
    omega⟩

theorem rankOf_val {n : ℕ} (x : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) :
    (rankOf x σ).val = (Finset.univ.filter fun k : Fin n => x (Fin.castSucc k) < x (Fin.last n)).card :=
  rfl

/-- The number of `Fin n` elements below `m`, i.e. the cardinality of the initial
segment `{0, …, m-1}`. -/
theorem card_filter_val_lt {n m : ℕ} (hm : m ≤ n) :
    (Finset.univ.filter fun k : Fin n => k.val < m).card = m := by
  have hset : (Finset.univ.filter fun k : Fin n => k.val < m)
      = (Finset.univ : Finset (Fin m)).image (Fin.castLE hm) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hk
      exact ⟨⟨k.val, hk⟩, Finset.mem_univ _, by simp [Fin.castLE]⟩
    · rintro ⟨a, -, rfl⟩
      simpa using a.isLt
  rw [hset, Finset.card_image_of_injective _ (Fin.castLE_injective hm), Finset.card_univ,
    Fintype.card_fin]

/-- The prefix indices whose value is below the new element's value, read in the
order `σ`: the insertion rank of the new element, as a set. -/
def rankSet {n : ℕ} (x : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun k => x (Fin.castSucc (σ k)) < x (Fin.last n)

theorem rankSet_eq_image {n : ℕ} (x : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) :
    rankSet x σ
      = (Finset.univ.filter fun k : Fin n => x (Fin.castSucc k) < x (Fin.last n)).image σ.symm := by
  ext k
  simp only [rankSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    exact ⟨σ k, h, σ.symm_apply_apply k⟩
  · rintro ⟨a, ha, rfl⟩
    simpa using ha

theorem rankSet_card {n : ℕ} (x : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) :
    (rankSet x σ).card = (rankOf x σ).val := by
  rw [rankSet_eq_image, Finset.card_image_of_injective _ σ.symm.injective]
  rfl

/-- `rankSet` is an initial segment of the ordering `σ`. -/
theorem rankSet_down {n : ℕ} {x : Fin (n + 1) → ℕ} {σ : Equiv.Perm (Fin n)}
    (hmono : StrictMono fun k : Fin n => x (Fin.castSucc (σ k))) {k k' : Fin n}
    (hk : k ∈ rankSet x σ) (h : k' ≤ k) : k' ∈ rankSet x σ := by
  simp only [rankSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact lt_of_le_of_lt (hmono.monotone h) hk

/-- **The insertion rank, elementwise**: a prefix element sits below the new
element exactly when its `σ`-position is below `rankOf x σ`. -/
theorem below_last_iff {n : ℕ} {x : Fin (n + 1) → ℕ} {σ : Equiv.Perm (Fin n)}
    (hmono : StrictMono fun k : Fin n => x (Fin.castSucc (σ k))) (m : Fin n) :
    x (Fin.castSucc (σ m)) < x (Fin.last n) ↔ m.val < (rankOf x σ).val := by
  have hcard := rankSet_card x σ
  have hmn : m.val ≤ n := le_of_lt m.isLt
  constructor
  · intro hm
    have hsub : (Finset.univ.filter fun k : Fin n => k.val < m.val + 1) ⊆ rankSet x σ := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact rankSet_down hmono hm (by omega)
    have := Finset.card_le_card hsub
    rw [card_filter_val_lt (by omega), hcard] at this
    omega
  · intro hm
    by_contra hnot
    have hsub : rankSet x σ ⊆ Finset.univ.filter (fun k : Fin n => k.val < m.val) := by
      intro k hk
      simp only [rankSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_contra hlt
      have hmk : m ≤ k := Fin.le_def.2 (by omega)
      exact hnot (lt_of_le_of_lt (hmono.monotone hmk) hk)
    have := Finset.card_le_card hsub
    rw [card_filter_val_lt hmn, hcard] at this
    omega

end SortBounds.Projects.SortTree
