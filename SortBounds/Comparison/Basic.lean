/-
SortBounds/Basic.lean

The semantic core of the comparison-sorting lower bound: what it means for a
permutation to *sort* an injective input, that such a permutation is unique,
and the family of "adversarial" injective inputs indexed by permutations.
-/
import Mathlib

namespace SortBounds

open Finset

variable {α : Type*} {n : ℕ}

/-- `Sorts x r` says: reading the input `x : Fin n → α` in the order given by the
permutation `r` yields a strictly increasing sequence.  For injective `x` this is
exactly "the output of the algorithm is the sorted order of the input". -/
abbrev Sorts [Preorder α] (x : Fin n → α) (r : Equiv.Perm (Fin n)) : Prop :=
  StrictMono fun k => x (r k)

/-- A sorting permutation is unique for an injective input. -/
theorem Sorts.unique [LinearOrder α] {x : Fin n → α} (hx : Function.Injective x)
    {r r' : Equiv.Perm (Fin n)} (hr : Sorts x r) (hr' : Sorts x r') : r = r' := by
  have hs : (univ.image x).card = n := by
    rw [card_image_of_injective _ hx, card_univ, Fintype.card_fin]
  have key : ∀ (s : Equiv.Perm (Fin n)), Sorts x s →
      (fun k => x (s k)) = (univ.image x).orderEmbOfFin hs := by
    intro s hs'
    exact orderEmbOfFin_unique hs
      (fun k => mem_image_of_mem x (mem_univ (s k))) hs'
  have h1 := key r hr
  have h2 := key r' hr'
  refine Equiv.ext fun k => ?_
  exact hx (by rw [congrFun h1 k, congrFun h2 k])

/-- The `p`-th canonical injective input: element `i` has value `p.symm i`, so the
inputs are ranked exactly according to the permutation `p`. -/
def xOfPerm (p : Equiv.Perm (Fin n)) : Fin n → ℕ := fun i => (p.symm i : ℕ)

theorem xOfPerm_sorts (p : Equiv.Perm (Fin n)) : Sorts (xOfPerm p) p := by
  intro k l hkl
  show ((p.symm (p k) : Fin n) : ℕ) < ((p.symm (p l) : Fin n) : ℕ)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact hkl

theorem xOfPerm_injective (p : Equiv.Perm (Fin n)) : Function.Injective (xOfPerm p) := by
  intro i j h
  exact p.symm.injective (Fin.ext h)

theorem xOfPerm_nodup (p : Equiv.Perm (Fin n)) :
    ((List.ofFn (xOfPerm p)).Nodup) := by
  rw [List.nodup_ofFn]
  exact xOfPerm_injective p

end SortBounds
