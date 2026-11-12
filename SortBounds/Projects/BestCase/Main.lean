/-
SortBounds/Projects/BestCase/Main.lean

**The best case of a comparison sort is `n - 1`.**

Any correct comparison tree makes at least `n - 1` comparisons on *every* input
with pairwise distinct values — not only on the already-sorted one.  Chain:
`comparisonGraph t x` is connected (`Connected.lean`), a connected graph on `n`
vertices has at least `n - 1` edges, and the number of distinct edges is at most
the number of comparisons made (`Compared.lean`).
-/
import SortBounds.Projects.BestCase.Connected
import SortBounds.Comparison.WorstCase

namespace SortBounds.Projects.BestCase

open SortBounds

variable {n : ℕ}

/-- **Every connected graph on `n` vertices has at least `n - 1` edges**, stated for
the comparison graph of a run: `n - 1 ≤ #(comparedPairs t x)`. -/
theorem pred_le_card_comparedPairs {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) : n - 1 ≤ (comparedPairs t x).card := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hconn := connected_comparedPairs h hx hn
  have hedge : Nat.card (comparisonGraph t x).edgeSet ≤ (comparedPairs t x).card := by
    rw [Nat.card_coe_set_eq]
    calc ((comparisonGraph t x).edgeSet).ncard
        ≤ ((comparedPairs t x : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))).ncard := by
          refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
          simp only [comparisonGraph, SimpleGraph.edgeSet_fromEdgeSet]
          exact Set.sdiff_subset
      _ = (comparedPairs t x).card := Set.ncard_coe_finset _
  have hvert : Nat.card (Fin n) = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)
  have := hconn.card_vert_le_card_edgeSet_add_one
  omega

/-- **The best case is `n - 1`**: every correct comparison sort makes at least
`n - 1` comparisons on *every* input with distinct values. -/
theorem pred_le_cost {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) : n - 1 ≤ cost t x :=
  le_trans (pred_le_card_comparedPairs h hx) (card_comparedPairs_le_cost t x)

/-- The README's original claim is the special case `x = 0 < 1 < ⋯ < n - 1`: the
already-sorted input already forces `n - 1` comparisons. -/
theorem pred_le_cost_id {t : Tree n} (h : Correct (α := ℕ) t) :
    n - 1 ≤ cost t (fun i : Fin n => (i : ℕ)) := by
  refine pred_le_cost h ?_
  intro a b hab
  exact Fin.ext hab

/-- In the notation of `Comparison/WorstCase.lean`: the bound holds at every one of
the `n!` canonical injective inputs, not just at a generic one. -/
theorem pred_le_cost_xOfPerm {t : Tree n} (h : Correct (α := ℕ) t)
    (p : Equiv.Perm (Fin n)) : n - 1 ≤ cost t (xOfPerm p) :=
  pred_le_cost h (xOfPerm_injective p)

/-- Consequently the *worst* case is at least `n - 1` as well: `pred_le_cost` bounds
one input's cost, and no input costs more than the worst case (`le_worstCase`). -/
theorem pred_le_worstCase {t : Tree n} (h : Correct (α := ℕ) t) : n - 1 ≤ worstCase t :=
  le_trans (pred_le_cost_xOfPerm h 1) (le_worstCase t 1)

/-- Likewise the depth is at least `n - 1`: `cost_le_depth` bounds every input's cost
by the depth. -/
theorem pred_le_depth {t : Tree n} (h : Correct (α := ℕ) t) : n - 1 ≤ depth t :=
  le_trans (pred_le_cost h (x := fun i : Fin n => (i : ℕ)) fun _ _ hab => Fin.ext hab)
    (cost_le_depth t _)

end SortBounds.Projects.BestCase
