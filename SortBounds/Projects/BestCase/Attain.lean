/-
SortBounds/Projects/BestCase/Attain.lean

**The bound `n - 1` is attained** (M3, the stretch goal of the lane).

`Main.lean` proves `n - 1 ≤ cost t x` for *every* correct tree and *every* injective
input.  Here a correct tree is built whose cost on the already-sorted input is
*exactly* `n - 1`, so `n - 1` is the best case, not merely a lower bound.

The tree is the "sorted chain" `x 0 < x 1 < ⋯ < x (n-1)`: it walks down the
comparisons `x 0 < x 1`, `x 1 < x 2`, … and answers the identity permutation if
every answer is "yes"; every input that breaks the chain is handed to an arbitrary
correct tree `T`.  On the sorted input the chain answers "yes" `n - 1` times, so the
cost is `n - 1`; on every other input the chain is left at some "no", and `T` sorts.

(The hypothesis `Correct T` is carried rather than constructed: a correct tree on
`n` positions exists — e.g. `SortBounds.Projects.SN.exists_correct_tree` — but this
lane does not need its construction.)
-/
import SortBounds.Projects.BestCase.Main
import SortBounds.Comparison.Aggregate

namespace SortBounds.Projects.BestCase

open SortBounds

variable {n m : ℕ}

/-! ### The sorted chain -/

/-- `chainAux T k hk` is the tree entered once the comparisons
`x k < x (k+1) < ⋯ < x (n-1)` are already known to hold: it asks about
`x (k-1) < x k` next, and hands the "no" answer to `T`.  For `k = 0` the chain is
complete, and the identity permutation is the answer. -/
noncomputable def chainAux (T : Tree n) : (k : ℕ) → k < n → Tree n
  | 0, _ => Tree.leaf 1
  | k + 1, hk => Tree.node ⟨k, by omega⟩ ⟨k + 1, hk⟩ (chainAux T k (by omega)) T

@[simp]
theorem chainAux_zero (T : Tree n) (h : 0 < n) : chainAux T 0 h = Tree.leaf 1 := rfl

theorem chainAux_succ (T : Tree n) (k : ℕ) (h : k + 1 < n) :
    chainAux T (k + 1) h = Tree.node ⟨k, by omega⟩ ⟨k + 1, h⟩ (chainAux T k (by omega)) T :=
  rfl

/-- The "already sorted" chain on `n` positions: compare `x 0 < x 1 < ⋯ < x (n-1)`,
answer the identity permutation when all comparisons hold, and let `T` sort anything
that breaks the chain. -/
noncomputable def sortedChain : (n : ℕ) → Tree n → Tree n
  | 0, _ => Tree.leaf 1
  | m + 1, T => chainAux T m (Nat.lt_succ_self m)

theorem sortedChain_succ (T : Tree (m + 1)) :
    sortedChain (m + 1) T = chainAux T m (Nat.lt_succ_self m) := rfl

theorem sortedChain_zero (T : Tree 0) : sortedChain 0 T = Tree.leaf 1 := rfl

/-! ### The chain is a correct sort -/

/-- The chain's invariant: if the comparisons from position `k` upwards are known
to hold, then `chainAux T k` sorts `x`. -/
theorem chainAux_sorts {T : Tree (m + 1)} (hT : Correct (α := ℕ) T) {x : Fin (m + 1) → ℕ}
    (hx : Function.Injective x) (k : ℕ) (hk : k < m + 1)
    (hinv : ∀ i : Fin m, k ≤ i.val → x i.castSucc < x i.succ) :
    Sorts x (run (chainAux T k hk) x) := by
  induction k with
  | zero =>
    rw [chainAux_zero]
    have hmono : StrictMono x :=
      (Fin.strictMono_iff_lt_succ (f := x)).mpr fun i => hinv i (Nat.zero_le _)
    exact hmono
  | succ k ih =>
    rw [chainAux_succ, run_node]
    by_cases hlt : x ⟨k, by omega⟩ < x ⟨k + 1, hk⟩
    · rw [ite_eq_left hlt]
      refine ih (by omega) fun i hi => ?_
      by_cases hik : i.val = k
      · subst hik
        convert hlt using 2 <;> exact Fin.ext rfl
      · exact hinv i (by omega)
    · rw [ite_eq_right hlt]
      exact hT x hx

/-- **The sorted chain is a correct sort.** -/
theorem sortedChain_correct {T : Tree n} (hT : Correct (α := ℕ) T) :
    Correct (α := ℕ) (sortedChain n T) := by
  cases n with
  | zero =>
    intro x hx a b hab
    exact absurd a.isLt (by omega)
  | succ m =>
    intro x hx
    rw [sortedChain_succ]
    exact chainAux_sorts hT hx m (Nat.lt_succ_self m) fun i hi => absurd hi (by omega)

/-! ### Its cost on the sorted input is `n - 1` -/

theorem cost_chainAux_id (T : Tree n) (k : ℕ) (hk : k < n) :
    cost (chainAux T k hk) (fun i : Fin n => (i : ℕ)) = k := by
  induction k with
  | zero => rw [chainAux_zero]; rfl
  | succ k ih =>
    rw [chainAux_succ, cost_node]
    have hlt : ((⟨k, by omega⟩ : Fin n) : ℕ) < ((⟨k + 1, hk⟩ : Fin n) : ℕ) := by
      show k < k + 1
      omega
    rw [ite_eq_left hlt, ih]
    omega

/-- **The best case is exactly `n - 1`.**  Given any correct tree (to sort the inputs
that break the chain) there is a correct tree whose cost on the already-sorted input
is exactly `n - 1` — matching the lower bound of `pred_le_cost`. -/
theorem exists_correct_cost_id_eq {T : Tree n} (hT : Correct (α := ℕ) T) :
    ∃ t : Tree n, Correct (α := ℕ) t ∧ cost t (fun i : Fin n => (i : ℕ)) = n - 1 := by
  refine ⟨sortedChain n T, sortedChain_correct hT, ?_⟩
  cases n with
  | zero => rfl
  | succ m =>
    rw [sortedChain_succ, cost_chainAux_id]
    omega

/-! ### Non-vacuity: `Correct` has an explicit inhabitant -/

/-- The tree for two positions: ask `x 0 < x 1` and answer the matching
permutation.  A concrete witness that `Correct` is inhabited, so neither
`pred_le_cost` nor `exists_correct_cost_id_eq` is a statement about an empty class. -/
def sortTwo : Tree 2 := Tree.node 0 1 (Tree.leaf 1) (Tree.leaf (Equiv.swap 0 1))

theorem sortTwo_correct : Correct (α := ℕ) sortTwo := by
  intro x hx
  have hrun : run sortTwo x =
      if x 0 < x 1 then run (Tree.leaf 1) x else run (Tree.leaf (Equiv.swap 0 1)) x := rfl
  rw [hrun]
  by_cases h : x 0 < x 1
  · rw [ite_eq_left h]
    simp only [run]
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · have hne : x 0 ≠ x 1 := fun he => absurd (hx he) (by decide)
    have hgt : x 1 < x 0 := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
    rw [ite_eq_right h]
    simp only [run]
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all

/-- On the sorted two-element input that tree makes exactly one comparison. -/
theorem sortTwo_cost : cost sortTwo (fun i : Fin 2 => (i : ℕ)) = 1 := by
  rw [show sortTwo = Tree.node 0 1 (Tree.leaf 1) (Tree.leaf (Equiv.swap 0 1)) from rfl,
    cost_node, ite_eq_left (show ((0 : Fin 2) : ℕ) < ((1 : Fin 2) : ℕ) from by decide)]
  rfl

end SortBounds.Projects.BestCase
