/-
SortBounds/Tree.lean

The comparison model, as a binary decision tree.  A deterministic
comparison-based sorting algorithm is *exactly* a binary tree whose internal
nodes ask "is `x i < x j`?" and whose leaves are candidate output
permutations.  Everything below is therefore model-independent: no formal
semantics of a programming language is needed, and no step counting.
-/
import SortBounds.Basic

namespace SortBounds

variable {n : ℕ} {α : Type*}

/-- A comparison tree on `n` positions.  Internal nodes compare `x i` with `x j`
and branch on the outcome; leaves carry a candidate output permutation. -/
inductive Tree (n : ℕ) where
  | leaf : Equiv.Perm (Fin n) → Tree n
  | node : Fin n → Fin n → Tree n → Tree n → Tree n

/-- Run the tree on input `x`: follow the comparisons, return the leaf's
permutation.  This is the output of the algorithm. -/
def run [LinearOrder α] : Tree n → (Fin n → α) → Equiv.Perm (Fin n)
  | .leaf σ, _ => σ
  | .node i j l r, x => if x i < x j then run l x else run r x

/-- Number of comparisons the algorithm performs on input `x`: the number of
internal nodes on the path taken by `x`. -/
def cost [LinearOrder α] : Tree n → (Fin n → α) → ℕ
  | .leaf _, _ => 0
  | .node i j l r, x => 1 + (if x i < x j then cost l x else cost r x)

/-- Number of leaves of the tree. -/
def numLeaves : Tree n → ℕ
  | .leaf _ => 1
  | .node _ _ l r => numLeaves l + numLeaves r

/-- Depth of the tree: the worst-case number of comparisons. -/
def depth : Tree n → ℕ
  | .leaf _ => 0
  | .node _ _ l r => 1 + max (depth l) (depth r)

/-- The set of permutations occurring as leaf labels. -/
def labels : Tree n → Finset (Equiv.Perm (Fin n))
  | .leaf σ => {σ}
  | .node _ _ l r => labels l ∪ labels r

/-- A correct comparison-based sorting algorithm, as a tree: on every input
with pairwise distinct values it outputs the (unique) sorting permutation. -/
def Correct [LinearOrder α] (t : Tree n) : Prop :=
  ∀ x : Fin n → α, Function.Injective x → Sorts x (run t x)

theorem run_mem_labels [LinearOrder α] (t : Tree n) (x : Fin n → α) : run t x ∈ labels t := by
  induction t with
  | leaf σ => simp [run, labels]
  | node i j l r ihl ihr =>
    show (if x i < x j then run l x else run r x) ∈ labels l ∪ labels r
    split_ifs
    · exact Finset.mem_union_left _ ihl
    · exact Finset.mem_union_right _ ihr

theorem card_labels_le_numLeaves (t : Tree n) : (labels t).card ≤ numLeaves t := by
  induction t with
  | leaf σ => simp [labels, numLeaves]
  | node i j l r ihl ihr =>
    show (labels l ∪ labels r).card ≤ numLeaves l + numLeaves r
    calc (labels l ∪ labels r).card ≤ (labels l).card + (labels r).card := Finset.card_union_le _ _
      _ ≤ numLeaves l + numLeaves r := Nat.add_le_add ihl ihr

theorem numLeaves_le_pow_depth (t : Tree n) : numLeaves t ≤ 2 ^ depth t := by
  induction t with
  | leaf σ => simp [numLeaves, depth]
  | node i j l r ihl ihr =>
    show numLeaves l + numLeaves r ≤ 2 ^ (1 + max (depth l) (depth r))
    have key : ∀ a b : ℕ, 2 ^ a + 2 ^ b ≤ 2 ^ (1 + max a b) := by
      intro a b
      rcases le_total a b with h | h
      · calc 2 ^ a + 2 ^ b ≤ 2 ^ b + 2 ^ b :=
              Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) h) le_rfl
          _ = 2 ^ (b + 1) := by ring
          _ = 2 ^ (1 + max a b) := by rw [max_eq_right h]; ring
      · calc 2 ^ a + 2 ^ b ≤ 2 ^ a + 2 ^ a :=
              Nat.add_le_add le_rfl (Nat.pow_le_pow_right (by norm_num) h)
          _ = 2 ^ (a + 1) := by ring
          _ = 2 ^ (1 + max a b) := by rw [max_eq_left h]; ring
    exact le_trans (Nat.add_le_add ihl ihr) (key _ _)

/-- **Every correct comparison sort has at least `Nat.factorial n` leaves.** -/
theorem factorial_le_numLeaves {t : Tree n} (h : Correct (α := ℕ) t) :
    Nat.factorial n ≤ numLeaves t := by
  have hrun : ∀ p : Equiv.Perm (Fin n), run t (xOfPerm p) = p := by
    intro p
    exact Sorts.unique (xOfPerm_injective p) (h (xOfPerm p) (xOfPerm_injective p)) (xOfPerm_sorts p)
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆ labels t := by
    intro p _
    rw [← hrun p]
    exact run_mem_labels t (xOfPerm p)
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  calc Nat.factorial n = (Finset.univ : Finset (Equiv.Perm (Fin n))).card := hcard.symm
    _ ≤ (labels t).card := Finset.card_le_card hsub
    _ ≤ numLeaves t := card_labels_le_numLeaves t

/-- **Comparison lower bound, combinatorial form.**  Any correct comparison sort
on `n` distinct values has a decision tree with at least `Nat.factorial n` leaves; a binary
tree of depth `d` has at most `2^d` leaves, so `Nat.factorial n ≤ 2^depth`. -/
theorem factorial_le_two_pow_depth {t : Tree n} (h : Correct (α := ℕ) t) :
    Nat.factorial n ≤ 2 ^ depth t :=
  le_trans (factorial_le_numLeaves h) (numLeaves_le_pow_depth t)

/-- The number of comparisons made on any input is at most the depth. -/
theorem cost_le_depth [LinearOrder α] (t : Tree n) (x : Fin n → α) : cost t x ≤ depth t := by
  induction t with
  | leaf σ => simp [cost, depth]
  | node i j l r ihl ihr =>
    show 1 + (if x i < x j then cost l x else cost r x) ≤ 1 + max (depth l) (depth r)
    split_ifs
    · exact Nat.add_le_add_left (le_trans ihl (le_max_left _ _)) 1
    · exact Nat.add_le_add_left (le_trans ihr (le_max_right _ _)) 1

end SortBounds
