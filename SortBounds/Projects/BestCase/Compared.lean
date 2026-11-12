/-
SortBounds/Projects/BestCase/Compared.lean

**The comparison graph of a run.**  Fix a tree `t` and an input `x`; the path `t`
takes on `x` asks a sequence of questions `x i < x j ?`.  `comparedPairs t x` is
the *set* of unordered position pairs asked along that path (repeats collapsed),
and `comparisonGraph t x` is the simple graph with those edges.

Two facts:

* `card_comparedPairs_le_cost`: the number of *distinct* pairs asked is at most
  the number of questions asked (`cost` counts questions with multiplicity).
* `run_eq_of_agree`: **the leaf reached depends only on the answers to the
  questions on the path**, so an input that answers every one of those questions
  the same way reaches the same leaf.

Together with `Connected.lean`'s "the comparison graph is connected" these give
`n - 1 ≤ cost` (`Main.lean`).
-/
import SortBounds.Comparison.Tree
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace SortBounds.Projects.BestCase

open SortBounds

variable {n : ℕ}

/-- The set of (distinct, unordered) pairs of positions compared along the path
that `t` takes on the input `x`.  A repeated comparison of the same pair
contributes its pair once. -/
def comparedPairs (t : Tree n) (x : Fin n → ℕ) : Finset (Sym2 (Fin n)) :=
  match t with
  | Tree.leaf _ => ∅
  | Tree.node i j l r =>
      insert s(i, j) (if x i < x j then comparedPairs l x else comparedPairs r x)

/-- The comparison graph of the run of `t` on `x`: vertices are positions, edges
are the pairs in `comparedPairs t x`.  Loop-shaped questions (`i = j`, whose
answer is always "no") are not edges of this graph. -/
def comparisonGraph (t : Tree n) (x : Fin n → ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (comparedPairs t x : Set (Sym2 (Fin n)))

@[simp]
theorem comparedPairs_leaf (σ : Equiv.Perm (Fin n)) (x : Fin n → ℕ) :
    comparedPairs (Tree.leaf σ) x = ∅ := rfl

theorem comparedPairs_node (i j : Fin n) (l r : Tree n) (x : Fin n → ℕ) :
    comparedPairs (Tree.node i j l r) x =
      insert s(i, j) (if x i < x j then comparedPairs l x else comparedPairs r x) := rfl

/-- A question asked at the root of a subtree is asked on the whole path. -/
theorem mem_comparedPairs_node {i j : Fin n} {l r : Tree n} {x : Fin n → ℕ} :
    s(i, j) ∈ comparedPairs (Tree.node i j l r) x := by
  rw [comparedPairs_node]
  exact Finset.mem_insert_self _ _

/-- **Distinct pairs asked ≤ questions asked.**  `cost` counts every internal node
on the path, so a pair asked twice is counted twice there but once here. -/
theorem card_comparedPairs_le_cost (t : Tree n) (x : Fin n → ℕ) :
    (comparedPairs t x).card ≤ cost t x := by
  induction t with
  | leaf σ => simp [comparedPairs, cost]
  | node i j l r ihl ihr =>
    rw [comparedPairs_node]
    show (insert s(i, j) (if x i < x j then comparedPairs l x else comparedPairs r x)).card
        ≤ 1 + (if x i < x j then cost l x else cost r x)
    calc (insert s(i, j) (if x i < x j then comparedPairs l x else comparedPairs r x)).card
        ≤ (if x i < x j then comparedPairs l x else comparedPairs r x).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (if x i < x j then cost l x else cost r x) + 1 := by
          refine Nat.add_le_add_right ?_ 1
          by_cases h : x i < x j
          · rw [ite_eq_left h, ite_eq_left h]; exact ihl
          · rw [ite_eq_right h, ite_eq_right h]; exact ihr
      _ = 1 + (if x i < x j then cost l x else cost r x) := Nat.add_comm _ _

/-- **The leaf depends only on the answers along the path.**  Two inputs that
agree on every question the path asks reach the same leaf.  (Compare
`SortBounds.run_eq_of_pattern`, which assumes agreement on *all* pairs; here only
the pairs in `comparedPairs t x` matter.) -/
theorem run_eq_of_agree (t : Tree n) (x y : Fin n → ℕ)
    (h : ∀ i j, s(i, j) ∈ comparedPairs t x → (x i < x j ↔ y i < y j)) :
    run t x = run t y := by
  induction t with
  | leaf σ => rfl
  | node i j l r ihl ihr =>
    have hroot : x i < x j ↔ y i < y j := h i j mem_comparedPairs_node
    show (if x i < x j then run l x else run r x) = (if y i < y j then run l y else run r y)
    by_cases hlt : x i < x j
    · rw [ite_eq_left hlt, ite_eq_left (hroot.mp hlt)]
      exact ihl fun a b hab => h a b (by
        rw [comparedPairs_node, ite_eq_left hlt]
        exact Finset.mem_insert_of_mem hab)
    · rw [ite_eq_right hlt, ite_eq_right (fun hc => hlt (hroot.mpr hc))]
      exact ihr fun a b hab => h a b (by
        rw [comparedPairs_node, ite_eq_right hlt]
        exact Finset.mem_insert_of_mem hab)

end SortBounds.Projects.BestCase
