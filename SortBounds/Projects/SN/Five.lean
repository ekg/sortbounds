/-
SortBounds/Projects/SN/Five.lean

`S 5 = 7`: seven comparisons sort five elements, and counting forbids fewer
(`⌈log₂ 5!⌉ = ⌈log₂ 120⌉ = 7`).

A *network* does not give this upper bound: the smallest sorting network on five
wires has nine comparators (a classical fact, not formalised here), so seven
comparisons require an *adaptive* tree.  `tree5` below is one; `Four.lean` is the
contrast — there the optimal tree is a network folded into a tree by `netTree`.

How `tree5` was found: by an exhaustive search over *knowledge states*.  A state
is the set of orderings of the five positions still consistent with the answers
received so far; a comparison splits a state in two, and a leaf is a state with
one ordering left.  The run that produced this tree explored 239 states, so the
skeleton is small — but the search itself is *not* formalised.  Everything that
matters is checked in the kernel:

* `tree5_depth`: the depth is `7`;
* `tree5_numLeaves`: the tree has `120` leaves, as many as there are orderings;
* `tree5_correct`: it sorts every input — `correct_of_forall_run_xOfPerm` reduces
  this to the `5! = 120` canonical inputs, and `decide` checks those.

Every internal node is annotated with the number of orderings consistent with the
answers that reach it, so a reader can check without redoing the search that the
two children of a node add up to the node's own count (neither child is empty),
that the counts fall `120 → 60 → 30 → 15 → 8/7 → … → 1` as evenly as the counting
bound allows, and that each of the `120` leaves has exactly one ordering left.
A leaf carries that ordering as the permutation to output, written as a product of
transpositions: `swapProd [(0, 1), (1, 2)]` is `Equiv.swap 0 1 * Equiv.swap 1 2`,
which maps `0 ↦ 1 ↦ 2 ↦ 0`; the identity is written `1`.
-/
import SortBounds.Projects.SN.Verify
import SortBounds.Projects.SN.Basic

namespace SortBounds.Projects.SN

open SortBounds

/-- A `7`-comparison decision tree sorting five positions.  A node
`.node i j l r` compares positions `i` and `j`: `l` is taken when `x i < x j`,
`r` otherwise. -/
def tree5 : Tree 5 :=
  (.node 0 1   -- 120
    (.node 2 3   -- 60
      (.node 0 2   -- 30
        (.node 2 4   -- 15
          (.node 3 4   -- 8
            (.node 1 3   -- 4
              (.node 1 2   -- 2
                (Tree.leaf 1)
                (Tree.leaf (swapProd [(1, 2)])))
              (.node 1 4   -- 2
                (Tree.leaf (swapProd [(1, 2), (2, 3)]))
                (Tree.leaf (swapProd [(1, 2), (2, 3), (3, 4)]))))
            (.node 1 4   -- 4
              (.node 1 2   -- 2
                (Tree.leaf (swapProd [(3, 4)]))
                (Tree.leaf (swapProd [(1, 2), (3, 4)])))
              (.node 1 3   -- 2
                (Tree.leaf (swapProd [(1, 2), (2, 4), (4, 3)]))
                (Tree.leaf (swapProd [(1, 2), (2, 4)])))))
          (.node 0 4   -- 7
            (.node 1 2   -- 4
              (.node 1 4   -- 2
                (Tree.leaf (swapProd [(2, 4), (4, 3)]))
                (Tree.leaf (swapProd [(1, 4), (4, 3), (3, 2)])))
              (.node 3 1   -- 2
                (Tree.leaf (swapProd [(1, 4)]))
                (Tree.leaf (swapProd [(1, 4), (4, 3)]))))
            (.node 1 3   -- 3
              (.node 1 2   -- 2
                (Tree.leaf (swapProd [(0, 4), (4, 3), (3, 2), (2, 1)]))
                (Tree.leaf (swapProd [(0, 4), (4, 3), (3, 1)])))
              (Tree.leaf (swapProd [(0, 4), (4, 1)])))))
        (.node 0 4   -- 15
          (.node 1 4   -- 8
            (.node 1 3   -- 4
              (.node 3 4   -- 2
                (Tree.leaf (swapProd [(0, 2), (2, 1)]))
                (Tree.leaf (swapProd [(0, 2), (2, 1), (3, 4)])))
              (.node 3 0   -- 2
                (Tree.leaf (swapProd [(0, 2), (1, 3)]))
                (Tree.leaf (swapProd [(0, 2), (2, 3), (3, 1)]))))
            (.node 4 3   -- 4
              (.node 3 1   -- 2
                (Tree.leaf (swapProd [(0, 2), (2, 4), (4, 1)]))
                (Tree.leaf (swapProd [(0, 2), (2, 4), (4, 3), (3, 1)])))
              (.node 3 0   -- 2
                (Tree.leaf (swapProd [(0, 2), (1, 3), (3, 4)]))
                (Tree.leaf (swapProd [(0, 2), (2, 3), (3, 4), (4, 1)])))))
          (.node 2 4   -- 7
            (.node 3 0   -- 4
              (.node 4 3   -- 2
                (Tree.leaf (swapProd [(0, 2), (2, 3), (1, 4)]))
                (Tree.leaf (swapProd [(0, 2), (2, 4), (4, 1), (1, 3)])))
              (.node 1 3   -- 2
                (Tree.leaf (swapProd [(0, 2), (1, 4), (4, 3)]))
                (Tree.leaf (swapProd [(0, 2), (1, 4)]))))
            (.node 1 3   -- 3
              (Tree.leaf (swapProd [(0, 4), (4, 3), (3, 1), (1, 2)]))
              (.node 3 0   -- 2
                (Tree.leaf (swapProd [(0, 4), (4, 1), (1, 2), (2, 3)]))
                (Tree.leaf (swapProd [(0, 4), (4, 1), (1, 2)])))))))
      (.node 0 3   -- 30
        (.node 3 4   -- 15
          (.node 2 4   -- 8
            (.node 1 2   -- 4
              (.node 1 3   -- 2
                (Tree.leaf (swapProd [(2, 3)]))
                (Tree.leaf (swapProd [(1, 3), (3, 2)])))
              (.node 1 4   -- 2
                (Tree.leaf (swapProd [(1, 3)]))
                (Tree.leaf (swapProd [(1, 3), (3, 4)]))))
            (.node 1 4   -- 4
              (.node 1 3   -- 2
                (Tree.leaf (swapProd [(2, 3), (3, 4)]))
                (Tree.leaf (swapProd [(1, 3), (3, 4), (4, 2)])))
              (.node 1 2   -- 2
                (Tree.leaf (swapProd [(1, 3), (2, 4)]))
                (Tree.leaf (swapProd [(1, 3), (3, 2), (2, 4)])))))
          (.node 0 4   -- 7
            (.node 1 3   -- 4
              (.node 1 4   -- 2
                (Tree.leaf (swapProd [(2, 4)]))
                (Tree.leaf (swapProd [(1, 4), (4, 2)])))
              (.node 2 1   -- 2
                (Tree.leaf (swapProd [(1, 4), (2, 3)]))
                (Tree.leaf (swapProd [(1, 4), (4, 2), (2, 3)]))))
            (.node 1 2   -- 3
              (.node 1 3   -- 2
                (Tree.leaf (swapProd [(0, 4), (4, 2), (2, 1)]))
                (Tree.leaf (swapProd [(0, 4), (4, 2), (2, 3), (3, 1)])))
              (Tree.leaf (swapProd [(0, 4), (4, 1), (2, 3)])))))
        (.node 0 4   -- 15
          (.node 1 4   -- 8
            (.node 1 2   -- 4
              (.node 2 4   -- 2
                (Tree.leaf (swapProd [(0, 3), (3, 2), (2, 1)]))
                (Tree.leaf (swapProd [(0, 3), (3, 4), (4, 2), (2, 1)])))
              (.node 2 0   -- 2
                (Tree.leaf (swapProd [(0, 3), (3, 1), (1, 2)]))
                (Tree.leaf (swapProd [(0, 3), (3, 1)]))))
            (.node 4 2   -- 4
              (.node 2 1   -- 2
                (Tree.leaf (swapProd [(0, 3), (3, 2), (2, 4), (4, 1)]))
                (Tree.leaf (swapProd [(0, 3), (3, 1), (2, 4)])))
              (.node 2 0   -- 2
                (Tree.leaf (swapProd [(0, 3), (3, 4), (4, 1), (1, 2)]))
                (Tree.leaf (swapProd [(0, 3), (3, 4), (4, 1)])))))
          (.node 3 4   -- 7
            (.node 2 0   -- 4
              (.node 4 2   -- 2
                (Tree.leaf (swapProd [(0, 3), (1, 4)]))
                (Tree.leaf (swapProd [(0, 3), (1, 2), (2, 4)])))
              (.node 1 2   -- 2
                (Tree.leaf (swapProd [(0, 3), (3, 1), (1, 4), (4, 2)]))
                (Tree.leaf (swapProd [(0, 3), (3, 2), (1, 4)]))))
            (.node 1 2   -- 3
              (Tree.leaf (swapProd [(0, 4), (4, 2), (1, 3)]))
              (.node 2 0   -- 2
                (Tree.leaf (swapProd [(0, 4), (4, 1), (1, 3)]))
                (Tree.leaf (swapProd [(0, 4), (4, 1), (1, 3), (3, 2)]))))))))
    (.node 2 3   -- 60
      (.node 1 2   -- 30
        (.node 2 4   -- 15
          (.node 3 4   -- 8
            (.node 0 3   -- 4
              (.node 0 2   -- 2
                (Tree.leaf (swapProd [(0, 1)]))
                (Tree.leaf (swapProd [(0, 1), (1, 2)])))
              (.node 0 4   -- 2
                (Tree.leaf (swapProd [(0, 1), (1, 2), (2, 3)]))
                (Tree.leaf (swapProd [(0, 1), (1, 2), (2, 3), (3, 4)]))))
            (.node 0 4   -- 4
              (.node 0 2   -- 2
                (Tree.leaf (swapProd [(0, 1), (3, 4)]))
                (Tree.leaf (swapProd [(0, 1), (1, 2), (3, 4)])))
              (.node 0 3   -- 2
                (Tree.leaf (swapProd [(0, 1), (1, 2), (2, 4), (4, 3)]))
                (Tree.leaf (swapProd [(0, 1), (1, 2), (2, 4)])))))
          (.node 1 4   -- 7
            (.node 0 2   -- 4
              (.node 0 4   -- 2
                (Tree.leaf (swapProd [(0, 1), (2, 4), (4, 3)]))
                (Tree.leaf (swapProd [(0, 1), (1, 4), (4, 3), (3, 2)])))
              (.node 3 0   -- 2
                (Tree.leaf (swapProd [(0, 1), (1, 4)]))
                (Tree.leaf (swapProd [(0, 1), (1, 4), (4, 3)]))))
            (.node 0 3   -- 3
              (.node 0 2   -- 2
                (Tree.leaf (swapProd [(0, 4), (4, 3), (3, 2)]))
                (Tree.leaf (swapProd [(0, 4), (4, 3)])))
              (Tree.leaf (swapProd [(0, 4)])))))
        (.node 1 4   -- 15
          (.node 0 4   -- 8
            (.node 0 3   -- 4
              (.node 3 4   -- 2
                (Tree.leaf (swapProd [(0, 2)]))
                (Tree.leaf (swapProd [(0, 2), (3, 4)])))
              (.node 3 1   -- 2
                (Tree.leaf (swapProd [(0, 2), (2, 1), (1, 3)]))
                (Tree.leaf (swapProd [(0, 2), (2, 3)]))))
            (.node 4 3   -- 4
              (.node 3 0   -- 2
                (Tree.leaf (swapProd [(0, 2), (2, 4)]))
                (Tree.leaf (swapProd [(0, 2), (2, 4), (4, 3)])))
              (.node 3 1   -- 2
                (Tree.leaf (swapProd [(0, 2), (2, 1), (1, 3), (3, 4)]))
                (Tree.leaf (swapProd [(0, 2), (2, 3), (3, 4)])))))
          (.node 2 4   -- 7
            (.node 3 1   -- 4
              (.node 4 3   -- 2
                (Tree.leaf (swapProd [(0, 2), (2, 3), (3, 1), (1, 4)]))
                (Tree.leaf (swapProd [(0, 2), (2, 4), (1, 3)])))
              (.node 0 3   -- 2
                (Tree.leaf (swapProd [(0, 2), (2, 1), (1, 4), (4, 3)]))
                (Tree.leaf (swapProd [(0, 2), (2, 1), (1, 4)]))))
            (.node 0 3   -- 3
              (Tree.leaf (swapProd [(0, 4), (4, 3), (1, 2)]))
              (.node 3 1   -- 2
                (Tree.leaf (swapProd [(0, 4), (1, 2), (2, 3)]))
                (Tree.leaf (swapProd [(0, 4), (1, 2)])))))))
      (.node 1 3   -- 30
        (.node 3 4   -- 15
          (.node 2 4   -- 8
            (.node 0 2   -- 4
              (.node 0 3   -- 2
                (Tree.leaf (swapProd [(0, 1), (2, 3)]))
                (Tree.leaf (swapProd [(0, 1), (1, 3), (3, 2)])))
              (.node 0 4   -- 2
                (Tree.leaf (swapProd [(0, 1), (1, 3)]))
                (Tree.leaf (swapProd [(0, 1), (1, 3), (3, 4)]))))
            (.node 0 4   -- 4
              (.node 0 3   -- 2
                (Tree.leaf (swapProd [(0, 1), (2, 3), (3, 4)]))
                (Tree.leaf (swapProd [(0, 1), (1, 3), (3, 4), (4, 2)])))
              (.node 0 2   -- 2
                (Tree.leaf (swapProd [(0, 1), (1, 3), (2, 4)]))
                (Tree.leaf (swapProd [(0, 1), (1, 3), (3, 2), (2, 4)])))))
          (.node 1 4   -- 7
            (.node 0 3   -- 4
              (.node 0 4   -- 2
                (Tree.leaf (swapProd [(0, 1), (2, 4)]))
                (Tree.leaf (swapProd [(0, 1), (1, 4), (4, 2)])))
              (.node 2 0   -- 2
                (Tree.leaf (swapProd [(0, 1), (1, 4), (2, 3)]))
                (Tree.leaf (swapProd [(0, 1), (1, 4), (4, 2), (2, 3)]))))
            (.node 0 2   -- 3
              (.node 0 3   -- 2
                (Tree.leaf (swapProd [(0, 4), (4, 2)]))
                (Tree.leaf (swapProd [(0, 4), (4, 2), (2, 3)])))
              (Tree.leaf (swapProd [(0, 4), (2, 3)])))))
        (.node 1 4   -- 15
          (.node 0 4   -- 8
            (.node 0 2   -- 4
              (.node 2 4   -- 2
                (Tree.leaf (swapProd [(0, 3), (3, 2)]))
                (Tree.leaf (swapProd [(0, 3), (3, 4), (4, 2)])))
              (.node 2 1   -- 2
                (Tree.leaf (swapProd [(0, 3), (1, 2)]))
                (Tree.leaf (swapProd [(0, 3)]))))
            (.node 4 2   -- 4
              (.node 2 0   -- 2
                (Tree.leaf (swapProd [(0, 3), (3, 2), (2, 4)]))
                (Tree.leaf (swapProd [(0, 3), (2, 4)])))
              (.node 2 1   -- 2
                (Tree.leaf (swapProd [(0, 3), (3, 4), (1, 2)]))
                (Tree.leaf (swapProd [(0, 3), (3, 4)])))))
          (.node 3 4   -- 7
            (.node 2 1   -- 4
              (.node 4 2   -- 2
                (Tree.leaf (swapProd [(0, 3), (3, 1), (1, 4)]))
                (Tree.leaf (swapProd [(0, 3), (3, 1), (1, 2), (2, 4)])))
              (.node 0 2   -- 2
                (Tree.leaf (swapProd [(0, 3), (1, 4), (4, 2)]))
                (Tree.leaf (swapProd [(0, 3), (3, 2), (2, 1), (1, 4)]))))
            (.node 0 2   -- 3
              (Tree.leaf (swapProd [(0, 4), (4, 2), (2, 1), (1, 3)]))
              (.node 2 1   -- 2
                (Tree.leaf (swapProd [(0, 4), (1, 3)]))
                (Tree.leaf (swapProd [(0, 4), (1, 3), (3, 2)])))))))))

/-- Every leaf of `tree5` is at depth `6` or `7`. -/
theorem tree5_depth : depth tree5 = 7 := by decide

/-- As many leaves as there are orderings of five elements. -/
theorem tree5_numLeaves : numLeaves tree5 = 120 := by decide

-- `decide` enumerates `Equiv.Perm (Fin 5)`, and that `Fintype` instance filters
-- the `5 ^ 5 = 3125` functions `Fin 5 → Fin 5`, deeper than the default
-- elaborator recursion limit of 1000.
set_option maxRecDepth 2000 in
/-- The tree sorts: on all `5! = 120` canonical inputs it outputs the sorting
permutation, hence on every input with distinct values. -/
theorem tree5_correct : Correct (α := ℕ) tree5 :=
  correct_of_forall_run_xOfPerm (by decide)

/-- **`S 5 = 7`**: seven comparisons sort five elements, and counting rules out
six. -/
theorem S_five : S 5 = 7 := by
  refine le_antisymm ?_ ?_
  · -- upper bound: the adaptive tree
    refine (S_le_iff 5 7).2 ⟨tree5, tree5_correct, ?_⟩
    rw [tree5_depth]
  · -- lower bound: `Nat.clog 2 5! = 7`
    have h := S_lower 5
    have h120 : Nat.clog 2 (Nat.factorial 5) = 7 := by decide
    omega

end SortBounds.Projects.SN
