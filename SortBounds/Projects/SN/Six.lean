/-
SortBounds/Projects/SN/Six.lean

`S 6 = 10`: ten comparisons sort six elements, and counting forbids fewer
(`⌈log₂ 6!⌉ = ⌈log₂ 720⌉ = 10`).

No *network* gives this bound: the smallest sorting network on six wires has
twelve comparators (a classical fact, not formalised here), so ten comparisons
require an *adaptive* tree, exactly as for `n = 5` (`Five.lean`).  `tree6` below
is such a tree: depth `10` with `720 = 6!` leaves.

How `tree6` was found: the same exhaustive search over *knowledge states* that
produced `tree5` (`Five.lean`), run by `search_optimal_tree.py` in this directory,
which prints the literal below.  A state is the set of orderings of the six
positions still consistent with the answers received so far, a comparison splits
a state in two, and a leaf is a state with one ordering left.  The search itself
is *not* formalised; everything that matters is checked in the kernel:

* `tree6_depth`: the depth is `10`;
* `tree6_numLeaves`: the tree has `720` leaves — exactly the counting bound for a
  correct tree on six positions (`factorial_le_numLeaves`), so there is no slack;
* `tree6_correct`: it sorts every `ℕ`-valued input with pairwise distinct values —
  `correct_of_allPerms` reduces this to the `6! = 720` canonical inputs and has
  `decide` check those.

Every internal node is annotated with the number of orderings consistent with the
answers that reach it, so a reader can check without redoing the search that the
two children of a node add up to the node's own count, and that no subtree asks
for more comparisons than its own count allows (`#orderings ≤ 2 ^ remaining
depth`).  Along the leftmost path the counts read
`720 → 360 → 180 → 90 → 45 → 26 → 12 → 6 → 3 → 1`, and their first four splits
are exactly even (`720 = 2·360`, `360 = 2·180`, `180 = 2·90`, `90 = 2·45`), while
`45` splits as `26 + 19`.

A leaf carries its ordering as the permutation to output, written as a product of
transpositions: `swapProd [(0, 1), (1, 2)]` is `Equiv.swap 0 1 * Equiv.swap 1 2`,
which sends `0 ↦ 1 ↦ 2 ↦ 0`; the identity is written `1`.
-/
import SortBounds.Projects.SN.Verify
import SortBounds.Projects.SN.Basic
import SortBounds.Comparison.LowerBound

namespace SortBounds.Projects.SN

open SortBounds

/-- A `10`-comparison decision tree sorting six positions.  A node
`.node i j l r` compares positions `i` and `j`: `l` is taken when `x i < x j`,
`r` otherwise.  The comment on each internal node is the number of orderings of
the six positions consistent with the answers that lead to it. -/
def tree6 : Tree 6 :=
  (.node 0 1   -- 720
    (.node 2 3   -- 360
      (.node 0 2   -- 180
        (.node 4 5   -- 90
          (.node 1 5   -- 45
            (.node 1 2   -- 26
              (.node 1 4   -- 12
                (.node 2 4   -- 6
                  (.node 3 4   -- 3
                    (.leaf 1)
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(3, 4)]))
                      (.leaf (swapProd [(3, 5), (3, 4)]))
                    )
                  )
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(2, 3), (2, 4)]))
                      (.leaf (swapProd [(2, 3), (2, 5), (2, 4)]))
                    )
                    (.leaf (swapProd [(2, 4), (3, 5)]))
                  )
                )
                (.node 0 4   -- 6
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 2), (1, 3), (1, 4)]))
                      (.leaf (swapProd [(1, 2), (1, 3), (1, 5), (1, 4)]))
                    )
                    (.leaf (swapProd [(1, 2), (1, 4), (3, 5)]))
                  )
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 4)]))
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 5), (0, 4)]))
                    )
                    (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (3, 5)]))
                  )
                )
              )
              (.node 2 4   -- 14
                (.node 1 4   -- 8
                  (.node 3 4   -- 4
                    (.node 1 3   -- 2
                      (.leaf (swapProd [(1, 2)]))
                      (.leaf (swapProd [(1, 3), (1, 2)]))
                    )
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 2), (3, 4)]))
                      (.leaf (swapProd [(1, 2), (3, 5), (3, 4)]))
                    )
                  )
                  (.node 1 3   -- 4
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 3), (1, 4), (1, 2)]))
                      (.leaf (swapProd [(1, 3), (1, 5), (1, 4), (1, 2)]))
                    )
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(1, 4), (1, 3), (1, 2)]))
                      (.leaf (swapProd [(1, 4), (1, 2)]))
                    )
                  )
                )
                (.node 0 4   -- 6
                  (.node 1 3   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 3), (1, 4)]))
                      (.leaf (swapProd [(1, 3), (1, 5), (1, 4)]))
                    )
                    (.leaf (swapProd [(1, 4)]))
                  )
                  (.node 1 3   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 3), (0, 4)]))
                      (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 4)]))
                    )
                    (.leaf (swapProd [(0, 1), (0, 4)]))
                  )
                )
              )
            )
            (.node 0 4   -- 19
              (.node 1 3   -- 10
                (.node 2 5   -- 4
                  (.node 2 4   -- 2
                    (.leaf (swapProd [(1, 4), (1, 2), (3, 5)]))
                    (.leaf (swapProd [(1, 4), (3, 5)]))
                  )
                  (.node 1 2   -- 2
                    (.leaf (swapProd [(1, 3), (1, 5), (1, 2), (1, 4)]))
                    (.leaf (swapProd [(1, 4), (2, 3), (2, 5)]))
                  )
                )
                (.node 2 4   -- 6
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(1, 5), (1, 4), (1, 3), (1, 2)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 5), (1, 4), (1, 2)]))
                      (.leaf (swapProd [(1, 5), (1, 3), (1, 4), (1, 2)]))
                    )
                  )
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 5), (1, 4)]))
                      (.leaf (swapProd [(1, 5), (1, 3), (1, 4)]))
                    )
                    (.leaf (swapProd [(1, 5), (1, 2), (1, 3), (1, 4)]))
                  )
                )
              )
              (.node 1 3   -- 9
                (.node 0 5   -- 5
                  (.node 1 2   -- 3
                    (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 2), (0, 4)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 4), (3, 5)]))
                      (.leaf (swapProd [(0, 1), (0, 4), (2, 3), (2, 5)]))
                    )
                  )
                  (.node 1 2   -- 2
                    (.leaf (swapProd [(0, 2), (0, 4), (1, 3), (1, 5)]))
                    (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 1), (0, 4)]))
                  )
                )
                (.node 2 5   -- 4
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 1), (0, 5), (0, 4)]))
                    (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 4)]))
                  )
                  (.node 0 5   -- 2
                    (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 3), (0, 4)]))
                    (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (1, 5)]))
                  )
                )
              )
            )
          )
          (.node 1 4   -- 45
            (.node 1 2   -- 26
              (.node 1 5   -- 12
                (.node 2 5   -- 6
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(4, 5)]))
                      (.leaf (swapProd [(3, 4), (3, 5)]))
                    )
                    (.leaf (swapProd [(3, 5)]))
                  )
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(2, 3), (2, 4), (2, 5)]))
                      (.leaf (swapProd [(2, 3), (2, 5)]))
                    )
                    (.leaf (swapProd [(2, 4), (2, 3), (2, 5)]))
                  )
                )
                (.node 0 5   -- 6
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(1, 2), (1, 3), (1, 4), (1, 5)]))
                      (.leaf (swapProd [(1, 2), (1, 3), (1, 5)]))
                    )
                    (.leaf (swapProd [(1, 2), (1, 4), (1, 3), (1, 5)]))
                  )
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]))
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 5)]))
                    )
                    (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 3), (0, 5)]))
                  )
                )
              )
              (.node 2 5   -- 14
                (.node 1 5   -- 8
                  (.node 3 5   -- 4
                    (.node 1 3   -- 2
                      (.leaf (swapProd [(1, 2), (4, 5)]))
                      (.leaf (swapProd [(1, 3), (1, 2), (4, 5)]))
                    )
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(1, 2), (3, 4), (3, 5)]))
                      (.leaf (swapProd [(1, 2), (3, 5)]))
                    )
                  )
                  (.node 1 3   -- 4
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(1, 3), (1, 4), (1, 5), (1, 2)]))
                      (.leaf (swapProd [(1, 3), (1, 5), (1, 2)]))
                    )
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 4), (1, 5), (1, 3), (1, 2)]))
                      (.leaf (swapProd [(1, 4), (1, 5), (1, 2)]))
                    )
                  )
                )
                (.node 0 5   -- 6
                  (.node 1 3   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(1, 3), (1, 4), (1, 5)]))
                      (.leaf (swapProd [(1, 3), (1, 5)]))
                    )
                    (.leaf (swapProd [(1, 4), (1, 5)]))
                  )
                  (.node 1 3   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 5)]))
                      (.leaf (swapProd [(0, 1), (0, 3), (0, 5)]))
                    )
                    (.leaf (swapProd [(0, 1), (0, 4), (0, 5)]))
                  )
                )
              )
            )
            (.node 0 5   -- 19
              (.node 1 3   -- 10
                (.node 2 4   -- 4
                  (.node 2 5   -- 2
                    (.leaf (swapProd [(1, 4), (1, 3), (1, 5), (1, 2)]))
                    (.leaf (swapProd [(1, 4), (1, 3), (1, 5)]))
                  )
                  (.node 1 2   -- 2
                    (.leaf (swapProd [(1, 3), (1, 5), (2, 4)]))
                    (.leaf (swapProd [(1, 4), (1, 2), (1, 3), (1, 5)]))
                  )
                )
                (.node 2 5   -- 6
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 5), (1, 3), (1, 2)]))
                      (.leaf (swapProd [(1, 5), (1, 2)]))
                    )
                    (.leaf (swapProd [(1, 5), (1, 2), (3, 4)]))
                  )
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(1, 5)]))
                      (.leaf (swapProd [(1, 5), (3, 4)]))
                    )
                    (.leaf (swapProd [(1, 5), (2, 3), (2, 4)]))
                  )
                )
              )
              (.node 1 3   -- 9
                (.node 0 4   -- 5
                  (.node 1 2   -- 3
                    (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (2, 4)]))
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 5)]))
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 3), (0, 5)]))
                    )
                  )
                  (.node 1 2   -- 2
                    (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 3), (0, 5)]))
                    (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (1, 4)]))
                  )
                )
                (.node 2 4   -- 4
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 1), (0, 5)]))
                    (.leaf (swapProd [(0, 1), (0, 5), (3, 4)]))
                  )
                  (.node 0 4   -- 2
                    (.leaf (swapProd [(0, 1), (0, 5), (2, 3), (2, 4)]))
                    (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 1), (0, 5)]))
                  )
                )
              )
            )
          )
        )
        (.node 4 5   -- 90
          (.node 1 5   -- 45
            (.node 0 4   -- 19
              (.node 1 3   -- 10
                (.node 1 4   -- 5
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 1), (0, 2)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 2), (3, 4)]))
                      (.leaf (swapProd [(0, 1), (0, 2), (3, 5), (3, 4)]))
                    )
                  )
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 2)]))
                    (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 4), (0, 2)]))
                  )
                )
                (.node 0 3   -- 5
                  (.node 1 4   -- 3
                    (.leaf (swapProd [(0, 1), (0, 3), (0, 2)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 2)]))
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 2)]))
                    )
                  )
                  (.node 1 4   -- 2
                    (.leaf (swapProd [(0, 2), (1, 3)]))
                    (.leaf (swapProd [(0, 2), (1, 4), (1, 3)]))
                  )
                )
              )
              (.node 1 3   -- 9
                (.node 2 4   -- 4
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 2), (1, 3), (1, 4)]))
                    (.leaf (swapProd [(0, 2), (1, 3), (1, 5), (1, 4)]))
                  )
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 4)]))
                    (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 5), (0, 4)]))
                  )
                )
                (.node 0 3   -- 5
                  (.node 2 4   -- 2
                    (.leaf (swapProd [(0, 2), (1, 4)]))
                    (.leaf (swapProd [(0, 2), (0, 1), (0, 4)]))
                  )
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 2)]))
                      (.leaf (swapProd [(0, 3), (0, 2), (1, 4)]))
                    )
                    (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 4)]))
                  )
                )
              )
            )
            (.node 0 5   -- 26
              (.node 3 5   -- 14
                (.node 0 3   -- 8
                  (.node 0 4   -- 4
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 3), (0, 2)]))
                      (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 2)]))
                    )
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 2), (1, 5), (1, 4)]))
                      (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 4)]))
                    )
                  )
                  (.node 3 4   -- 4
                    (.node 0 4   -- 2
                      (.leaf (swapProd [(0, 2), (1, 5), (1, 4), (1, 3)]))
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 4), (0, 2)]))
                    )
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 3), (0, 2), (1, 5), (1, 4)]))
                      (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 5), (0, 4)]))
                    )
                  )
                )
                (.node 1 3   -- 6
                  (.node 0 4   -- 3
                    (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (3, 5)]))
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 2), (1, 4), (3, 5)]))
                      (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (3, 5)]))
                    )
                  )
                  (.node 0 4   -- 3
                    (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 4), (0, 2)]))
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 2), (1, 5), (1, 3), (1, 4)]))
                      (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 3), (0, 4)]))
                    )
                  )
                )
              )
              (.node 0 3   -- 12
                (.node 1 3   -- 6
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (1, 4)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 1), (0, 4)]))
                      (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 4)]))
                    )
                  )
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 5), (0, 2)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 4), (1, 5), (1, 2)]))
                      (.leaf (swapProd [(0, 3), (0, 4), (1, 5)]))
                    )
                  )
                )
                (.node 2 4   -- 6
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 4), (0, 2), (1, 5), (1, 3)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 3), (0, 2)]))
                      (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 2)]))
                    )
                  )
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (1, 5), (1, 3), (1, 2)]))
                      (.leaf (swapProd [(0, 4), (1, 5), (1, 2)]))
                    )
                    (.leaf (swapProd [(0, 4), (1, 5)]))
                  )
                )
              )
            )
          )
          (.node 1 4   -- 45
            (.node 0 5   -- 19
              (.node 1 3   -- 10
                (.node 1 5   -- 5
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 2), (4, 5)]))
                      (.leaf (swapProd [(0, 1), (0, 2), (3, 4), (3, 5)]))
                    )
                    (.leaf (swapProd [(0, 1), (0, 2), (3, 5)]))
                  )
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 5), (0, 2)]))
                    (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 2)]))
                  )
                )
                (.node 0 3   -- 5
                  (.node 1 5   -- 3
                    (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (4, 5)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 3), (0, 2)]))
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 2)]))
                    )
                  )
                  (.node 1 5   -- 2
                    (.leaf (swapProd [(0, 2), (1, 3), (4, 5)]))
                    (.leaf (swapProd [(0, 2), (1, 4), (1, 5), (1, 3)]))
                  )
                )
              )
              (.node 1 3   -- 9
                (.node 2 5   -- 4
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 2), (1, 3), (1, 4), (1, 5)]))
                    (.leaf (swapProd [(0, 2), (1, 3), (1, 5)]))
                  )
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 4), (0, 5)]))
                    (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 5)]))
                  )
                )
                (.node 0 3   -- 5
                  (.node 2 5   -- 2
                    (.leaf (swapProd [(0, 2), (1, 4), (1, 5)]))
                    (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 5)]))
                  )
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 5), (0, 2)]))
                      (.leaf (swapProd [(0, 3), (0, 2), (1, 4), (1, 5)]))
                    )
                    (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 4), (0, 5)]))
                  )
                )
              )
            )
            (.node 0 4   -- 26
              (.node 3 4   -- 14
                (.node 0 3   -- 8
                  (.node 0 5   -- 4
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 2)]))
                      (.leaf (swapProd [(0, 1), (0, 5), (0, 2)]))
                    )
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 2), (1, 5)]))
                      (.leaf (swapProd [(0, 2), (0, 1), (0, 5)]))
                    )
                  )
                  (.node 3 5   -- 4
                    (.node 0 5   -- 2
                      (.leaf (swapProd [(0, 2), (1, 5), (1, 3)]))
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 2)]))
                    )
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 2), (1, 5)]))
                      (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 5)]))
                    )
                  )
                )
                (.node 1 3   -- 6
                  (.node 0 5   -- 3
                    (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 5), (0, 2)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 2), (1, 4), (1, 3), (1, 5)]))
                      (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 3), (0, 5)]))
                    )
                  )
                  (.node 0 5   -- 3
                    (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (3, 4)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 2), (1, 5), (3, 4)]))
                      (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (3, 4)]))
                    )
                  )
                )
              )
              (.node 0 3   -- 12
                (.node 1 3   -- 6
                  (.node 2 4   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 4), (0, 2)]))
                      (.leaf (swapProd [(0, 3), (0, 5), (1, 4), (1, 2)]))
                    )
                    (.leaf (swapProd [(0, 3), (0, 5), (1, 4)]))
                  )
                  (.node 2 4   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (1, 5)]))
                      (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 1), (0, 5)]))
                    )
                    (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 5)]))
                  )
                )
                (.node 2 5   -- 6
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 5), (0, 2)]))
                      (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (1, 5)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 2), (1, 5)]))
                  )
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 1), (0, 5)]))
                      (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 5)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 1), (0, 5)]))
                  )
                )
              )
            )
          )
        )
      )
      (.node 0 3   -- 180
        (.node 4 5   -- 90
          (.node 1 5   -- 45
            (.node 1 3   -- 26
              (.node 1 4   -- 12
                (.node 2 5   -- 6
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(2, 3)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(2, 4), (2, 3)]))
                      (.leaf (swapProd [(2, 4)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(2, 5), (2, 4), (2, 3)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(2, 5), (2, 4)]))
                      (.leaf (swapProd [(2, 5), (2, 3), (2, 4)]))
                    )
                  )
                )
                (.node 0 4   -- 6
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(1, 2), (1, 4)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 2), (1, 5), (1, 4)]))
                      (.leaf (swapProd [(1, 2), (1, 5), (1, 3), (1, 4)]))
                    )
                  )
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(0, 1), (0, 2), (0, 4)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 4)]))
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 3), (0, 4)]))
                    )
                  )
                )
              )
              (.node 3 4   -- 14
                (.node 1 4   -- 8
                  (.node 2 4   -- 4
                    (.node 1 2   -- 2
                      (.leaf (swapProd [(1, 2), (1, 3)]))
                      (.leaf (swapProd [(1, 3)]))
                    )
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(1, 2), (1, 4), (1, 3)]))
                      (.leaf (swapProd [(1, 2), (1, 5), (1, 4), (1, 3)]))
                    )
                  )
                  (.node 1 2   -- 4
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(1, 3), (2, 4)]))
                      (.leaf (swapProd [(1, 3), (2, 5), (2, 4)]))
                    )
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(1, 4), (1, 3)]))
                      (.leaf (swapProd [(1, 4), (1, 2), (1, 3)]))
                    )
                  )
                )
                (.node 0 4   -- 6
                  (.node 1 2   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(1, 3), (1, 2), (1, 4)]))
                      (.leaf (swapProd [(1, 3), (1, 2), (1, 5), (1, 4)]))
                    )
                    (.leaf (swapProd [(1, 4), (2, 3)]))
                  )
                  (.node 1 2   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 4)]))
                      (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 5), (0, 4)]))
                    )
                    (.leaf (swapProd [(0, 1), (0, 4), (2, 3)]))
                  )
                )
              )
            )
            (.node 0 4   -- 19
              (.node 1 2   -- 10
                (.node 3 5   -- 4
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(1, 4), (1, 2), (1, 5), (1, 3)]))
                    (.leaf (swapProd [(1, 4), (2, 5), (2, 3)]))
                  )
                  (.node 1 3   -- 2
                    (.leaf (swapProd [(1, 3), (1, 4), (2, 5)]))
                    (.leaf (swapProd [(1, 4), (2, 5)]))
                  )
                )
                (.node 2 5   -- 6
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(1, 5), (1, 4), (1, 3)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(1, 5), (1, 4), (1, 2), (1, 3)]))
                      (.leaf (swapProd [(1, 5), (1, 4), (2, 3)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(1, 5), (1, 3), (2, 4)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 5), (1, 3), (1, 2), (1, 4)]))
                      (.leaf (swapProd [(1, 5), (1, 2), (1, 4)]))
                    )
                  )
                )
              )
              (.node 1 2   -- 9
                (.node 0 5   -- 5
                  (.node 1 3   -- 3
                    (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (2, 5)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 4), (2, 5), (2, 3)]))
                      (.leaf (swapProd [(0, 1), (0, 4), (2, 5)]))
                    )
                  )
                  (.node 1 3   -- 2
                    (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 3), (0, 4)]))
                    (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 4)]))
                  )
                )
                (.node 3 5   -- 4
                  (.node 2 5   -- 2
                    (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (2, 3)]))
                    (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 2), (0, 4)]))
                  )
                  (.node 0 5   -- 2
                    (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 4)]))
                    (.leaf (swapProd [(0, 2), (0, 4), (1, 5)]))
                  )
                )
              )
            )
          )
          (.node 1 4   -- 45
            (.node 1 3   -- 26
              (.node 1 5   -- 12
                (.node 2 4   -- 6
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(2, 3), (4, 5)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(2, 4), (2, 5), (2, 3)]))
                      (.leaf (swapProd [(2, 4), (2, 5)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(2, 5), (2, 3)]))
                      (.leaf (swapProd [(2, 5)]))
                    )
                    (.leaf (swapProd [(2, 5), (3, 4)]))
                  )
                )
                (.node 0 5   -- 6
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(1, 2), (1, 4), (1, 5)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(1, 2), (1, 5)]))
                      (.leaf (swapProd [(1, 2), (1, 5), (3, 4)]))
                    )
                  )
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 5)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 5)]))
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (3, 4)]))
                    )
                  )
                )
              )
              (.node 3 5   -- 14
                (.node 1 5   -- 8
                  (.node 2 5   -- 4
                    (.node 1 2   -- 2
                      (.leaf (swapProd [(1, 2), (1, 3), (4, 5)]))
                      (.leaf (swapProd [(1, 3), (4, 5)]))
                    )
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(1, 2), (1, 4), (1, 5), (1, 3)]))
                      (.leaf (swapProd [(1, 2), (1, 5), (1, 3)]))
                    )
                  )
                  (.node 1 2   -- 4
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(1, 3), (2, 4), (2, 5)]))
                      (.leaf (swapProd [(1, 3), (2, 5)]))
                    )
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(1, 4), (1, 5), (1, 3)]))
                      (.leaf (swapProd [(1, 4), (1, 5), (1, 2), (1, 3)]))
                    )
                  )
                )
                (.node 0 5   -- 6
                  (.node 1 2   -- 3
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(1, 3), (1, 2), (1, 4), (1, 5)]))
                      (.leaf (swapProd [(1, 3), (1, 2), (1, 5)]))
                    )
                    (.leaf (swapProd [(1, 4), (1, 5), (2, 3)]))
                  )
                  (.node 1 2   -- 3
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 4), (0, 5)]))
                      (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 5)]))
                    )
                    (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (2, 3)]))
                  )
                )
              )
            )
            (.node 0 5   -- 19
              (.node 1 2   -- 10
                (.node 3 4   -- 4
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(1, 4), (1, 3), (2, 5)]))
                    (.leaf (swapProd [(1, 4), (1, 3), (1, 2), (1, 5)]))
                  )
                  (.node 1 3   -- 2
                    (.leaf (swapProd [(1, 3), (1, 4), (1, 2), (1, 5)]))
                    (.leaf (swapProd [(1, 4), (1, 2), (1, 5)]))
                  )
                )
                (.node 2 4   -- 6
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(1, 5), (1, 3)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 5), (1, 2), (1, 3)]))
                      (.leaf (swapProd [(1, 5), (2, 3)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(1, 5), (1, 2), (1, 4), (1, 3)]))
                      (.leaf (swapProd [(1, 5), (2, 4), (2, 3)]))
                    )
                    (.leaf (swapProd [(1, 5), (2, 4)]))
                  )
                )
              )
              (.node 1 2   -- 9
                (.node 0 4   -- 5
                  (.node 1 3   -- 3
                    (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 2), (0, 5)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 2), (0, 5)]))
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 5)]))
                    )
                  )
                  (.node 1 3   -- 2
                    (.leaf (swapProd [(0, 2), (0, 5), (1, 3), (1, 4)]))
                    (.leaf (swapProd [(0, 2), (0, 5), (1, 4)]))
                  )
                )
                (.node 3 4   -- 4
                  (.node 2 4   -- 2
                    (.leaf (swapProd [(0, 1), (0, 5), (2, 3)]))
                    (.leaf (swapProd [(0, 1), (0, 5), (2, 4), (2, 3)]))
                  )
                  (.node 0 4   -- 2
                    (.leaf (swapProd [(0, 1), (0, 5), (2, 4)]))
                    (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 5)]))
                  )
                )
              )
            )
          )
        )
        (.node 4 5   -- 90
          (.node 1 5   -- 45
            (.node 0 4   -- 19
              (.node 1 2   -- 10
                (.node 1 4   -- 5
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 1), (0, 2), (0, 3)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 3)]))
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 4), (0, 3)]))
                    )
                  )
                  (.node 2 5   -- 2
                    (.leaf (swapProd [(0, 1), (0, 3), (2, 4)]))
                    (.leaf (swapProd [(0, 1), (0, 3), (2, 5), (2, 4)]))
                  )
                )
                (.node 0 2   -- 5
                  (.node 1 4   -- 3
                    (.leaf (swapProd [(0, 1), (0, 3)]))
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 3)]))
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 3)]))
                    )
                  )
                  (.node 1 4   -- 2
                    (.leaf (swapProd [(0, 2), (0, 1), (0, 3)]))
                    (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 3)]))
                  )
                )
              )
              (.node 1 2   -- 9
                (.node 2 5   -- 4
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 3)]))
                    (.leaf (swapProd [(0, 2), (0, 4), (1, 3)]))
                  )
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 1), (0, 3)]))
                    (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (1, 3)]))
                  )
                )
                (.node 0 2   -- 5
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 2), (0, 3), (1, 4)]))
                    (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 4)]))
                  )
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 3), (1, 4), (1, 2)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 3), (1, 4)]))
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 4)]))
                    )
                  )
                )
              )
            )
            (.node 0 5   -- 26
              (.node 2 5   -- 14
                (.node 0 2   -- 8
                  (.node 0 4   -- 4
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 3)]))
                      (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 2), (0, 3)]))
                    )
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 2), (0, 3), (1, 5), (1, 4)]))
                      (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 5), (0, 4)]))
                    )
                  )
                  (.node 2 4   -- 4
                    (.node 0 4   -- 2
                      (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 4), (0, 3)]))
                      (.leaf (swapProd [(0, 3), (1, 5), (1, 4), (1, 2)]))
                    )
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 3), (1, 5), (1, 4)]))
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 4)]))
                    )
                  )
                )
                (.node 1 2   -- 6
                  (.node 0 4   -- 3
                    (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 5), (0, 3)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (1, 4)]))
                      (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 1), (0, 4)]))
                    )
                  )
                  (.node 0 4   -- 3
                    (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (2, 4)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 5), (0, 3)]))
                      (.leaf (swapProd [(0, 2), (0, 4), (1, 5), (1, 3)]))
                    )
                  )
                )
              )
              (.node 0 2   -- 12
                (.node 1 2   -- 6
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 3), (1, 4), (2, 5)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (2, 5)]))
                      (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 1), (0, 4)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 3), (1, 5), (1, 2), (1, 4)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 2), (0, 4)]))
                      (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (1, 5)]))
                    )
                  )
                )
                (.node 2 5   -- 6
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 5), (0, 3)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 3)]))
                      (.leaf (swapProd [(0, 4), (1, 5), (1, 3)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 2), (0, 3)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (1, 5), (1, 2), (1, 3)]))
                      (.leaf (swapProd [(0, 4), (1, 5), (2, 3)]))
                    )
                  )
                )
              )
            )
          )
          (.node 1 4   -- 45
            (.node 0 5   -- 19
              (.node 1 2   -- 10
                (.node 1 5   -- 5
                  (.node 2 4   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (4, 5)]))
                      (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 5), (0, 3)]))
                    )
                    (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 3)]))
                  )
                  (.node 2 4   -- 2
                    (.leaf (swapProd [(0, 1), (0, 3), (2, 4), (2, 5)]))
                    (.leaf (swapProd [(0, 1), (0, 3), (2, 5)]))
                  )
                )
                (.node 0 2   -- 5
                  (.node 1 5   -- 3
                    (.leaf (swapProd [(0, 1), (0, 3), (4, 5)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 3)]))
                      (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 2), (0, 3)]))
                    )
                  )
                  (.node 1 5   -- 2
                    (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (4, 5)]))
                    (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 5), (0, 3)]))
                  )
                )
              )
              (.node 1 2   -- 9
                (.node 2 4   -- 4
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 1), (0, 3)]))
                    (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (1, 3)]))
                  )
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 3)]))
                    (.leaf (swapProd [(0, 2), (0, 5), (1, 3)]))
                  )
                )
                (.node 0 2   -- 5
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 2), (0, 3), (1, 4), (1, 5)]))
                    (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 4), (0, 5)]))
                  )
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(0, 3), (1, 4), (1, 5), (1, 2)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 3), (1, 4), (1, 5)]))
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 5)]))
                    )
                  )
                )
              )
            )
            (.node 0 4   -- 26
              (.node 2 4   -- 14
                (.node 0 2   -- 8
                  (.node 0 5   -- 4
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 1), (0, 5), (0, 3)]))
                      (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 3)]))
                    )
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 3), (1, 5)]))
                      (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 5)]))
                    )
                  )
                  (.node 2 5   -- 4
                    (.node 0 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 3)]))
                      (.leaf (swapProd [(0, 3), (1, 5), (1, 2)]))
                    )
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 3), (1, 5)]))
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 5)]))
                    )
                  )
                )
                (.node 1 2   -- 6
                  (.node 0 5   -- 3
                    (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (2, 5)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 4), (0, 3)]))
                      (.leaf (swapProd [(0, 2), (0, 5), (1, 4), (1, 3)]))
                    )
                  )
                  (.node 0 5   -- 3
                    (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 4), (0, 3)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (1, 5)]))
                      (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 1), (0, 5)]))
                    )
                  )
                )
              )
              (.node 0 2   -- 12
                (.node 1 2   -- 6
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 3), (1, 4), (1, 2), (1, 5)]))
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 2), (0, 5)]))
                    )
                    (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (1, 4)]))
                  )
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 3), (1, 5), (2, 4)]))
                      (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (2, 4)]))
                    )
                    (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 1), (0, 5)]))
                  )
                )
                (.node 2 4   -- 6
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(0, 4), (0, 3), (1, 5), (1, 2)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 3), (1, 5)]))
                      (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 5)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (1, 5)]))
                      (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 1), (0, 5)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (2, 3)]))
                  )
                )
              )
            )
          )
        )
      )
    )
    (.node 2 3   -- 360
      (.node 0 3   -- 180
        (.node 4 5   -- 90
          (.node 1 4   -- 45
            (.node 0 4   -- 26
              (.node 0 2   -- 12
                (.node 2 4   -- 6
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 1)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (3, 4)]))
                      (.leaf (swapProd [(0, 1), (3, 5), (3, 4)]))
                    )
                  )
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (2, 3), (2, 4)]))
                      (.leaf (swapProd [(0, 1), (2, 3), (2, 5), (2, 4)]))
                    )
                    (.leaf (swapProd [(0, 1), (2, 4), (3, 5)]))
                  )
                )
                (.node 1 2   -- 6
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 2), (0, 1)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 1), (3, 4)]))
                      (.leaf (swapProd [(0, 2), (0, 1), (3, 5), (3, 4)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 2)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 2), (3, 4)]))
                      (.leaf (swapProd [(0, 2), (3, 5), (3, 4)]))
                    )
                  )
                )
              )
              (.node 2 4   -- 14
                (.node 1 2   -- 6
                  (.node 0 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 1)]))
                      (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 2), (0, 1)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (3, 5)]))
                  )
                  (.node 0 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 4), (0, 2)]))
                      (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 2)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 2), (3, 5)]))
                  )
                )
                (.node 0 2   -- 8
                  (.node 2 5   -- 4
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 1)]))
                      (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 4), (0, 1)]))
                    )
                    (.node 0 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (3, 5)]))
                      (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 4), (0, 1)]))
                    )
                  )
                  (.node 0 5   -- 4
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 4), (0, 1)]))
                      (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 1)]))
                    )
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 1), (3, 5)]))
                      (.leaf (swapProd [(0, 4), (0, 1), (2, 3), (2, 5)]))
                    )
                  )
                )
              )
            )
            (.node 0 5   -- 19
              (.node 1 2   -- 9
                (.node 0 2   -- 5
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 3), (0, 4)]))
                      (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 4)]))
                    )
                    (.leaf (swapProd [(0, 2), (0, 4), (3, 5)]))
                  )
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 3), (0, 4)]))
                    (.leaf (swapProd [(0, 3), (0, 5), (0, 4)]))
                  )
                )
                (.node 2 4   -- 4
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 2)]))
                    (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 1), (0, 2)]))
                  )
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 3), (0, 4), (1, 2)]))
                    (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (1, 2)]))
                  )
                )
              )
              (.node 1 2   -- 10
                (.node 0 2   -- 5
                  (.node 1 5   -- 2
                    (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 4)]))
                    (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 2), (0, 4)]))
                  )
                  (.node 1 5   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 4), (3, 5)]))
                      (.leaf (swapProd [(0, 4), (2, 3), (2, 5)]))
                    )
                    (.leaf (swapProd [(0, 4), (1, 2), (1, 3), (1, 5)]))
                  )
                )
                (.node 1 5   -- 5
                  (.node 2 4   -- 2
                    (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (3, 5)]))
                    (.leaf (swapProd [(0, 4), (1, 2), (3, 5)]))
                  )
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 5), (0, 2)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 4), (1, 3), (1, 5), (1, 2)]))
                      (.leaf (swapProd [(0, 4), (1, 3), (1, 5)]))
                    )
                  )
                )
              )
            )
          )
          (.node 1 5   -- 45
            (.node 0 5   -- 26
              (.node 0 2   -- 12
                (.node 2 5   -- 6
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (4, 5)]))
                      (.leaf (swapProd [(0, 1), (3, 4), (3, 5)]))
                    )
                    (.leaf (swapProd [(0, 1), (3, 5)]))
                  )
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 1), (2, 3), (2, 4), (2, 5)]))
                      (.leaf (swapProd [(0, 1), (2, 3), (2, 5)]))
                    )
                    (.leaf (swapProd [(0, 1), (2, 4), (2, 3), (2, 5)]))
                  )
                )
                (.node 1 2   -- 6
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 1), (4, 5)]))
                      (.leaf (swapProd [(0, 2), (0, 1), (3, 4), (3, 5)]))
                    )
                    (.leaf (swapProd [(0, 2), (0, 1), (3, 5)]))
                  )
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 2), (4, 5)]))
                      (.leaf (swapProd [(0, 2), (3, 4), (3, 5)]))
                    )
                    (.leaf (swapProd [(0, 2), (3, 5)]))
                  )
                )
              )
              (.node 2 5   -- 14
                (.node 1 2   -- 6
                  (.node 0 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 2), (0, 1)]))
                      (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 1)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 2), (0, 1)]))
                  )
                  (.node 0 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 2)]))
                      (.leaf (swapProd [(0, 3), (0, 5), (0, 2)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 2)]))
                  )
                )
                (.node 0 2   -- 8
                  (.node 2 4   -- 4
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 5), (0, 1)]))
                      (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 1)]))
                    )
                    (.node 0 4   -- 2
                      (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 5), (0, 1)]))
                      (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (2, 4)]))
                    )
                  )
                  (.node 0 4   -- 4
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 1)]))
                      (.leaf (swapProd [(0, 3), (0, 5), (0, 1)]))
                    )
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 1)]))
                      (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 5), (0, 1)]))
                    )
                  )
                )
              )
            )
            (.node 0 4   -- 19
              (.node 1 2   -- 9
                (.node 0 2   -- 5
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 5)]))
                      (.leaf (swapProd [(0, 2), (0, 3), (0, 5)]))
                    )
                    (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 5)]))
                  )
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 3), (0, 4), (0, 5)]))
                    (.leaf (swapProd [(0, 3), (0, 5)]))
                  )
                )
                (.node 2 5   -- 4
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 1), (0, 2)]))
                    (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 2)]))
                  )
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (1, 2)]))
                    (.leaf (swapProd [(0, 3), (0, 5), (1, 2)]))
                  )
                )
              )
              (.node 1 2   -- 10
                (.node 0 2   -- 5
                  (.node 1 4   -- 2
                    (.leaf (swapProd [(0, 3), (0, 5), (2, 4)]))
                    (.leaf (swapProd [(0, 3), (0, 5), (1, 2), (1, 4)]))
                  )
                  (.node 1 4   -- 3
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 3), (0, 5)]))
                      (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 5)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 3), (0, 5)]))
                  )
                )
                (.node 1 4   -- 5
                  (.node 2 5   -- 2
                    (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 1), (0, 2)]))
                    (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (1, 2)]))
                  )
                  (.node 2 4   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 2), (1, 3), (1, 5)]))
                      (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 3), (0, 5)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 5)]))
                  )
                )
              )
            )
          )
        )
        (.node 4 5   -- 90
          (.node 1 4   -- 45
            (.node 0 5   -- 19
              (.node 1 2   -- 9
                (.node 3 4   -- 4
                  (.node 0 4   -- 2
                    (.leaf (swapProd [(0, 3), (0, 2), (0, 1)]))
                    (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 1)]))
                  )
                  (.node 2 4   -- 2
                    (.leaf (swapProd [(0, 4), (0, 2), (0, 1)]))
                    (.leaf (swapProd [(0, 4), (0, 1)]))
                  )
                )
                (.node 0 4   -- 5
                  (.node 1 3   -- 2
                    (.leaf (swapProd [(0, 3), (0, 2)]))
                    (.leaf (swapProd [(0, 3), (0, 1), (0, 2)]))
                  )
                  (.node 1 3   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 3), (0, 2)]))
                      (.leaf (swapProd [(0, 4), (0, 2)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 2)]))
                  )
                )
              )
              (.node 1 2   -- 10
                (.node 2 4   -- 6
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 2), (0, 1)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 1)]))
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 2), (0, 1)]))
                    )
                  )
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 4), (0, 1)]))
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 1)]))
                    )
                    (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 4), (0, 1)]))
                  )
                )
                (.node 3 4   -- 4
                  (.node 1 3   -- 2
                    (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 2)]))
                    (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 1), (0, 2)]))
                  )
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 5), (0, 4), (0, 2)]))
                    (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 2)]))
                  )
                )
              )
            )
            (.node 1 3   -- 26
              (.node 3 5   -- 14
                (.node 0 5   -- 6
                  (.node 1 2   -- 3
                    (.leaf (swapProd [(0, 4)]))
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 1), (0, 2)]))
                      (.leaf (swapProd [(0, 4), (1, 2)]))
                    )
                  )
                  (.node 1 2   -- 3
                    (.leaf (swapProd [(0, 5), (0, 4)]))
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 2)]))
                      (.leaf (swapProd [(0, 5), (0, 4), (1, 2)]))
                    )
                  )
                )
                (.node 1 5   -- 8
                  (.node 1 2   -- 4
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 4)]))
                      (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 4)]))
                    )
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 1), (0, 2)]))
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (1, 2)]))
                    )
                  )
                  (.node 2 5   -- 4
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 5), (0, 2), (1, 3), (1, 4)]))
                      (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 3), (0, 4)]))
                    )
                    (.node 1 2   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 3), (0, 4)]))
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 4)]))
                    )
                  )
                )
              )
              (.node 1 5   -- 12
                (.node 0 5   -- 6
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 2), (1, 3)]))
                      (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 2)]))
                    )
                    (.leaf (swapProd [(0, 4), (1, 3), (1, 2)]))
                  )
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (1, 3)]))
                      (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 3), (0, 2)]))
                    )
                    (.leaf (swapProd [(0, 5), (0, 4), (1, 3), (1, 2)]))
                  )
                )
                (.node 2 4   -- 6
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 4), (0, 2)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (1, 4)]))
                      (.leaf (swapProd [(0, 5), (0, 2), (1, 4)]))
                    )
                  )
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 1), (0, 4)]))
                      (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 4)]))
                    )
                    (.leaf (swapProd [(0, 5), (0, 1), (0, 4)]))
                  )
                )
              )
            )
          )
          (.node 1 5   -- 45
            (.node 0 4   -- 19
              (.node 1 2   -- 9
                (.node 3 5   -- 4
                  (.node 0 5   -- 2
                    (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (4, 5)]))
                    (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 2), (0, 1)]))
                  )
                  (.node 2 5   -- 2
                    (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 1)]))
                    (.leaf (swapProd [(0, 4), (0, 5), (0, 1)]))
                  )
                )
                (.node 0 5   -- 5
                  (.node 1 3   -- 2
                    (.leaf (swapProd [(0, 3), (0, 2), (4, 5)]))
                    (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (4, 5)]))
                  )
                  (.node 1 3   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 2)]))
                      (.leaf (swapProd [(0, 4), (0, 5), (0, 2)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 1), (0, 2)]))
                  )
                )
              )
              (.node 1 2   -- 10
                (.node 2 5   -- 6
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 1)]))
                      (.leaf (swapProd [(0, 5), (0, 2), (0, 1)]))
                    )
                    (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (3, 4)]))
                  )
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1)]))
                      (.leaf (swapProd [(0, 5), (0, 1), (3, 4)]))
                    )
                    (.leaf (swapProd [(0, 5), (0, 1), (2, 3), (2, 4)]))
                  )
                )
                (.node 3 5   -- 4
                  (.node 1 3   -- 2
                    (.leaf (swapProd [(0, 5), (0, 3), (0, 2)]))
                    (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 2)]))
                  )
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 5), (0, 2)]))
                    (.leaf (swapProd [(0, 5), (0, 2), (3, 4)]))
                  )
                )
              )
            )
            (.node 1 3   -- 26
              (.node 3 4   -- 14
                (.node 0 4   -- 6
                  (.node 1 2   -- 3
                    (.leaf (swapProd [(0, 4), (0, 5)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 2)]))
                      (.leaf (swapProd [(0, 4), (0, 5), (1, 2)]))
                    )
                  )
                  (.node 1 2   -- 3
                    (.leaf (swapProd [(0, 5)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 2)]))
                      (.leaf (swapProd [(0, 5), (1, 2)]))
                    )
                  )
                )
                (.node 1 4   -- 8
                  (.node 1 2   -- 4
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 5), (3, 4)]))
                      (.leaf (swapProd [(0, 5), (2, 3), (2, 4)]))
                    )
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (3, 4)]))
                      (.leaf (swapProd [(0, 5), (1, 2), (3, 4)]))
                    )
                  )
                  (.node 2 4   -- 4
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 4), (0, 2)]))
                      (.leaf (swapProd [(0, 5), (1, 3), (1, 4), (1, 2)]))
                    )
                    (.node 1 2   -- 2
                      (.leaf (swapProd [(0, 5), (1, 2), (1, 3), (1, 4)]))
                      (.leaf (swapProd [(0, 5), (1, 3), (1, 4)]))
                    )
                  )
                )
              )
              (.node 1 4   -- 12
                (.node 0 4   -- 6
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (1, 3)]))
                      (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 3), (0, 2)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 5), (1, 3), (1, 2)]))
                  )
                  (.node 2 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 2), (1, 3)]))
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 2)]))
                    )
                    (.leaf (swapProd [(0, 5), (1, 3), (1, 2)]))
                  )
                )
                (.node 2 5   -- 6
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 2), (1, 4), (1, 3)]))
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 3), (0, 2)]))
                    )
                    (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 2)]))
                  )
                  (.node 2 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 5), (1, 4), (1, 3), (1, 2)]))
                      (.leaf (swapProd [(0, 5), (1, 4), (1, 2)]))
                    )
                    (.leaf (swapProd [(0, 5), (1, 4)]))
                  )
                )
              )
            )
          )
        )
      )
      (.node 0 2   -- 180
        (.node 4 5   -- 90
          (.node 1 4   -- 45
            (.node 0 4   -- 26
              (.node 0 3   -- 12
                (.node 2 5   -- 6
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 1), (2, 3)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 1), (2, 4), (2, 3)]))
                      (.leaf (swapProd [(0, 1), (2, 4)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 1), (2, 5), (2, 4), (2, 3)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (2, 5), (2, 4)]))
                      (.leaf (swapProd [(0, 1), (2, 5), (2, 3), (2, 4)]))
                    )
                  )
                )
                (.node 1 3   -- 6
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 2), (0, 3), (0, 1)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 1)]))
                      (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 3), (0, 1)]))
                    )
                  )
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 2), (0, 3)]))
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 4), (0, 3)]))
                      (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 3)]))
                    )
                  )
                )
              )
              (.node 3 4   -- 14
                (.node 1 3   -- 6
                  (.node 0 5   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 1), (2, 4)]))
                      (.leaf (swapProd [(0, 3), (0, 1), (2, 5), (2, 4)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 3), (0, 1)]))
                  )
                  (.node 0 5   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 3), (2, 4)]))
                      (.leaf (swapProd [(0, 3), (2, 5), (2, 4)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 3)]))
                  )
                )
                (.node 0 3   -- 8
                  (.node 3 5   -- 4
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 4), (0, 1)]))
                      (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 1)]))
                    )
                    (.node 0 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 4), (0, 1)]))
                      (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (2, 5)]))
                    )
                  )
                  (.node 0 5   -- 4
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 1)]))
                      (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 4), (0, 1)]))
                    )
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 1), (2, 5), (2, 3)]))
                      (.leaf (swapProd [(0, 4), (0, 1), (2, 5)]))
                    )
                  )
                )
              )
            )
            (.node 0 5   -- 19
              (.node 1 3   -- 9
                (.node 0 3   -- 5
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(0, 2), (0, 4)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 5), (0, 4)]))
                      (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 4)]))
                    )
                  )
                  (.node 2 5   -- 2
                    (.leaf (swapProd [(0, 3), (0, 2), (0, 4)]))
                    (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 4)]))
                  )
                )
                (.node 2 5   -- 4
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 3), (1, 2), (1, 4)]))
                    (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 4)]))
                  )
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 3), (1, 2), (1, 5), (1, 4)]))
                    (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 5), (0, 4)]))
                  )
                )
              )
              (.node 1 3   -- 10
                (.node 0 3   -- 5
                  (.node 1 5   -- 2
                    (.leaf (swapProd [(0, 3), (0, 4), (2, 5)]))
                    (.leaf (swapProd [(0, 3), (0, 4), (1, 2), (1, 5)]))
                  )
                  (.node 1 5   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (2, 5), (2, 3)]))
                      (.leaf (swapProd [(0, 4), (2, 5)]))
                    )
                    (.leaf (swapProd [(0, 4), (1, 2), (1, 5)]))
                  )
                )
                (.node 1 5   -- 5
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 5), (0, 3)]))
                    (.leaf (swapProd [(0, 4), (1, 2), (1, 5), (1, 3)]))
                  )
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (2, 5)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (1, 3), (2, 5)]))
                      (.leaf (swapProd [(0, 4), (1, 3), (1, 2), (1, 5)]))
                    )
                  )
                )
              )
            )
          )
          (.node 1 5   -- 45
            (.node 0 5   -- 26
              (.node 0 3   -- 12
                (.node 2 4   -- 6
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(0, 1), (2, 3), (4, 5)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (2, 4), (2, 5), (2, 3)]))
                      (.leaf (swapProd [(0, 1), (2, 4), (2, 5)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 1), (2, 5), (2, 3)]))
                      (.leaf (swapProd [(0, 1), (2, 5)]))
                    )
                    (.leaf (swapProd [(0, 1), (2, 5), (3, 4)]))
                  )
                )
                (.node 1 3   -- 6
                  (.node 2 4   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (4, 5)]))
                      (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 3), (0, 1)]))
                    )
                    (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 1)]))
                  )
                  (.node 2 4   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 2), (0, 3), (4, 5)]))
                      (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 3)]))
                    )
                    (.leaf (swapProd [(0, 2), (0, 5), (0, 3)]))
                  )
                )
              )
              (.node 3 5   -- 14
                (.node 1 3   -- 6
                  (.node 0 4   -- 3
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 3), (0, 1), (2, 4), (2, 5)]))
                      (.leaf (swapProd [(0, 3), (0, 1), (2, 5)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (2, 5)]))
                  )
                  (.node 0 4   -- 3
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 3), (2, 4), (2, 5)]))
                      (.leaf (swapProd [(0, 3), (2, 5)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 3), (2, 5)]))
                  )
                )
                (.node 0 3   -- 8
                  (.node 3 4   -- 4
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 1)]))
                      (.leaf (swapProd [(0, 2), (0, 5), (0, 1)]))
                    )
                    (.node 0 4   -- 2
                      (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (3, 4)]))
                      (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 5), (0, 1)]))
                    )
                  )
                  (.node 0 4   -- 4
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 5), (0, 1)]))
                      (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 1)]))
                    )
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 5), (0, 1)]))
                      (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 1)]))
                    )
                  )
                )
              )
            )
            (.node 0 4   -- 19
              (.node 1 3   -- 9
                (.node 0 3   -- 5
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 2), (0, 4), (0, 5)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 2), (0, 5)]))
                      (.leaf (swapProd [(0, 2), (0, 5), (3, 4)]))
                    )
                  )
                  (.node 2 4   -- 2
                    (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 5)]))
                    (.leaf (swapProd [(0, 3), (0, 2), (0, 5)]))
                  )
                )
                (.node 2 4   -- 4
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 3), (1, 2), (1, 4), (1, 5)]))
                    (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 4), (0, 5)]))
                  )
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 3), (1, 2), (1, 5)]))
                    (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 5)]))
                  )
                )
              )
              (.node 1 3   -- 10
                (.node 0 3   -- 5
                  (.node 1 4   -- 2
                    (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 5)]))
                    (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 2), (0, 5)]))
                  )
                  (.node 1 4   -- 3
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 5)]))
                      (.leaf (swapProd [(0, 4), (0, 2), (0, 5)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 5)]))
                  )
                )
                (.node 1 4   -- 5
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 4), (0, 3), (1, 2), (1, 5)]))
                    (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 2), (0, 5)]))
                  )
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 1), (0, 3)]))
                      (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (1, 3)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 2), (0, 5)]))
                  )
                )
              )
            )
          )
        )
        (.node 4 5   -- 90
          (.node 1 4   -- 45
            (.node 0 5   -- 19
              (.node 1 3   -- 9
                (.node 2 4   -- 4
                  (.node 0 4   -- 2
                    (.leaf (swapProd [(0, 3), (0, 1)]))
                    (.leaf (swapProd [(0, 4), (0, 3), (0, 1)]))
                  )
                  (.node 3 4   -- 2
                    (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 1)]))
                    (.leaf (swapProd [(0, 4), (0, 1), (2, 3)]))
                  )
                )
                (.node 0 4   -- 5
                  (.node 1 2   -- 2
                    (.leaf (swapProd [(0, 3)]))
                    (.leaf (swapProd [(0, 3), (1, 2)]))
                  )
                  (.node 1 2   -- 3
                    (.node 2 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 3)]))
                      (.leaf (swapProd [(0, 4), (0, 2), (0, 3)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 3), (1, 2)]))
                  )
                )
              )
              (.node 1 3   -- 10
                (.node 2 5   -- 6
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 1)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 3), (0, 1)]))
                      (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (2, 3)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (2, 4)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 4), (0, 1)]))
                      (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 1)]))
                    )
                  )
                )
                (.node 2 4   -- 4
                  (.node 1 2   -- 2
                    (.leaf (swapProd [(0, 5), (0, 4), (0, 3)]))
                    (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (1, 2)]))
                  )
                  (.node 2 5   -- 2
                    (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 3)]))
                    (.leaf (swapProd [(0, 5), (0, 3), (2, 4)]))
                  )
                )
              )
            )
            (.node 1 2   -- 26
              (.node 2 5   -- 14
                (.node 0 5   -- 6
                  (.node 1 3   -- 3
                    (.leaf (swapProd [(0, 4), (2, 3)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 3)]))
                      (.leaf (swapProd [(0, 4), (1, 2), (1, 3)]))
                    )
                  )
                  (.node 1 3   -- 3
                    (.leaf (swapProd [(0, 5), (0, 4), (2, 3)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 2), (0, 3)]))
                      (.leaf (swapProd [(0, 5), (0, 4), (1, 2), (1, 3)]))
                    )
                  )
                )
                (.node 1 5   -- 8
                  (.node 1 3   -- 4
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 4)]))
                      (.leaf (swapProd [(0, 5), (0, 2), (0, 4)]))
                    )
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 5), (0, 3), (1, 2), (1, 4)]))
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 2), (0, 4)]))
                    )
                  )
                  (.node 3 5   -- 4
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 1), (0, 3)]))
                      (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (1, 3)]))
                    )
                    (.node 1 3   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 4)]))
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 2), (0, 4)]))
                    )
                  )
                )
              )
              (.node 1 5   -- 12
                (.node 0 5   -- 6
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 3)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 4), (0, 1), (0, 3)]))
                      (.leaf (swapProd [(0, 4), (1, 3)]))
                    )
                  )
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 1), (0, 3)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 3)]))
                      (.leaf (swapProd [(0, 5), (0, 4), (1, 3)]))
                    )
                  )
                )
                (.node 2 5   -- 6
                  (.node 2 4   -- 3
                    (.leaf (swapProd [(0, 5), (0, 3), (1, 4), (1, 2)]))
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 5), (0, 3), (1, 4)]))
                      (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 4)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (1, 4)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 1), (0, 4)]))
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (2, 3)]))
                    )
                  )
                )
              )
            )
          )
          (.node 1 5   -- 45
            (.node 0 4   -- 19
              (.node 1 3   -- 9
                (.node 2 5   -- 4
                  (.node 0 5   -- 2
                    (.leaf (swapProd [(0, 3), (0, 1), (4, 5)]))
                    (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 1)]))
                  )
                  (.node 3 5   -- 2
                    (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 3), (0, 1)]))
                    (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (2, 3)]))
                  )
                )
                (.node 0 5   -- 5
                  (.node 1 2   -- 2
                    (.leaf (swapProd [(0, 3), (4, 5)]))
                    (.leaf (swapProd [(0, 3), (1, 2), (4, 5)]))
                  )
                  (.node 1 2   -- 3
                    (.node 2 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 5), (0, 3)]))
                      (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 3)]))
                    )
                    (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (1, 2)]))
                  )
                )
              )
              (.node 1 3   -- 10
                (.node 2 4   -- 6
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(0, 5), (0, 3), (0, 1)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 1)]))
                      (.leaf (swapProd [(0, 5), (0, 1), (2, 3)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 3), (0, 1)]))
                      (.leaf (swapProd [(0, 5), (0, 1), (2, 4), (2, 3)]))
                    )
                    (.leaf (swapProd [(0, 5), (0, 1), (2, 4)]))
                  )
                )
                (.node 2 5   -- 4
                  (.node 1 2   -- 2
                    (.leaf (swapProd [(0, 5), (0, 3)]))
                    (.leaf (swapProd [(0, 5), (0, 3), (1, 2)]))
                  )
                  (.node 2 4   -- 2
                    (.leaf (swapProd [(0, 5), (0, 2), (0, 3)]))
                    (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 3)]))
                  )
                )
              )
            )
            (.node 1 2   -- 26
              (.node 2 4   -- 14
                (.node 0 4   -- 6
                  (.node 1 3   -- 3
                    (.leaf (swapProd [(0, 4), (0, 5), (2, 3)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 2), (0, 3)]))
                      (.leaf (swapProd [(0, 4), (0, 5), (1, 2), (1, 3)]))
                    )
                  )
                  (.node 1 3   -- 3
                    (.leaf (swapProd [(0, 5), (2, 3)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 3)]))
                      (.leaf (swapProd [(0, 5), (1, 2), (1, 3)]))
                    )
                  )
                )
                (.node 1 4   -- 8
                  (.node 1 3   -- 4
                    (.node 3 4   -- 2
                      (.leaf (swapProd [(0, 5), (2, 4), (2, 3)]))
                      (.leaf (swapProd [(0, 5), (2, 4)]))
                    )
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 4), (0, 3)]))
                      (.leaf (swapProd [(0, 5), (1, 2), (1, 4), (1, 3)]))
                    )
                  )
                  (.node 3 4   -- 4
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (2, 4)]))
                      (.leaf (swapProd [(0, 5), (1, 3), (2, 4)]))
                    )
                    (.node 1 3   -- 2
                      (.leaf (swapProd [(0, 5), (1, 2), (1, 4)]))
                      (.leaf (swapProd [(0, 5), (1, 3), (1, 2), (1, 4)]))
                    )
                  )
                )
              )
              (.node 1 4   -- 12
                (.node 0 4   -- 6
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 1), (0, 3)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 3)]))
                      (.leaf (swapProd [(0, 4), (0, 5), (1, 3)]))
                    )
                  )
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 3)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 3)]))
                      (.leaf (swapProd [(0, 5), (1, 3)]))
                    )
                  )
                )
                (.node 2 4   -- 6
                  (.node 2 5   -- 3
                    (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 4), (0, 3)]))
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 3)]))
                      (.leaf (swapProd [(0, 5), (1, 4), (1, 3)]))
                    )
                  )
                  (.node 3 4   -- 3
                    (.node 3 5   -- 2
                      (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 2), (0, 3)]))
                      (.leaf (swapProd [(0, 5), (1, 4), (1, 2), (1, 3)]))
                    )
                    (.leaf (swapProd [(0, 5), (1, 4), (2, 3)]))
                  )
                )
              )
            )
          )
        )
      )
    )
  )

/-- The depth is `10`: ten comparisons always suffice.  (`depth` is the maximum over
leaves, so some leaf sits exactly at depth `10`.) -/
theorem tree6_depth : depth tree6 = 10 := by decide

/-- As many leaves as there are orderings of six elements. -/
theorem tree6_numLeaves : numLeaves tree6 = 720 := by decide

set_option maxRecDepth 8000 in
/-- The tree sorts: on all `6! = 720` canonical inputs it outputs the sorting
permutation, hence on every input with distinct values.  `decide` folds over the
`720` canonical inputs listed by `allPerms 6` (`Verify.lean`), so this does not go
through the `Fintype (Equiv.Perm (Fin 6))` instance.  The fold is still `720`
elements deep, past the elaborator's default recursion limit of 1000. -/
theorem tree6_correct : Correct (α := ℕ) tree6 :=
  correct_of_allPerms (by decide)

/-- **`S 6 = 10`**: ten comparisons sort six elements, and counting rules out
nine. -/
theorem S_six : S 6 = 10 := by
  refine le_antisymm ?_ ?_
  · -- upper bound: the adaptive tree
    refine (S_le_iff 6 10).2 ⟨tree6, tree6_correct, ?_⟩
    rw [tree6_depth]
  · -- lower bound: `Nat.clog 2 6! = 10`
    have h := S_lower 6
    have h720 : Nat.clog 2 (Nat.factorial 6) = 10 := by decide
    omega

/-- **Ten comparisons are necessary in the *comparison-count* reading too**: no
correct tree keeps every input at `≤ 9` comparisons. -/
theorem six_needs_ten_comparisons :
    ¬ ∃ t : Tree 6, Correct (α := ℕ) t ∧
      ∀ x : Fin 6 → ℕ, Function.Injective x → cost t x ≤ 9 := by
  rintro ⟨t, ht, hcost⟩
  have hwc : worstCase t ≤ 9 := by
    apply Finset.sup_le
    intro p _
    exact hcost (xOfPerm p) (xOfPerm_injective p)
  have hlb := logb_factorial_le_worstCase ht
  have h720 : (9 : ℝ) < Real.logb 2 (Nat.factorial 6) := by
    have hfac : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
    rw [hfac]
    have hpow : (2 : ℝ) ^ 9 < 720 := by norm_num
    calc (9 : ℝ) = Real.logb 2 ((2 : ℝ) ^ 9) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
      _ < Real.logb 2 (720 : ℝ) :=
          Real.logb_lt_logb (b := 2) (by norm_num : (1 : ℝ) < 2) (by positivity) hpow
  have : (worstCase t : ℝ) ≤ 9 := by exact_mod_cast hwc
  linarith

end SortBounds.Projects.SN
