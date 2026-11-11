/-
SortBounds/Projects/SN/Seven.lean

`S 7 = 13`: thirteen comparisons sort seven elements, and counting forbids fewer
(`⌈log₂ 7!⌉ = ⌈log₂ 5040⌉ = 13`).

Thirteen comparisons is far below the sixteen comparators of the best sorting
*network* on seven wires (a classical fact, not formalised here), so the upper
bound again requires an *adaptive* tree — `tree7` below, of depth `13` with
`5040 = 7!` leaves.  Like `tree5`/`tree6` it is the output of the exhaustive
search over knowledge states in `search_optimal_tree.py` (which prints the
definitions below); the search is *not* formalised.  The three facts that make
the tree trustworthy are kernel-checked:

* `tree7_depth`: the depth is `13`;
* `tree7_numLeaves`: the tree has `5040` leaves — exactly `7!`, the counting
  bound of `factorial_le_numLeaves`, so there is no slack;
* `tree7_correct`: it sorts every `ℕ`-valued input with pairwise distinct values —
  `correct_of_forall_run_xOfPerm` reduces this to the `7! = 5040` canonical
  inputs, and `decide` checks those (`correct_of_allPerms`, which feeds the `5040`
  canonical inputs to `decide` as an explicit list instead of filtering the
  `7 ^ 7` functions `Fin 7 → Fin 7`).

Every internal node is annotated with the number of orderings consistent with the
answers that reach it, so the two children of a node add up to the node's own
count and no subtree is asked for more comparisons than its own count allows
(`#orderings ≤ 2 ^ remaining depth`).  Along the leftmost path the counts read
`5040 → 2520 → 1260 → 630 → 315 → 168 → 84 → 42 → 21 → 10 → 6 → 3 → 2 → 1`: the
first four splits are exactly even (`5040 = 2·2520`, …, `630 = 2·315`), then
`315` splits as `168 + 147`.

A leaf carries its ordering as the permutation to output, written as a product of
transpositions: `swapProd [(0, 1), (1, 2)]` is `Equiv.swap 0 1 * Equiv.swap 1 2`,
which sends `0 ↦ 1 ↦ 2 ↦ 0`; the identity is written `1`.
-/
import SortBounds.Projects.SN.Verify
import SortBounds.Projects.SN.Basic
import SortBounds.Comparison.LowerBound

namespace SortBounds.Projects.SN

open SortBounds

-- The tree is `5039` internal nodes and `5039` leaves — a term no elaborator
-- wants to see at once (`set_option maxRecDepth` alone does not save it: the
-- pending-mvar synthesis becomes quadratic).  So it is written in `63` pieces:
-- one `private def` for every subtree with more than `120` nodes, children
-- before parents, each piece small enough to elaborate on its own.  `tree7` is
-- the top piece; every subtree below `120` nodes is spelled out inline.
-- subtrees, children before parents
private def tree70 : Tree 7 :=
            (.node 3 6   -- 168
              (.node 1 3   -- 84
                (.node 1 2   -- 42
                  (.node 1 4   -- 21
                    (.node 2 4   -- 10
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf 1)
                            (.leaf (swapProd [(5, 6)]))
                          )
                          (.leaf (swapProd [(4, 5), (4, 6)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(3, 4)]))
                            (.leaf (swapProd [(3, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(3, 5), (3, 4)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(2, 3), (2, 4)]))
                          (.leaf (swapProd [(2, 3), (2, 4), (5, 6)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(2, 3), (2, 5), (2, 4)]))
                          (.leaf (swapProd [(2, 4), (3, 5)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 2 5   -- 5
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 4)]))
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(1, 2), (1, 3), (1, 5), (1, 4)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 2), (1, 4), (3, 5)]))
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 2), (1, 4)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 5), (0, 4)]))
                        )
                        (.node 0 5   -- 3
                          (.node 1 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 2), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 4), (1, 3), (1, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 4   -- 21
                    (.node 1 4   -- 10
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2)]))
                            (.leaf (swapProd [(1, 2), (5, 6)]))
                          )
                          (.leaf (swapProd [(1, 2), (4, 5), (4, 6)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (3, 4)]))
                            (.leaf (swapProd [(1, 2), (3, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(1, 2), (3, 5), (3, 4)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 2), (5, 6)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(1, 4), (1, 2), (3, 5)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 1 5   -- 5
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 3), (1, 4)]))
                            (.leaf (swapProd [(1, 3), (1, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 4)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 4), (3, 5)]))
                          (.leaf (swapProd [(1, 4), (2, 3), (2, 5)]))
                        )
                      )
                      (.node 1 5   -- 6
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 4)]))
                        )
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (2, 3), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 1), (0, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 6   -- 42
                  (.node 1 5   -- 21
                    (.node 3 4   -- 11
                      (.node 1 4   -- 5
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 3), (1, 2)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (5, 6)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 2), (4, 5), (4, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 2)]))
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 2), (5, 6)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(1, 4), (1, 2)]))
                            (.leaf (swapProd [(1, 4)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4)]))
                        )
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(1, 4), (1, 2), (5, 6)]))
                            (.leaf (swapProd [(1, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4), (5, 6)]))
                        )
                      )
                    )
                    (.node 0 4   -- 10
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
                  (.node 2 4   -- 21
                    (.node 1 5   -- 10
                      (.node 4 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 4), (1, 3), (1, 2)]))
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 4), (1, 2)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 6), (1, 3), (1, 2)]))
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 3), (1, 2)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 5), (1, 4), (1, 3), (1, 2)]))
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 3), (1, 2)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 3), (1, 2)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 5), (1, 4), (1, 2)]))
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 2)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 5), (1, 3), (1, 4), (1, 2)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 3 5   -- 5
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(1, 6), (1, 4)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 6), (1, 5), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(1, 6), (1, 5), (1, 2), (1, 3), (1, 4)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 2), (0, 3), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (1, 6), (1, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 6   -- 84
                (.node 1 2   -- 42
                  (.node 1 4   -- 21
                    (.node 2 4   -- 10
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(3, 4), (3, 5), (3, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(3, 5), (3, 6), (3, 4)]))
                            (.leaf (swapProd [(3, 5), (3, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(3, 6), (3, 5), (3, 4)]))
                            (.leaf (swapProd [(3, 6), (3, 4)]))
                          )
                          (.leaf (swapProd [(3, 6)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(2, 3), (2, 6), (2, 5), (2, 4)]))
                          (.leaf (swapProd [(2, 4), (3, 6), (3, 5)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(2, 3), (2, 5), (2, 6), (2, 4)]))
                          (.leaf (swapProd [(2, 3), (2, 6), (2, 4)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 2 5   -- 5
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(1, 2), (1, 3), (1, 5), (1, 6), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 6), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 6), (1, 4)]))
                          )
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 2), (1, 4), (3, 6), (3, 5)]))
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 5), (1, 2), (1, 4)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 6), (0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 6), (0, 4)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.node 1 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (3, 6), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 5), (0, 2), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 4), (1, 3), (1, 6), (1, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 4   -- 21
                    (.node 1 4   -- 10
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(1, 2), (3, 4), (3, 5), (3, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 2), (3, 5), (3, 6), (3, 4)]))
                            (.leaf (swapProd [(1, 2), (3, 5), (3, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (3, 6), (3, 5), (3, 4)]))
                            (.leaf (swapProd [(1, 2), (3, 6), (3, 4)]))
                          )
                          (.leaf (swapProd [(1, 2), (3, 6)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 5), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(1, 4), (1, 2), (3, 6), (3, 5)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 6), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 4), (1, 2)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 1 5   -- 5
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 6), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 3), (1, 6), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(1, 3), (1, 6), (1, 4)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 4), (3, 6), (3, 5)]))
                          (.leaf (swapProd [(1, 4), (2, 3), (2, 6), (2, 5)]))
                        )
                      )
                      (.node 1 5   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 6), (0, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 4)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (3, 6), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (2, 3), (2, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 5), (0, 1), (0, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 42
                  (.node 1 5   -- 21
                    (.node 3 5   -- 11
                      (.node 4 6   -- 6
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(1, 4), (1, 2), (3, 5), (3, 6)]))
                            (.leaf (swapProd [(1, 4), (3, 5), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4), (3, 5), (3, 6)]))
                        )
                        (.node 1 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 3), (1, 4), (1, 5), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(1, 3), (1, 5), (1, 6), (1, 2)]))
                          )
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 5), (1, 6), (1, 2)]))
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 2)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 4), (1, 2), (3, 6)]))
                            (.leaf (swapProd [(1, 4), (1, 3), (1, 6), (1, 2)]))
                          )
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (3, 6)]))
                        )
                      )
                    )
                    (.node 0 4   -- 10
                      (.node 2 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 5), (1, 3), (1, 6), (1, 4), (1, 2)]))
                            (.leaf (swapProd [(1, 5), (1, 4), (1, 2), (3, 6)]))
                          )
                          (.leaf (swapProd [(1, 5), (1, 4), (1, 3), (1, 6), (1, 2)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 5), (1, 3), (1, 6), (1, 4)]))
                            (.leaf (swapProd [(1, 5), (1, 4), (3, 6)]))
                          )
                          (.leaf (swapProd [(1, 5), (1, 2), (1, 3), (1, 6), (1, 4)]))
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (3, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 3), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 4), (1, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 4   -- 21
                    (.node 1 5   -- 10
                      (.node 3 4   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 6), (1, 2)]))
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 2)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 3), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 2), (3, 4)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(1, 6), (1, 2)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 3), (1, 4), (1, 2)]))
                            (.leaf (swapProd [(1, 6), (1, 2), (3, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 2), (3, 5)]))
                            (.leaf (swapProd [(1, 6), (1, 3), (1, 5), (1, 4), (1, 2)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 2), (3, 5), (3, 4)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 3 5   -- 5
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(1, 6), (1, 3), (1, 4)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 4), (3, 5)]))
                            (.leaf (swapProd [(1, 6), (1, 3), (1, 5), (1, 4)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 4), (2, 3), (2, 5)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (2, 3), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 1), (0, 6), (0, 4)]))
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 3), (0, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 5), (0, 4)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree71 : Tree 7 :=
            (.node 4 6   -- 147
              (.node 1 2   -- 66
                (.node 1 6   -- 32
                  (.node 0 4   -- 15
                    (.node 1 4   -- 9
                      (.node 2 5   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(2, 4), (3, 5), (3, 6)]))
                          (.leaf (swapProd [(2, 4), (3, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(2, 5), (2, 3), (2, 6), (2, 4)]))
                          (.leaf (swapProd [(2, 5), (2, 4), (3, 6)]))
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 2), (1, 4), (3, 5), (3, 6)]))
                          (.leaf (swapProd [(1, 2), (1, 4), (3, 6)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 3), (1, 6), (1, 4)]))
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 4), (3, 6)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 4), (2, 5)]))
                        )
                      )
                    )
                    (.node 5 6   -- 6
                      (.node 0 5   -- 3
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 3), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 4), (2, 5)]))
                        )
                        (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 3), (0, 6), (0, 4)]))
                      )
                      (.node 2 5   -- 3
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (3, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (3, 6)]))
                        )
                        (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 4), (3, 6)]))
                      )
                    )
                  )
                  (.node 1 5   -- 17
                    (.node 0 4   -- 9
                      (.node 2 5   -- 3
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 6), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 2), (1, 4)]))
                        )
                        (.leaf (swapProd [(1, 3), (1, 6), (1, 2), (1, 5), (1, 4)]))
                      )
                      (.node 0 6   -- 6
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 6), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 2), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 2), (0, 5), (0, 4)]))
                        )
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (1, 3), (1, 5), (1, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (1, 3), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (1, 3), (1, 6)]))
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 0 5   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 4), (2, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (2, 5), (3, 6)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 5), (0, 1), (0, 4)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 4), (2, 5), (2, 3), (2, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (2, 5), (2, 3), (2, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 6), (0, 1), (0, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 4), (2, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 34
                  (.node 2 5   -- 17
                    (.node 0 4   -- 9
                      (.node 1 5   -- 3
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 4), (2, 3), (2, 5), (2, 6)]))
                          (.leaf (swapProd [(1, 4), (2, 3), (2, 6)]))
                        )
                        (.leaf (swapProd [(1, 5), (1, 4), (2, 3), (2, 6)]))
                      )
                      (.node 0 6   -- 6
                        (.node 1 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (2, 3), (2, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (2, 3), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (2, 3), (2, 6)]))
                        )
                        (.node 1 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 6), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 1), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 1), (0, 5), (0, 4)]))
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 0 5   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 5), (1, 2), (1, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 4), (3, 6)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (1, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 4), (1, 5)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 5), (1, 3), (1, 6), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 6), (0, 2), (0, 4)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (1, 5), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 5), (0, 2), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 2 5   -- 17
                    (.node 0 4   -- 9
                      (.node 1 5   -- 3
                        (.leaf (swapProd [(1, 5), (1, 6), (1, 2), (1, 3), (1, 4)]))
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 3), (1, 5), (1, 4)]))
                        )
                      )
                      (.node 0 6   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 2), (0, 3), (0, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 3), (0, 5), (0, 4)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (1, 5), (1, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (1, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 4), (1, 6)]))
                          )
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 0 5   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 6), (1, 3), (1, 5), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 5), (0, 2), (0, 4)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (1, 6), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 6), (0, 2), (0, 4)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 4), (3, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 4), (3, 5)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (1, 6), (3, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 4), (1, 6)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 3 5   -- 81
                (.node 0 6   -- 37
                  (.node 1 4   -- 18
                    (.node 3 4   -- 9
                      (.node 1 2   -- 4
                        (.node 1 6   -- 2
                          (.leaf (swapProd [(2, 3), (2, 4), (2, 5), (2, 6)]))
                          (.leaf (swapProd [(1, 2), (1, 3), (1, 4), (1, 5), (1, 6)]))
                        )
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 5), (1, 6)]))
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 6)]))
                        )
                      )
                      (.node 1 6   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(2, 3), (2, 5), (2, 6)]))
                          (.leaf (swapProd [(2, 4), (2, 3), (2, 5), (2, 6)]))
                        )
                        (.node 1 2   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 5), (1, 6)]))
                            (.leaf (swapProd [(1, 2), (1, 4), (1, 3), (1, 5), (1, 6)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 6)]))
                        )
                      )
                    )
                    (.node 2 4   -- 9
                      (.node 1 5   -- 5
                        (.node 1 3   -- 3
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 5), (1, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 5), (1, 6)]))
                            (.leaf (swapProd [(1, 5), (1, 6), (3, 4)]))
                          )
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 6)]))
                          (.leaf (swapProd [(1, 6), (3, 4)]))
                        )
                      )
                      (.node 1 3   -- 4
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 6), (2, 4)]))
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 3), (1, 5), (1, 6)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 5), (1, 6), (2, 3), (2, 4)]))
                          (.leaf (swapProd [(1, 6), (2, 3), (2, 4)]))
                        )
                      )
                    )
                  )
                  (.node 1 3   -- 19
                    (.node 1 2   -- 10
                      (.node 1 4   -- 5
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 5), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 3), (0, 5), (0, 6)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 6), (2, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 3), (0, 5), (0, 6)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 6)]))
                        )
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 3), (0, 5), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 6), (1, 4)]))
                        )
                      )
                    )
                    (.node 1 5   -- 9
                      (.node 2 4   -- 5
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (3, 4)]))
                          )
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (2, 3), (2, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 1), (0, 5), (0, 6)]))
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (3, 4)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6), (2, 3), (2, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 1), (0, 6)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 5   -- 44
                  (.node 0 6   -- 22
                    (.node 1 4   -- 11
                      (.node 1 6   -- 7
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(2, 3), (2, 6)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(2, 4), (2, 3), (2, 6)]))
                            (.leaf (swapProd [(2, 5), (2, 4), (2, 3), (2, 6)]))
                          )
                        )
                        (.node 2 4   -- 4
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(1, 3), (1, 6)]))
                          )
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(1, 2), (1, 4), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 4), (1, 3), (1, 6)]))
                          )
                        )
                      )
                      (.node 1 2   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 3), (1, 6), (2, 4)]))
                          (.leaf (swapProd [(1, 3), (1, 6), (2, 5), (2, 4)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 3), (1, 6)]))
                        )
                      )
                    )
                    (.node 1 2   -- 11
                      (.node 1 4   -- 7
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 6)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 3), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 4), (0, 3), (0, 6)]))
                          )
                        )
                        (.node 0 4   -- 4
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (2, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (2, 5), (2, 4)]))
                          )
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 3), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 1), (0, 3), (0, 6)]))
                          )
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 6)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 3), (0, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (1, 4)]))
                        )
                      )
                    )
                  )
                  (.node 2 5   -- 22
                    (.node 1 3   -- 10
                      (.node 0 6   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 5), (1, 4), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(1, 5), (1, 4), (1, 2), (1, 3), (1, 6)]))
                        )
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 3), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 2), (0, 3), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (1, 5), (1, 4)]))
                        )
                      )
                      (.node 0 6   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 6), (3, 5), (3, 4)]))
                          (.leaf (swapProd [(1, 6), (2, 3), (2, 5), (2, 4)]))
                        )
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (3, 5), (3, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (2, 3), (2, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 4), (0, 1), (0, 6)]))
                        )
                      )
                    )
                    (.node 0 4   -- 12
                      (.node 0 6   -- 6
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 5), (1, 3), (1, 6)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(1, 5), (1, 3), (1, 6), (2, 4)]))
                            (.leaf (swapProd [(1, 6), (2, 4), (3, 5)]))
                          )
                        )
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 5), (0, 3), (0, 6)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 6), (2, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (2, 4), (3, 5)]))
                          )
                        )
                      )
                      (.node 0 5   -- 6
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 6), (1, 4)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 5), (0, 3), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 6), (3, 5)]))
                          )
                        )
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 3), (0, 6), (1, 4), (2, 5)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (1, 5), (1, 2), (1, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 4), (0, 1), (0, 6)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree72 : Tree 7 :=
          (.node 2 6   -- 315
            tree70
            tree71
          )

private def tree73 : Tree 7 :=
            (.node 3 6   -- 168
              (.node 1 3   -- 84
                (.node 1 2   -- 42
                  (.node 1 5   -- 21
                    (.node 2 5   -- 10
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(4, 6), (4, 5)]))
                            (.leaf (swapProd [(4, 6)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(3, 4), (3, 5)]))
                            (.leaf (swapProd [(3, 4), (3, 6), (3, 5)]))
                          )
                          (.leaf (swapProd [(3, 5)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(2, 3), (2, 4), (2, 5)]))
                          (.leaf (swapProd [(2, 3), (2, 4), (2, 6), (2, 5)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(2, 3), (2, 5)]))
                          (.leaf (swapProd [(2, 4), (2, 3), (2, 5)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 2 4   -- 5
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 4), (1, 6), (1, 5)]))
                          )
                          (.leaf (swapProd [(1, 2), (1, 3), (1, 5)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(1, 3), (1, 5), (2, 4)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 5)]))
                        )
                        (.node 0 4   -- 3
                          (.node 1 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 3), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 5   -- 21
                    (.node 1 5   -- 10
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 2), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (4, 6), (4, 5)]))
                            (.leaf (swapProd [(1, 2), (4, 6)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 2), (3, 4), (3, 5)]))
                            (.leaf (swapProd [(1, 2), (3, 4), (3, 6), (3, 5)]))
                          )
                          (.leaf (swapProd [(1, 2), (3, 5)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 5), (1, 2)]))
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 6), (1, 5), (1, 2)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 2)]))
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 5), (1, 2)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 1 4   -- 5
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 3), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(1, 3), (1, 4), (1, 6), (1, 5)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 5)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 3), (1, 5)]))
                        )
                      )
                      (.node 1 4   -- 6
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5)]))
                        )
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 3), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (1, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 6   -- 42
                  (.node 1 4   -- 21
                    (.node 3 5   -- 11
                      (.node 1 5   -- 5
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 3), (1, 2), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 3), (1, 2), (4, 6), (4, 5)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (4, 6)]))
                          )
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 3), (1, 2)]))
                          (.leaf (swapProd [(1, 4), (1, 6), (1, 5), (1, 3), (1, 2)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(1, 4), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(1, 4), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5)]))
                        )
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(1, 4), (1, 6), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(1, 4), (1, 6), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 5)]))
                        )
                      )
                    )
                    (.node 0 5   -- 10
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
                  (.node 2 5   -- 21
                    (.node 1 4   -- 10
                      (.node 5 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 5), (1, 3), (1, 2), (4, 6)]))
                          (.leaf (swapProd [(1, 5), (1, 2), (4, 6)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 4), (1, 6), (1, 3), (1, 2)]))
                          (.leaf (swapProd [(1, 5), (1, 4), (1, 6), (1, 3), (1, 2)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 6), (1, 5), (1, 3), (1, 2)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 5), (1, 3), (1, 2)]))
                            (.leaf (swapProd [(1, 6), (1, 3), (1, 2), (4, 5)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 5), (1, 2)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 5), (1, 2), (3, 4)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 3 4   -- 5
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(1, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 5)]))
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 5)]))
                          )
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 6), (1, 5), (3, 4)]))
                          (.leaf (swapProd [(1, 6), (1, 5), (2, 3), (2, 4)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 5)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (3, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (2, 3), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 1), (0, 6), (0, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 6   -- 84
                (.node 1 2   -- 42
                  (.node 1 5   -- 21
                    (.node 2 5   -- 10
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(3, 4), (3, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(3, 5), (4, 6)]))
                            (.leaf (swapProd [(3, 5), (3, 4), (3, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(3, 6), (3, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(3, 6), (3, 4), (3, 5)]))
                            (.leaf (swapProd [(3, 6), (4, 5)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(2, 3), (2, 6), (2, 5)]))
                          (.leaf (swapProd [(2, 4), (2, 3), (2, 6), (2, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(2, 3), (2, 5), (4, 6)]))
                          (.leaf (swapProd [(2, 3), (2, 6), (2, 4), (2, 5)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 2 4   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(1, 2), (1, 3), (1, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 6), (1, 4), (1, 5)]))
                          )
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 3), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 5), (2, 4)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 6), (0, 4), (0, 5)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.node 1 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 3), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 3), (0, 6), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 5   -- 21
                    (.node 1 5   -- 10
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(1, 2), (3, 4), (3, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (3, 5), (4, 6)]))
                            (.leaf (swapProd [(1, 2), (3, 5), (3, 4), (3, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 2), (3, 6), (3, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (3, 6), (3, 4), (3, 5)]))
                            (.leaf (swapProd [(1, 2), (3, 6), (4, 5)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 5), (1, 2)]))
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 6), (1, 5), (1, 2)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 2), (4, 6)]))
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 4), (1, 5), (1, 2)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 1 4   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(1, 3), (1, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 3), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(1, 3), (1, 6), (1, 4), (1, 5)]))
                          )
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 3), (1, 6), (1, 5)]))
                        )
                      )
                      (.node 1 4   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 4), (0, 5)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 3), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 5), (1, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 42
                  (.node 1 4   -- 21
                    (.node 3 4   -- 11
                      (.node 5 6   -- 6
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(1, 4), (1, 6), (1, 3), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(1, 4), (1, 6), (1, 3), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 3), (0, 5)]))
                        )
                        (.node 1 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 3), (1, 4), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(1, 3), (1, 5), (1, 4), (1, 6), (1, 2)]))
                          )
                          (.leaf (swapProd [(1, 4), (1, 6), (1, 2), (3, 5)]))
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 2), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 4), (1, 5), (1, 2), (3, 6)]))
                            (.leaf (swapProd [(1, 4), (1, 5), (1, 3), (1, 6), (1, 2)]))
                          )
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 4), (1, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (3, 6)]))
                        )
                      )
                    )
                    (.node 0 5   -- 10
                      (.node 2 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 5), (1, 2), (3, 6), (3, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 5), (1, 2), (3, 6)]))
                            (.leaf (swapProd [(1, 5), (1, 3), (1, 6), (1, 2)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 5), (3, 6), (3, 4)]))
                            (.leaf (swapProd [(1, 5), (3, 6)]))
                          )
                          (.leaf (swapProd [(1, 5), (2, 3), (2, 6), (2, 4)]))
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (3, 6), (3, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (3, 6)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 3), (2, 6), (2, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 4), (0, 1), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 5   -- 21
                    (.node 1 4   -- 10
                      (.node 3 5   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 4), (1, 6), (1, 2)]))
                          (.leaf (swapProd [(1, 5), (1, 4), (1, 6), (1, 2)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(1, 5), (1, 2), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(1, 5), (1, 3), (1, 4), (1, 6), (1, 2)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(1, 6), (1, 2), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 3), (1, 4), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(1, 6), (1, 2), (3, 4), (3, 5)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 6), (1, 4), (1, 3), (1, 5), (1, 2)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 3), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(1, 6), (1, 2), (3, 5)]))
                          )
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 3 4   -- 5
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 5), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(1, 6), (1, 3), (1, 4), (1, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 3), (1, 5)]))
                            (.leaf (swapProd [(1, 6), (1, 3), (1, 5)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 4), (1, 2), (1, 3), (1, 5)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 2), (0, 3), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (1, 6), (1, 4)]))
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (3, 4), (3, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 5)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree74 : Tree 7 :=
            (.node 5 6   -- 147
              (.node 1 2   -- 66
                (.node 1 6   -- 32
                  (.node 0 5   -- 15
                    (.node 1 5   -- 9
                      (.node 2 4   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(2, 4), (2, 6), (2, 3), (2, 5)]))
                          (.leaf (swapProd [(2, 4), (2, 5), (3, 6)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(2, 5), (3, 6), (3, 4)]))
                          (.leaf (swapProd [(2, 5), (3, 6)]))
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 6), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 5), (3, 6)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 5), (3, 6), (3, 4)]))
                            (.leaf (swapProd [(1, 2), (1, 5), (3, 6)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 4), (1, 2), (1, 5)]))
                        )
                      )
                    )
                    (.node 4 6   -- 6
                      (.node 0 4   -- 3
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (3, 6), (3, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 4), (0, 2), (0, 5)]))
                        )
                        (.leaf (swapProd [(0, 2), (0, 5), (1, 3), (1, 6), (1, 4)]))
                      )
                      (.node 2 4   -- 3
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 6), (0, 3), (0, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 5), (3, 6)]))
                        )
                        (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (3, 6)]))
                      )
                    )
                  )
                  (.node 1 4   -- 17
                    (.node 0 5   -- 9
                      (.node 2 4   -- 3
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 3), (1, 5), (2, 4), (2, 6)]))
                          (.leaf (swapProd [(1, 3), (1, 6), (1, 2), (1, 4), (1, 5)]))
                        )
                        (.leaf (swapProd [(1, 3), (1, 6), (1, 2), (1, 5)]))
                      )
                      (.node 0 6   -- 6
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (2, 4), (2, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 2), (0, 4), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 2), (0, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 1), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (1, 3), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 3), (1, 6)]))
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 0 4   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 5), (3, 6)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 5), (1, 4)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 6), (1, 2), (1, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 6), (0, 2), (0, 5)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 4), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 4), (0, 2), (0, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 34
                  (.node 2 4   -- 17
                    (.node 0 5   -- 9
                      (.node 1 4   -- 3
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 4), (1, 6), (1, 2), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(1, 4), (1, 5), (2, 3), (2, 6)]))
                        )
                        (.leaf (swapProd [(1, 5), (2, 3), (2, 6)]))
                      )
                      (.node 0 6   -- 6
                        (.node 1 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 2), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (2, 3), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 3), (2, 6)]))
                        )
                        (.node 1 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (1, 4), (1, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 1), (0, 4), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 1), (0, 5)]))
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 0 4   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 5), (2, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 4), (3, 6)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 4), (0, 1), (0, 5)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 5), (2, 4), (2, 3), (2, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 4), (2, 3), (2, 6)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 6), (0, 1), (0, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 5), (2, 4)]))
                        )
                      )
                    )
                  )
                  (.node 2 4   -- 17
                    (.node 0 5   -- 9
                      (.node 1 4   -- 3
                        (.leaf (swapProd [(1, 5), (2, 3), (2, 4), (2, 6)]))
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 3), (1, 4), (1, 5)]))
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 3), (1, 5)]))
                        )
                      )
                      (.node 0 6   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 3), (2, 4), (2, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 3), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 3), (0, 5)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 6), (0, 1), (0, 5)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 5), (1, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (1, 6)]))
                          )
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 0 4   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 6), (1, 3), (1, 5), (2, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 5), (2, 4)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 6), (0, 3), (0, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (1, 6), (1, 2), (1, 4)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 4), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 4), (0, 3), (0, 5)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 5), (1, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (1, 6), (2, 4)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 3 4   -- 81
                (.node 0 6   -- 37
                  (.node 1 5   -- 18
                    (.node 3 5   -- 9
                      (.node 1 2   -- 4
                        (.node 1 6   -- 2
                          (.leaf (swapProd [(2, 3), (2, 4), (2, 6)]))
                          (.leaf (swapProd [(1, 2), (1, 3), (1, 4), (1, 6)]))
                        )
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 6)]))
                          (.leaf (swapProd [(1, 4), (1, 6)]))
                        )
                      )
                      (.node 1 6   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(2, 3), (2, 5), (2, 4), (2, 6)]))
                          (.leaf (swapProd [(2, 4), (2, 6), (3, 5)]))
                        )
                        (.node 1 2   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 5), (1, 4), (1, 6)]))
                            (.leaf (swapProd [(1, 2), (1, 4), (1, 6), (3, 5)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 4), (1, 6)]))
                        )
                      )
                    )
                    (.node 2 5   -- 9
                      (.node 1 4   -- 5
                        (.node 1 3   -- 3
                          (.leaf (swapProd [(1, 4), (1, 6), (3, 5)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 5), (1, 4), (1, 6)]))
                            (.leaf (swapProd [(1, 5), (1, 3), (1, 4), (1, 6)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 6), (4, 5)]))
                          (.leaf (swapProd [(1, 6), (3, 4), (3, 5)]))
                        )
                      )
                      (.node 1 3   -- 4
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 2), (1, 4), (1, 6)]))
                          (.leaf (swapProd [(1, 4), (1, 6), (2, 3), (2, 5)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 5), (1, 2), (1, 3), (1, 4), (1, 6)]))
                          (.leaf (swapProd [(1, 6), (2, 3), (2, 4), (2, 5)]))
                        )
                      )
                    )
                  )
                  (.node 1 3   -- 19
                    (.node 1 2   -- 10
                      (.node 1 5   -- 5
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 5), (0, 4), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 6), (3, 5)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 2), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (1, 3), (1, 5)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 4), (0, 6)]))
                        )
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (2, 3), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 1), (0, 4), (0, 6)]))
                        )
                      )
                    )
                    (.node 1 4   -- 9
                      (.node 2 5   -- 5
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 4), (0, 6)]))
                          )
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 3), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 6), (1, 5)]))
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (3, 4), (3, 5)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6), (2, 3), (2, 4), (2, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 5), (0, 1), (0, 6)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 4   -- 44
                  (.node 0 6   -- 22
                    (.node 1 5   -- 11
                      (.node 1 6   -- 7
                        (.node 2 4   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(2, 3), (2, 6), (4, 5)]))
                            (.leaf (swapProd [(2, 4), (2, 5), (2, 3), (2, 6)]))
                          )
                          (.leaf (swapProd [(2, 5), (2, 3), (2, 6)]))
                        )
                        (.node 2 5   -- 4
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(1, 2), (1, 3), (1, 6), (4, 5)]))
                            (.leaf (swapProd [(1, 3), (1, 6), (4, 5)]))
                          )
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(1, 2), (1, 4), (1, 5), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 3), (1, 6)]))
                          )
                        )
                      )
                      (.node 1 2   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 3), (1, 6), (2, 4), (2, 5)]))
                          (.leaf (swapProd [(1, 3), (1, 6), (2, 5)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 2), (1, 3), (1, 6)]))
                        )
                      )
                    )
                    (.node 1 2   -- 11
                      (.node 1 5   -- 7
                        (.node 2 4   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (0, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 5), (0, 3), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 3), (0, 6)]))
                        )
                        (.node 0 5   -- 4
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (2, 4), (2, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (2, 5)]))
                          )
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 1), (0, 3), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 3), (0, 6)]))
                          )
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 3), (0, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 2), (0, 3), (0, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (1, 4), (1, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 4   -- 22
                    (.node 1 3   -- 10
                      (.node 0 6   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 5), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(1, 5), (1, 2), (1, 3), (1, 6)]))
                        )
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 3), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (1, 5)]))
                        )
                      )
                      (.node 0 6   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 6), (3, 5)]))
                          (.leaf (swapProd [(1, 6), (2, 3), (2, 5)]))
                        )
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (2, 3), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 1), (0, 6)]))
                        )
                      )
                    )
                    (.node 0 5   -- 12
                      (.node 0 6   -- 6
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 6), (2, 5)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(1, 5), (1, 2), (1, 4), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(1, 6), (2, 4), (2, 3), (2, 5)]))
                          )
                        )
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 6), (2, 5)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 4), (0, 3), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (2, 4), (2, 3), (2, 5)]))
                          )
                        )
                      )
                      (.node 0 4   -- 6
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 4), (0, 3), (0, 6)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 5), (0, 1), (0, 6)]))
                          )
                        )
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 3), (0, 6), (1, 4), (1, 2), (1, 5)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (1, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 6), (2, 4)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree75 : Tree 7 :=
          (.node 2 6   -- 315
            tree73
            tree74
          )

private def tree76 : Tree 7 :=
        (.node 4 5   -- 630
          tree72
          tree75
        )

private def tree77 : Tree 7 :=
            (.node 1 6   -- 168
              (.node 1 3   -- 84
                (.node 3 6   -- 42
                  (.node 0 4   -- 21
                    (.node 1 4   -- 10
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (4, 5), (4, 6)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (3, 5), (3, 4)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 2), (5, 6)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (3, 5)]))
                        )
                      )
                    )
                    (.node 1 5   -- 11
                      (.node 2 4   -- 6
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 2), (1, 3), (1, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (1, 3), (1, 5), (1, 4)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 5), (0, 4)]))
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 2), (1, 4), (3, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (3, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (1, 4)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 4)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 1 4   -- 10
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (3, 4), (3, 5), (3, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 5), (3, 6), (3, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 5), (3, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 6), (3, 5), (3, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 6), (3, 4)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (3, 6)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 5), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (3, 6), (3, 5)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 6), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 4), (0, 2)]))
                        )
                      )
                    )
                    (.node 1 5   -- 11
                      (.node 2 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 2), (1, 3), (1, 5), (1, 6), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 3), (1, 6), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(0, 2), (1, 3), (1, 6), (1, 4)]))
                          )
                        )
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 5), (0, 6), (0, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 6), (0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 6), (0, 4)]))
                          )
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 2), (1, 4), (3, 6), (3, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (3, 6), (3, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 2), (1, 4)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 2), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 1), (0, 4)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 0 3   -- 42
                  (.node 0 4   -- 21
                    (.node 3 4   -- 10
                      (.node 1 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (4, 5), (4, 6)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 2), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 3), (0, 2)]))
                        )
                      )
                      (.node 1 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (5, 6)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 4), (0, 2)]))
                        )
                      )
                    )
                    (.node 2 4   -- 11
                      (.node 1 5   -- 5
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 2), (1, 4)]))
                          (.leaf (swapProd [(0, 2), (1, 4), (5, 6)]))
                        )
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(0, 2), (1, 5), (1, 3), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 5), (0, 2)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 4)]))
                        )
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 3), (0, 4)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (1, 5)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 21
                    (.node 0 4   -- 11
                      (.node 1 4   -- 5
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (1, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (1, 3), (4, 5), (4, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 3)]))
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 3), (5, 6)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 4)]))
                        )
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 2), (5, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (1, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 4), (5, 6)]))
                        )
                      )
                    )
                    (.node 0 5   -- 10
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
              )
              (.node 3 6   -- 84
                (.node 0 3   -- 42
                  (.node 0 4   -- 21
                    (.node 1 5   -- 10
                      (.node 4 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 4), (0, 3), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 4), (0, 2)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 6), (0, 3), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 3), (0, 2)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 4), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 3), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 2)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 3), (0, 4), (0, 2)]))
                        )
                      )
                    )
                    (.node 2 4   -- 11
                      (.node 3 5   -- 5
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (1, 5), (1, 6), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 4)]))
                          )
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 2), (1, 6), (1, 5), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 6), (0, 5), (0, 2)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 6), (0, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 4)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 5), (0, 3), (0, 4)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (1, 6), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (1, 6), (1, 5)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 3 4   -- 21
                    (.node 0 4   -- 10
                      (.node 1 5   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 5), (1, 6), (1, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 5), (1, 6), (1, 4), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (1, 5), (1, 6), (1, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 5), (1, 4), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 4), (1, 3)]))
                          )
                          (.leaf (swapProd [(0, 2), (1, 6), (1, 3)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 5), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (1, 6), (1, 5), (1, 3)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 6), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 4), (0, 2)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 2 4   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 2), (1, 5), (1, 6), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (1, 6), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (1, 6), (1, 4)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 5), (0, 6), (0, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 6), (0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 6), (0, 4)]))
                          )
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 5), (0, 3), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 5), (0, 2)]))
                        )
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (1, 6), (1, 5), (1, 3), (1, 2)]))
                            (.leaf (swapProd [(0, 4), (1, 6), (1, 5), (1, 2)]))
                          )
                          (.leaf (swapProd [(0, 4), (1, 6), (1, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 42
                  (.node 0 4   -- 21
                    (.node 3 5   -- 10
                      (.node 1 4   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 6), (0, 2)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (3, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 5), (0, 6), (0, 2)]))
                        )
                      )
                      (.node 1 5   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 2)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (3, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 6), (0, 2)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 6), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 2), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 3), (0, 6), (0, 2)]))
                        )
                      )
                    )
                    (.node 2 4   -- 11
                      (.node 1 5   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (1, 4), (3, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 2), (1, 4), (3, 6)]))
                        )
                        (.node 0 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 5), (1, 3), (1, 6), (1, 4)]))
                            (.leaf (swapProd [(0, 2), (1, 5), (1, 4), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 1), (0, 5), (0, 2)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 3), (0, 6), (0, 4)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (1, 5)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (3, 5), (3, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 4), (3, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 1 5   -- 10
                      (.node 3 4   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 2)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 3), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 2), (3, 4)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 2)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (3, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 2), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 5), (0, 4), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (3, 5), (3, 4)]))
                        )
                      )
                    )
                    (.node 2 4   -- 11
                      (.node 3 5   -- 5
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 2), (1, 5), (1, 6), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 2), (1, 6), (1, 3), (1, 4)]))
                        )
                        (.node 0 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 4), (3, 5)]))
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 3), (1, 5), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (1, 6), (1, 4)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 4), (3, 5)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 1), (0, 6), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 6), (0, 4)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 6), (0, 3), (0, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 3), (0, 5), (0, 4)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree78 : Tree 7 :=
            (.node 4 6   -- 147
              (.node 0 3   -- 66
                (.node 1 3   -- 34
                  (.node 0 5   -- 17
                    (.node 1 5   -- 9
                      (.node 3 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 2), (1, 4)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 2), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 1), (0, 4)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (1, 4)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 4)]))
                          )
                        )
                      )
                      (.node 2 4   -- 3
                        (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (1, 5), (1, 4)]))
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 1), (0, 5), (0, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 5), (0, 4)]))
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 2 5   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 2), (3, 6)]))
                          (.leaf (swapProd [(0, 4), (1, 5), (1, 2), (3, 6)]))
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 4), (1, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 4), (1, 5), (2, 3), (2, 6)]))
                        )
                      )
                      (.node 2 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 3), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (1, 5), (1, 3), (1, 6), (1, 2)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 4), (1, 5), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 4), (1, 5), (1, 2), (1, 3), (1, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 17
                    (.node 1 5   -- 9
                      (.node 2 4   -- 3
                        (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 5), (0, 6), (0, 2)]))
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (1, 5), (1, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (1, 5), (1, 6)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 6), (0, 2)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (1, 6)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 1), (0, 6), (0, 2)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (1, 6)]))
                          )
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 2 5   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 3), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (1, 6), (1, 3), (1, 5), (1, 2)]))
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 4), (1, 6), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (1, 6), (1, 2), (1, 3), (1, 5)]))
                        )
                      )
                      (.node 2 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 2), (3, 5)]))
                          (.leaf (swapProd [(0, 4), (1, 6), (1, 2), (3, 5)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 4), (1, 6), (3, 5)]))
                          (.leaf (swapProd [(0, 4), (1, 6), (2, 3), (2, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 3 6   -- 32
                  (.node 0 5   -- 15
                    (.node 1 5   -- 6
                      (.node 2 4   -- 3
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (1, 5), (1, 6), (1, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 6), (0, 3), (0, 2)]))
                        )
                        (.leaf (swapProd [(0, 4), (1, 5), (1, 6), (1, 3), (1, 2)]))
                      )
                      (.node 2 4   -- 3
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (1, 6), (1, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 3), (0, 2)]))
                        )
                        (.leaf (swapProd [(0, 4), (1, 6), (1, 3), (1, 2)]))
                      )
                    )
                    (.node 2 4   -- 9
                      (.node 3 4   -- 5
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 6), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (1, 6), (1, 3)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (1, 6), (1, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 6), (0, 3), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (1, 6), (1, 4)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 1), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 6), (1, 3), (1, 2)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 3 5   -- 17
                    (.node 0 5   -- 9
                      (.node 1 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 6), (0, 2)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 5), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 4), (1, 5), (1, 6)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 2)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 4), (1, 6)]))
                          )
                        )
                      )
                      (.node 2 4   -- 3
                        (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 6), (0, 2)]))
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 6)]))
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 2 5   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (1, 6), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 6), (0, 3), (0, 4)]))
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 3), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 2), (0, 3), (0, 4)]))
                        )
                      )
                      (.node 2 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 1), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (1, 6), (1, 2)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 4), (1, 6)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 5   -- 81
                (.node 2 6   -- 37
                  (.node 3 4   -- 18
                    (.node 1 4   -- 9
                      (.node 0 3   -- 4
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(0, 2), (1, 3), (1, 4), (1, 5), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 5), (1, 6)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 5), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (1, 4), (1, 5), (1, 6)]))
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 0 3   -- 3
                          (.leaf (swapProd [(0, 2), (1, 5), (1, 6)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (1, 5), (1, 6)]))
                          )
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 5), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (1, 5), (1, 6)]))
                        )
                      )
                    )
                    (.node 0 4   -- 9
                      (.node 1 4   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (1, 3), (1, 5), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (1, 3), (1, 6)]))
                        )
                        (.node 1 3   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (1, 4), (1, 3), (1, 5), (1, 6)]))
                            (.leaf (swapProd [(0, 2), (1, 4), (1, 3), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (1, 5), (1, 6), (3, 4)]))
                        )
                      )
                      (.node 1 3   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 1), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 4), (0, 2)]))
                        )
                        (.node 0 3   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (1, 5), (1, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (1, 5), (1, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 19
                    (.node 1 3   -- 10
                      (.node 1 4   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 4), (0, 5), (0, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 6)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 3), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 3), (0, 6)]))
                        )
                      )
                      (.node 0 3   -- 5
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 5), (0, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 6), (3, 4)]))
                          )
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 4), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 5), (0, 6)]))
                        )
                      )
                    )
                    (.node 1 3   -- 9
                      (.node 2 4   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (1, 4), (1, 2)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (1, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (1, 4)]))
                        )
                      )
                      (.node 0 3   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 1), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 5), (0, 6)]))
                        )
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 1), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 5), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 6)]))
                        )
                      )
                    )
                  )
                )
                (.node 3 5   -- 44
                  (.node 2 6   -- 22
                    (.node 0 4   -- 11
                      (.node 0 3   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (1, 6), (3, 4)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (1, 6)]))
                        )
                      )
                      (.node 0 5   -- 7
                        (.node 3 4   -- 4
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (1, 6)]))
                          )
                          (.node 0 3   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (1, 6)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 1), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 2), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (1, 6)]))
                        )
                      )
                    )
                    (.node 0 3   -- 11
                      (.node 0 4   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (3, 4)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 1), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 6)]))
                        )
                      )
                      (.node 0 5   -- 7
                        (.node 3 4   -- 4
                          (.node 0 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 1), (0, 6)]))
                          )
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 6)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 2), (0, 1), (0, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 22
                    (.node 1 3   -- 10
                      (.node 0 4   -- 5
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 2), (1, 5), (1, 4), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 4), (0, 3), (0, 6)]))
                        )
                        (.node 2 4   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 5), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (1, 5), (1, 4), (1, 2)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (1, 5), (1, 4)]))
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 2), (1, 6), (3, 5), (3, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (3, 5), (3, 4)]))
                        )
                        (.node 2 4   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 2), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 1), (0, 6)]))
                        )
                      )
                    )
                    (.node 2 4   -- 12
                      (.node 2 6   -- 6
                        (.node 0 3   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (1, 5), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (1, 6), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 2), (1, 6)]))
                        )
                        (.node 0 3   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 5), (0, 3), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 6), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 2), (0, 1), (0, 6)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 0 3   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 3), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 1), (0, 6)]))
                        )
                        (.node 0 3   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 2), (0, 3), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (2, 3), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 4), (0, 1), (0, 6)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree79 : Tree 7 :=
          (.node 0 6   -- 315
            tree77
            tree78
          )

private def tree710 : Tree 7 :=
            (.node 1 6   -- 168
              (.node 1 3   -- 84
                (.node 3 6   -- 42
                  (.node 0 5   -- 21
                    (.node 1 5   -- 10
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (4, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (4, 6)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 4), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 4), (3, 6), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (3, 5)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 6), (0, 5), (0, 2)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 5), (0, 2)]))
                        )
                      )
                    )
                    (.node 1 4   -- 11
                      (.node 2 5   -- 6
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 3), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 2), (1, 3), (1, 4), (1, 6), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (1, 3), (1, 5)]))
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 4), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 5)]))
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 3), (0, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (1, 4), (1, 2)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 5), (1, 4)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 1 5   -- 10
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (3, 4), (3, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 5), (4, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 5), (3, 4), (3, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (3, 6), (3, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 6), (3, 4), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (3, 6), (4, 5)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 6), (0, 5), (0, 2)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 2), (4, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 4), (0, 5), (0, 2)]))
                        )
                      )
                    )
                    (.node 1 4   -- 11
                      (.node 2 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 2), (1, 3), (1, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 3), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 2), (1, 3), (1, 6), (1, 4), (1, 5)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 6), (0, 4), (0, 5)]))
                          )
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 3), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 3), (0, 6), (0, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 1), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (1, 4), (1, 2)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (1, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 0 3   -- 42
                  (.node 0 5   -- 21
                    (.node 3 5   -- 10
                      (.node 1 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (4, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (4, 6)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 5), (0, 3), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 2)]))
                        )
                      )
                      (.node 1 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 5), (0, 2)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (3, 4)]))
                        )
                      )
                    )
                    (.node 2 5   -- 11
                      (.node 1 4   -- 5
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 5)]))
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 6), (1, 5)]))
                        )
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (1, 5)]))
                            (.leaf (swapProd [(0, 2), (1, 5), (3, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (1, 5)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5)]))
                        )
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (3, 4)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 1), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 5)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 21
                    (.node 0 5   -- 11
                      (.node 1 5   -- 5
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 2), (1, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 3), (4, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 2), (1, 3), (4, 6)]))
                          )
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 5), (1, 3)]))
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 6), (1, 5), (1, 3)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (1, 4), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 4), (0, 5)]))
                        )
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 6), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (1, 4), (1, 6), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 4), (0, 6), (0, 5)]))
                        )
                      )
                    )
                    (.node 0 4   -- 10
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
              (.node 3 6   -- 84
                (.node 0 3   -- 42
                  (.node 0 5   -- 21
                    (.node 1 4   -- 10
                      (.node 5 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 2), (4, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (4, 6)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 3), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 6), (0, 3), (0, 2)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 3), (0, 2)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 5), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 2), (4, 5)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 5), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 2), (3, 4)]))
                        )
                      )
                    )
                    (.node 2 5   -- 11
                      (.node 3 4   -- 5
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (1, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 4), (1, 5)]))
                          )
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 2), (1, 6), (1, 5), (3, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (1, 6), (1, 5)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 4), (0, 5)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 5), (3, 4)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 1), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 6), (0, 5)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 3 5   -- 21
                    (.node 0 5   -- 10
                      (.node 1 4   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 6), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 5), (1, 3), (4, 6)]))
                            (.leaf (swapProd [(0, 2), (1, 5), (1, 4), (1, 6), (1, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 2), (1, 6), (1, 5), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 4), (1, 5), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 3), (4, 5)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 6), (0, 5), (0, 2)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 2), (4, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 4), (0, 5), (0, 2)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 2 5   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 2), (1, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (1, 6), (1, 4), (1, 5)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 6), (0, 4), (0, 5)]))
                          )
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (1, 6), (1, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 1), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 42
                  (.node 0 5   -- 21
                    (.node 3 4   -- 10
                      (.node 1 5   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 4), (0, 6), (0, 2)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 3), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 2), (3, 5)]))
                        )
                      )
                      (.node 1 4   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 6), (0, 2), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 2), (3, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 3), (0, 6), (0, 2)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (3, 6), (3, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (3, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 6), (0, 2)]))
                          )
                        )
                      )
                    )
                    (.node 2 5   -- 11
                      (.node 1 4   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 6), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 5), (3, 6)]))
                        )
                        (.node 0 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 5), (3, 6), (3, 4)]))
                            (.leaf (swapProd [(0, 2), (1, 5), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 2), (1, 5)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (3, 6), (3, 4)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 2), (0, 1), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 1), (0, 5)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 6), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 5), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (3, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 1 4   -- 10
                      (.node 3 5   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 6), (0, 2)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 4), (0, 6), (0, 2)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 4), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (3, 4), (3, 5)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 3), (0, 5), (0, 2)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (3, 5)]))
                          )
                        )
                      )
                    )
                    (.node 2 5   -- 11
                      (.node 3 4   -- 5
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 2), (1, 5), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 2), (1, 6), (1, 3), (1, 4), (1, 5)]))
                        )
                        (.node 0 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 4), (1, 3), (1, 5)]))
                            (.leaf (swapProd [(0, 2), (1, 6), (1, 3), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 6), (0, 4), (0, 2)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 4), (0, 3), (0, 5)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (1, 6), (1, 4), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (1, 6), (1, 4)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (3, 4), (3, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 3), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 3), (0, 5)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree711 : Tree 7 :=
            (.node 5 6   -- 147
              (.node 0 3   -- 66
                (.node 1 3   -- 34
                  (.node 0 4   -- 17
                    (.node 1 4   -- 9
                      (.node 3 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 4), (0, 6), (0, 2)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (1, 4), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (1, 4), (1, 6)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (1, 4), (1, 5)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 1), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 4), (0, 5)]))
                          )
                        )
                      )
                      (.node 2 5   -- 3
                        (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (1, 5)]))
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 1), (0, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 5)]))
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 2 4   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (1, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 5), (3, 6)]))
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (2, 3), (2, 6)]))
                        )
                      )
                      (.node 2 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 2), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 2), (0, 1), (0, 5)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 1), (0, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 6), (0, 1), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 17
                    (.node 1 4   -- 9
                      (.node 2 5   -- 3
                        (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 2), (1, 5)]))
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 2), (0, 1), (0, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 1), (0, 5)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 1), (0, 6), (0, 2)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (1, 6)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 6), (0, 2)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (1, 6)]))
                          )
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 2 4   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (1, 6), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 6), (0, 3), (0, 5)]))
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 3), (0, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 2), (0, 3), (0, 5)]))
                        )
                      )
                      (.node 2 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 1), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (1, 6), (1, 2)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (1, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 5), (1, 6)]))
                        )
                      )
                    )
                  )
                )
                (.node 3 6   -- 32
                  (.node 0 4   -- 15
                    (.node 1 4   -- 6
                      (.node 2 5   -- 3
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 1), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 2), (1, 5)]))
                        )
                        (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 2), (0, 1), (0, 5)]))
                      )
                      (.node 2 5   -- 3
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (1, 6), (1, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 6), (0, 3), (0, 2)]))
                        )
                        (.leaf (swapProd [(0, 4), (0, 5), (1, 6), (1, 3), (1, 2)]))
                      )
                    )
                    (.node 2 5   -- 9
                      (.node 3 5   -- 5
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (1, 6), (1, 4), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (1, 6), (1, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 4), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 3), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 4), (0, 2)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 4), (1, 3), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 3), (1, 2)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 4)]))
                        )
                      )
                    )
                  )
                  (.node 3 4   -- 17
                    (.node 0 4   -- 9
                      (.node 1 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (1, 5)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 1), (0, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 5)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 6), (0, 2)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (1, 6)]))
                          )
                        )
                      )
                      (.node 2 5   -- 3
                        (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 2)]))
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (1, 6)]))
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 2 4   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 3), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 3), (1, 4), (1, 2)]))
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 2), (1, 3), (1, 4)]))
                        )
                      )
                      (.node 2 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 2), (3, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 2), (3, 4)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 5), (1, 6), (3, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (2, 3), (2, 4)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 4   -- 81
                (.node 2 6   -- 37
                  (.node 3 5   -- 18
                    (.node 1 5   -- 9
                      (.node 0 3   -- 4
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(0, 2), (1, 3), (1, 4), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (1, 4), (1, 6)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (1, 4), (1, 6)]))
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 0 3   -- 3
                          (.leaf (swapProd [(0, 2), (1, 5), (1, 4), (1, 6)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 4), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (1, 5), (1, 4), (1, 6)]))
                          )
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (1, 5), (1, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 5), (0, 3), (0, 2)]))
                        )
                      )
                    )
                    (.node 0 5   -- 9
                      (.node 1 5   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (1, 3), (1, 5), (1, 4), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (1, 3), (1, 6), (4, 5)]))
                        )
                        (.node 1 3   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (1, 4), (1, 6), (3, 5)]))
                            (.leaf (swapProd [(0, 2), (1, 4), (1, 5), (1, 3), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (1, 5), (1, 3), (1, 4), (1, 6)]))
                        )
                      )
                      (.node 1 3   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (1, 4), (1, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 4), (0, 5), (0, 2)]))
                        )
                        (.node 0 3   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 1), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 5), (0, 2)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 19
                    (.node 1 3   -- 10
                      (.node 1 5   -- 5
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 5), (0, 4), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (0, 6), (4, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 6), (3, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 5), (0, 3), (0, 6)]))
                        )
                      )
                      (.node 0 3   -- 5
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 3), (0, 4), (0, 6)]))
                          )
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 5), (0, 4), (0, 6)]))
                        )
                      )
                    )
                    (.node 1 3   -- 9
                      (.node 2 5   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 1), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (1, 4), (1, 5), (1, 2)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (1, 4), (1, 5)]))
                        )
                      )
                      (.node 0 3   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (1, 5), (1, 2)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (1, 5)]))
                        )
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (1, 5), (1, 3), (1, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (1, 5), (1, 2)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (1, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 3 4   -- 44
                  (.node 2 6   -- 22
                    (.node 0 5   -- 11
                      (.node 0 3   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (1, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 2), (1, 6), (3, 4), (3, 5)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 2), (4, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (1, 6), (4, 5)]))
                        )
                      )
                      (.node 0 4   -- 7
                        (.node 3 5   -- 4
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 1), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 2), (1, 6)]))
                          )
                          (.node 0 3   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (1, 6)]))
                          )
                        )
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (1, 6)]))
                        )
                      )
                    )
                    (.node 0 3   -- 11
                      (.node 0 5   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (3, 4), (3, 5)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 2), (0, 1), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 1), (0, 6)]))
                        )
                      )
                      (.node 0 4   -- 7
                        (.node 3 5   -- 4
                          (.node 0 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (0, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 2), (0, 1), (0, 6)]))
                          )
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 1), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 6)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 1), (0, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 22
                    (.node 1 3   -- 10
                      (.node 0 5   -- 5
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 2), (1, 5), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 3), (0, 6)]))
                        )
                        (.node 2 5   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (1, 5), (1, 2)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (1, 5)]))
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 2), (1, 6), (3, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (3, 5)]))
                        )
                        (.node 2 5   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 6)]))
                        )
                      )
                    )
                    (.node 2 5   -- 12
                      (.node 2 6   -- 6
                        (.node 0 3   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 1), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 2), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (1, 6), (3, 4)]))
                        )
                        (.node 0 3   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 2), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 6), (3, 4)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 0 3   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (3, 4)]))
                        )
                        (.node 0 3   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 5), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (2, 3), (2, 4)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree712 : Tree 7 :=
          (.node 0 6   -- 315
            tree710
            tree711
          )

private def tree713 : Tree 7 :=
        (.node 4 5   -- 630
          tree79
          tree712
        )

private def tree714 : Tree 7 :=
      (.node 0 2   -- 1260
        tree76
        tree713
      )

private def tree715 : Tree 7 :=
            (.node 2 6   -- 168
              (.node 1 2   -- 84
                (.node 1 3   -- 42
                  (.node 1 4   -- 21
                    (.node 3 4   -- 10
                      (.node 2 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(2, 3)]))
                            (.leaf (swapProd [(2, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(2, 3), (4, 5), (4, 6)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(2, 4), (2, 3)]))
                            (.leaf (swapProd [(2, 4), (2, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(2, 5), (2, 4), (2, 3)]))
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(2, 4)]))
                          (.leaf (swapProd [(2, 4), (5, 6)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(2, 5), (2, 4)]))
                          (.leaf (swapProd [(2, 5), (2, 3), (2, 4)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 2 5   -- 5
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(1, 2), (1, 4)]))
                          (.leaf (swapProd [(1, 2), (1, 4), (5, 6)]))
                        )
                        (.node 1 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 3), (1, 4)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 4), (2, 5)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 4)]))
                        )
                        (.node 0 5   -- 3
                          (.node 1 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 3), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 2 5   -- 21
                    (.node 1 4   -- 11
                      (.node 2 4   -- 5
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 3)]))
                            (.leaf (swapProd [(1, 2), (1, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(1, 2), (1, 3), (4, 5), (4, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 3)]))
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 3), (5, 6)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 3), (2, 4)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 4)]))
                        )
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 3), (2, 4), (5, 6)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 4), (5, 6)]))
                        )
                      )
                    )
                    (.node 0 4   -- 10
                      (.node 1 5   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(1, 2), (1, 5), (1, 4), (1, 3)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 3), (2, 5), (2, 4)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 5), (1, 4)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 5), (1, 3)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 4), (2, 5), (2, 3)]))
                            (.leaf (swapProd [(1, 4), (2, 5)]))
                          )
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 5), (0, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (2, 5), (2, 3)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (2, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 6   -- 42
                  (.node 1 5   -- 21
                    (.node 2 4   -- 11
                      (.node 1 4   -- 5
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 3)]))
                            (.leaf (swapProd [(1, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(1, 3), (4, 5), (4, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(1, 4), (1, 3)]))
                          (.leaf (swapProd [(1, 4), (1, 3), (5, 6)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 4), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(1, 4), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4), (2, 3)]))
                        )
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 4), (1, 2), (1, 3), (5, 6)]))
                            (.leaf (swapProd [(1, 4), (2, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4), (2, 3), (5, 6)]))
                        )
                      )
                    )
                    (.node 0 4   -- 10
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
                  (.node 3 4   -- 21
                    (.node 1 5   -- 10
                      (.node 4 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 4), (1, 3)]))
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 4), (1, 2), (1, 3)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 6), (1, 3)]))
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 3)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 5), (1, 4), (1, 3)]))
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 3)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 3)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 5), (1, 4), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 2), (1, 3)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 5), (1, 3), (2, 4)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 2 5   -- 5
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(1, 5), (1, 6), (1, 4), (2, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 5), (1, 4), (2, 3)]))
                            (.leaf (swapProd [(1, 6), (1, 4), (2, 3)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 6), (1, 5), (1, 3), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(1, 6), (1, 5), (1, 2), (1, 4)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 4), (2, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 4), (2, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (2, 3)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 3), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 2), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 4), (1, 6), (1, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 6   -- 84
                (.node 1 3   -- 42
                  (.node 1 4   -- 21
                    (.node 2 5   -- 10
                      (.node 4 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(2, 5), (2, 6), (2, 4), (2, 3)]))
                          (.leaf (swapProd [(2, 5), (2, 6), (2, 4)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(2, 4), (2, 5), (2, 6), (2, 3)]))
                          (.leaf (swapProd [(2, 5), (2, 6), (2, 3)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(2, 6), (2, 5), (2, 4), (2, 3)]))
                            (.leaf (swapProd [(2, 6), (2, 4), (2, 3)]))
                          )
                          (.leaf (swapProd [(2, 6), (2, 3)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(2, 6), (2, 5), (2, 4)]))
                            (.leaf (swapProd [(2, 6), (2, 4)]))
                          )
                          (.leaf (swapProd [(2, 6), (2, 5), (2, 3), (2, 4)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 3 5   -- 5
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(1, 2), (1, 5), (1, 6), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 4)]))
                          )
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 2), (1, 6), (1, 5), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(1, 3), (1, 4), (2, 6), (2, 5)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 6), (0, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 4)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.node 1 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 5), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (2, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 1), (0, 3), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 3 4   -- 21
                    (.node 1 4   -- 10
                      (.node 2 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 5), (1, 6), (1, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 6), (1, 4), (1, 3)]))
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 6), (1, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 5), (1, 4), (1, 3)]))
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 4), (1, 3)]))
                          )
                          (.leaf (swapProd [(1, 2), (1, 6), (1, 3)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 3), (2, 6), (2, 5), (2, 4)]))
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 6), (1, 5), (1, 3)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 3), (2, 5), (2, 6), (2, 4)]))
                          (.leaf (swapProd [(1, 3), (2, 6), (2, 4)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 1 5   -- 5
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(1, 3), (1, 2), (1, 5), (1, 6), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 6), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 6), (1, 4)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 4), (2, 6), (2, 5), (2, 3)]))
                          (.leaf (swapProd [(1, 4), (2, 6), (2, 5)]))
                        )
                      )
                      (.node 1 5   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 5), (0, 6), (0, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 6), (0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 6), (0, 4)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (2, 6), (2, 5), (2, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (2, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 1), (0, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 2   -- 42
                  (.node 1 5   -- 21
                    (.node 2 5   -- 11
                      (.node 4 6   -- 6
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 4), (1, 2), (1, 5), (1, 6), (1, 3)]))
                            (.leaf (swapProd [(1, 4), (2, 5), (2, 6), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4), (2, 5), (2, 6), (2, 3)]))
                        )
                        (.node 1 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(1, 3), (2, 4), (2, 5), (2, 6)]))
                            (.leaf (swapProd [(1, 3), (2, 5), (2, 6)]))
                          )
                          (.leaf (swapProd [(1, 4), (1, 3), (2, 5), (2, 6)]))
                        )
                      )
                      (.node 3 4   -- 5
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(1, 3), (2, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 4), (1, 2), (1, 6), (1, 3)]))
                            (.leaf (swapProd [(1, 4), (1, 3), (2, 6)]))
                          )
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 4), (2, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (2, 6), (2, 3)]))
                        )
                      )
                    )
                    (.node 0 4   -- 10
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 5), (1, 3), (2, 6), (2, 4)]))
                            (.leaf (swapProd [(1, 5), (1, 4), (1, 2), (1, 6), (1, 3)]))
                          )
                          (.leaf (swapProd [(1, 5), (1, 4), (1, 3), (2, 6)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 5), (1, 3), (1, 2), (1, 6), (1, 4)]))
                            (.leaf (swapProd [(1, 5), (1, 4), (2, 6), (2, 3)]))
                          )
                          (.leaf (swapProd [(1, 5), (1, 2), (1, 6), (1, 4)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 2), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (2, 6), (2, 3)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (1, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 5   -- 21
                    (.node 1 5   -- 11
                      (.node 4 6   -- 6
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 5), (1, 6), (1, 3), (2, 4)]))
                            (.leaf (swapProd [(1, 5), (1, 6), (1, 3), (1, 2), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 3), (0, 2), (0, 4)]))
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 6), (1, 2), (1, 3)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(1, 5), (1, 6), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(1, 5), (1, 6), (1, 2), (1, 4), (1, 3)]))
                          )
                        )
                      )
                      (.node 3 4   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 3), (2, 4)]))
                            (.leaf (swapProd [(1, 6), (1, 2), (1, 4), (1, 3)]))
                          )
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 6), (1, 3), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 2), (0, 4)]))
                        )
                      )
                    )
                    (.node 0 4   -- 10
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 2), (1, 5), (1, 3)]))
                            (.leaf (swapProd [(1, 6), (1, 3), (2, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 5), (1, 4), (1, 3)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 4), (2, 5), (2, 3)]))
                            (.leaf (swapProd [(1, 6), (1, 3), (1, 2), (1, 5), (1, 4)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 4), (2, 5)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (2, 5), (2, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 2), (0, 5), (0, 4)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (2, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 6), (0, 4)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree716 : Tree 7 :=
            (.node 4 6   -- 147
              (.node 1 3   -- 66
                (.node 1 6   -- 32
                  (.node 0 4   -- 15
                    (.node 1 4   -- 9
                      (.node 3 5   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(2, 5), (2, 6), (2, 3), (2, 4)]))
                          (.leaf (swapProd [(2, 6), (2, 3), (2, 4)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(2, 6), (2, 4), (3, 5)]))
                          (.leaf (swapProd [(2, 6), (2, 3), (2, 5), (2, 4)]))
                        )
                      )
                      (.node 3 5   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 2), (1, 5), (1, 6), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(1, 2), (1, 6), (1, 3), (1, 4)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 4), (3, 5)]))
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 3), (1, 5), (1, 4)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 2), (1, 6), (1, 4)]))
                        )
                      )
                    )
                    (.node 5 6   -- 6
                      (.node 0 5   -- 3
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 4), (3, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 2), (0, 6), (0, 4)]))
                        )
                        (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (1, 3), (1, 5)]))
                      )
                      (.node 2 5   -- 3
                        (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 6), (0, 3), (0, 4)]))
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 3), (0, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 3), (0, 5), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 17
                    (.node 0 4   -- 9
                      (.node 2 5   -- 3
                        (.leaf (swapProd [(1, 3), (1, 4), (2, 5), (2, 6)]))
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 3), (1, 4), (2, 6)]))
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 4), (2, 6)]))
                        )
                      )
                      (.node 0 6   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (2, 5), (2, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (2, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 4), (2, 6)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 1), (0, 3), (0, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 3), (0, 5), (0, 4)]))
                          )
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 0 5   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 4), (2, 6), (2, 3), (2, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (2, 6), (2, 3), (2, 5)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 5), (0, 1), (0, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 4), (2, 6)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 4), (2, 6), (3, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (2, 6), (3, 5)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 4), (3, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 6), (0, 1), (0, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 2   -- 34
                  (.node 3 5   -- 17
                    (.node 0 4   -- 9
                      (.node 1 5   -- 3
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 4), (2, 5), (2, 6)]))
                          (.leaf (swapProd [(1, 4), (2, 6)]))
                        )
                        (.leaf (swapProd [(1, 5), (1, 4), (2, 6)]))
                      )
                      (.node 0 6   -- 6
                        (.node 1 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (2, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (2, 6)]))
                        )
                        (.node 1 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 5), (0, 4)]))
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 0 5   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 5), (1, 2), (1, 6), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 6), (0, 3), (0, 4)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 4), (1, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (1, 5), (2, 6)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 5), (1, 3), (1, 4), (2, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 4), (2, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 5), (0, 3), (0, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (1, 5), (1, 2), (1, 6)]))
                        )
                      )
                    )
                  )
                  (.node 3 5   -- 17
                    (.node 0 4   -- 9
                      (.node 1 5   -- 3
                        (.leaf (swapProd [(1, 5), (1, 6), (1, 2), (1, 4)]))
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 5), (1, 4)]))
                        )
                      )
                      (.node 0 6   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 2), (0, 4)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 5), (0, 4)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 4), (1, 5), (1, 6)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (1, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (1, 6)]))
                          )
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 0 5   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 6), (1, 3), (1, 4), (2, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 4), (2, 5)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 6), (0, 3), (0, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (1, 6), (1, 2), (1, 5)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 5), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 5), (0, 3), (0, 4)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 4), (1, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (1, 6), (2, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 2 5   -- 81
                (.node 0 6   -- 37
                  (.node 1 4   -- 18
                    (.node 2 4   -- 9
                      (.node 1 3   -- 4
                        (.node 1 6   -- 2
                          (.leaf (swapProd [(2, 4), (2, 5), (2, 6)]))
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 5), (1, 6)]))
                        )
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(1, 3), (1, 2), (1, 4), (1, 5), (1, 6)]))
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 6), (2, 3)]))
                        )
                      )
                      (.node 1 6   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(2, 5), (2, 6)]))
                          (.leaf (swapProd [(2, 5), (2, 6), (3, 4)]))
                        )
                        (.node 1 3   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 6)]))
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 6), (3, 4)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 2), (1, 5), (1, 6)]))
                        )
                      )
                    )
                    (.node 3 4   -- 9
                      (.node 1 5   -- 5
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 2), (1, 5), (1, 6)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(1, 5), (1, 6), (2, 3)]))
                            (.leaf (swapProd [(1, 5), (1, 6), (2, 4), (2, 3)]))
                          )
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 6), (2, 3)]))
                          (.leaf (swapProd [(1, 6), (2, 4), (2, 3)]))
                        )
                      )
                      (.node 1 2   -- 4
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 2), (1, 5), (1, 6)]))
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 5), (1, 6)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 5), (1, 6), (2, 4)]))
                          (.leaf (swapProd [(1, 6), (2, 4)]))
                        )
                      )
                    )
                  )
                  (.node 1 2   -- 19
                    (.node 1 3   -- 10
                      (.node 1 4   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 5), (0, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 6), (3, 4)]))
                          )
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 2), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (1, 3), (1, 4)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 4), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 5), (0, 6)]))
                        )
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 2), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 5), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (1, 4)]))
                        )
                      )
                    )
                    (.node 1 5   -- 9
                      (.node 2 4   -- 5
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (2, 3)]))
                        )
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (2, 4), (2, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 5), (0, 6)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (2, 4), (2, 3)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6), (2, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 6)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 5   -- 44
                  (.node 0 6   -- 22
                    (.node 1 4   -- 11
                      (.node 1 6   -- 7
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(2, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(2, 6), (3, 4)]))
                            (.leaf (swapProd [(2, 6), (3, 5), (3, 4)]))
                          )
                        )
                        (.node 3 4   -- 4
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(1, 2), (1, 6)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 6)]))
                          )
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 2), (1, 6), (3, 4)]))
                            (.leaf (swapProd [(1, 2), (1, 6), (3, 5), (3, 4)]))
                          )
                        )
                      )
                      (.node 1 3   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 4), (1, 2), (1, 6)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 6)]))
                        )
                      )
                    )
                    (.node 1 3   -- 11
                      (.node 1 4   -- 7
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (3, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (3, 5), (3, 4)]))
                          )
                        )
                        (.node 0 4   -- 4
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 4), (0, 2), (0, 6)]))
                          )
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (1, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (1, 3), (1, 5), (1, 4)]))
                          )
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 2), (0, 6)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (1, 4)]))
                        )
                      )
                    )
                  )
                  (.node 3 5   -- 22
                    (.node 1 2   -- 10
                      (.node 0 6   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 5), (1, 4), (1, 3), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(1, 5), (1, 4), (1, 2), (1, 6)]))
                        )
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 3), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 2), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (1, 5), (1, 4)]))
                        )
                      )
                      (.node 0 6   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 6), (2, 5), (2, 4), (2, 3)]))
                          (.leaf (swapProd [(1, 6), (2, 5), (2, 4)]))
                        )
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (2, 5), (2, 4), (2, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (2, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 1), (0, 6)]))
                        )
                      )
                    )
                    (.node 0 4   -- 12
                      (.node 0 6   -- 6
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(1, 4), (1, 2), (1, 6), (3, 5)]))
                            (.leaf (swapProd [(1, 5), (1, 3), (1, 4), (1, 2), (1, 6)]))
                          )
                          (.leaf (swapProd [(1, 6), (2, 5), (2, 3), (2, 4)]))
                        )
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 6), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 4), (0, 2), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 6), (2, 5), (2, 3), (2, 4)]))
                        )
                      )
                      (.node 0 5   -- 6
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (1, 4), (3, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (1, 5), (1, 3), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 4), (0, 1), (0, 6)]))
                        )
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 6), (1, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 5), (0, 2), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 6), (2, 5)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree717 : Tree 7 :=
          (.node 3 6   -- 315
            tree715
            tree716
          )

private def tree718 : Tree 7 :=
            (.node 2 6   -- 168
              (.node 1 2   -- 84
                (.node 1 3   -- 42
                  (.node 1 5   -- 21
                    (.node 3 5   -- 10
                      (.node 2 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(2, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(2, 3), (4, 6), (4, 5)]))
                            (.leaf (swapProd [(2, 3), (4, 6)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(2, 4), (2, 5), (2, 3)]))
                            (.leaf (swapProd [(2, 4), (2, 6), (2, 5), (2, 3)]))
                          )
                          (.leaf (swapProd [(2, 5), (2, 3)]))
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(2, 4), (2, 5)]))
                          (.leaf (swapProd [(2, 4), (2, 6), (2, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(2, 5)]))
                          (.leaf (swapProd [(2, 5), (3, 4)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 2 4   -- 5
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 5)]))
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 6), (1, 5)]))
                        )
                        (.node 1 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 2), (1, 5)]))
                            (.leaf (swapProd [(1, 2), (1, 5), (3, 4)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 2), (1, 5)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 5)]))
                        )
                        (.node 0 4   -- 3
                          (.node 1 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (3, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 2), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 3), (1, 4)]))
                        )
                      )
                    )
                  )
                  (.node 2 4   -- 21
                    (.node 1 5   -- 11
                      (.node 2 5   -- 5
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 2), (1, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 3), (4, 6), (4, 5)]))
                            (.leaf (swapProd [(1, 2), (1, 3), (4, 6)]))
                          )
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 5), (1, 3)]))
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 6), (1, 5), (1, 3)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 3), (2, 4), (2, 5)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 4), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 4), (0, 5)]))
                        )
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 3), (2, 4), (2, 6), (2, 5)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 4), (1, 6), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 4), (0, 6), (0, 5)]))
                        )
                      )
                    )
                    (.node 0 5   -- 10
                      (.node 1 4   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(1, 2), (1, 5), (1, 3)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 3), (2, 5)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 5)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 4), (1, 3), (2, 5)]))
                            (.leaf (swapProd [(1, 4), (1, 3), (1, 2), (1, 5)]))
                          )
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 5)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 2), (0, 5)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 6   -- 42
                  (.node 1 4   -- 21
                    (.node 2 5   -- 11
                      (.node 1 5   -- 5
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 3), (4, 6), (4, 5)]))
                            (.leaf (swapProd [(1, 3), (4, 6)]))
                          )
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 3)]))
                          (.leaf (swapProd [(1, 4), (1, 6), (1, 5), (1, 3)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 4), (1, 5), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(1, 4), (1, 5), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (2, 3)]))
                        )
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 4), (1, 6), (1, 5), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(1, 4), (1, 6), (1, 5), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 5), (2, 3)]))
                        )
                      )
                    )
                    (.node 0 5   -- 10
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
                  (.node 3 5   -- 21
                    (.node 1 4   -- 10
                      (.node 5 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 5), (1, 3), (4, 6)]))
                          (.leaf (swapProd [(1, 5), (1, 2), (1, 3), (4, 6)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(1, 4), (1, 6), (1, 3)]))
                          (.leaf (swapProd [(1, 5), (1, 4), (1, 6), (1, 3)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 6), (1, 5), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 5), (1, 3)]))
                            (.leaf (swapProd [(1, 6), (1, 3), (4, 5)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 5), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 5), (1, 2), (1, 3)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 5), (1, 2), (1, 4), (1, 3)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 2 4   -- 5
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(1, 5), (2, 3), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 5), (2, 3)]))
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 5), (2, 3)]))
                          )
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 6), (1, 5), (2, 4), (2, 3)]))
                          (.leaf (swapProd [(1, 6), (1, 5), (2, 4)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 3), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (2, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 5), (2, 3)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (2, 4), (2, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 6), (0, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 6   -- 84
                (.node 1 3   -- 42
                  (.node 1 5   -- 21
                    (.node 2 4   -- 10
                      (.node 5 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(2, 5), (2, 3), (4, 6)]))
                          (.leaf (swapProd [(2, 5), (4, 6)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(2, 4), (2, 6), (2, 3)]))
                          (.leaf (swapProd [(2, 5), (2, 4), (2, 6), (2, 3)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(2, 6), (2, 5), (2, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(2, 6), (2, 4), (2, 5), (2, 3)]))
                            (.leaf (swapProd [(2, 6), (2, 3), (4, 5)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(2, 6), (2, 5)]))
                            (.leaf (swapProd [(2, 6), (2, 4), (2, 5)]))
                          )
                          (.leaf (swapProd [(2, 6), (2, 5), (3, 4)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 3 4   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(1, 2), (1, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 4), (1, 5)]))
                          )
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 2), (1, 6), (1, 5), (3, 4)]))
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 2), (1, 6), (1, 5)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 4), (0, 5)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.node 1 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 5), (3, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 2), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (1, 3), (1, 4)]))
                        )
                      )
                    )
                  )
                  (.node 3 5   -- 21
                    (.node 1 5   -- 10
                      (.node 2 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 6), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 3), (4, 6)]))
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 4), (1, 6), (1, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 2), (1, 6), (1, 5), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 4), (1, 5), (1, 3)]))
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 3), (4, 5)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 3), (2, 6), (2, 5)]))
                          (.leaf (swapProd [(1, 4), (1, 3), (2, 6), (2, 5)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 3), (2, 5), (4, 6)]))
                          (.leaf (swapProd [(1, 3), (2, 6), (2, 4), (2, 5)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 1 4   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(1, 3), (1, 2), (1, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 6), (1, 4), (1, 5)]))
                          )
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 2), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 6), (1, 5)]))
                        )
                      )
                      (.node 1 4   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 6), (0, 4), (0, 5)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 2), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (1, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 2   -- 42
                  (.node 1 4   -- 21
                    (.node 2 4   -- 11
                      (.node 5 6   -- 6
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 4), (1, 6), (1, 3), (2, 5)]))
                            (.leaf (swapProd [(1, 4), (1, 6), (1, 3), (1, 2), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 3), (0, 2), (0, 5)]))
                        )
                        (.node 1 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(1, 3), (2, 4), (2, 6)]))
                            (.leaf (swapProd [(1, 3), (2, 5), (2, 4), (2, 6)]))
                          )
                          (.leaf (swapProd [(1, 4), (1, 6), (1, 2), (1, 5), (1, 3)]))
                        )
                      )
                      (.node 3 5   -- 5
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(1, 3), (2, 6), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 4), (1, 5), (1, 2), (1, 6), (1, 3)]))
                            (.leaf (swapProd [(1, 4), (1, 5), (1, 3), (2, 6)]))
                          )
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 4), (1, 5), (2, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (2, 6), (2, 3)]))
                        )
                      )
                    )
                    (.node 0 5   -- 10
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 5), (1, 2), (1, 6), (1, 4), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 5), (1, 2), (1, 6), (1, 3)]))
                            (.leaf (swapProd [(1, 5), (1, 3), (2, 6)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 5), (2, 6), (2, 4), (2, 3)]))
                            (.leaf (swapProd [(1, 5), (2, 6), (2, 3)]))
                          )
                          (.leaf (swapProd [(1, 5), (2, 6), (2, 4)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 6), (2, 4), (2, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 6), (2, 3)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 6), (2, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 1), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 4   -- 21
                    (.node 1 4   -- 11
                      (.node 5 6   -- 6
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 5), (1, 2), (1, 4), (1, 6), (1, 3)]))
                            (.leaf (swapProd [(1, 5), (2, 4), (2, 6), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 4), (2, 6), (2, 3)]))
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(1, 4), (1, 6), (1, 2), (1, 3)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(1, 5), (1, 4), (1, 6), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(1, 5), (1, 3), (2, 4), (2, 6)]))
                          )
                        )
                      )
                      (.node 3 5   -- 5
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 3), (2, 4), (2, 5)]))
                            (.leaf (swapProd [(1, 6), (1, 2), (1, 4), (1, 5), (1, 3)]))
                          )
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 6), (1, 3), (1, 2), (1, 4), (1, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 2), (0, 4), (0, 5)]))
                        )
                      )
                    )
                    (.node 0 5   -- 10
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(1, 6), (1, 4), (1, 3), (2, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 3), (2, 5)]))
                            (.leaf (swapProd [(1, 6), (1, 2), (1, 5), (1, 3)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 6), (1, 4), (1, 3), (1, 2), (1, 5)]))
                            (.leaf (swapProd [(1, 6), (1, 3), (1, 2), (1, 5)]))
                          )
                          (.leaf (swapProd [(1, 6), (1, 4), (1, 2), (1, 5)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 3), (0, 2), (0, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 2), (0, 5)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 2), (0, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 6), (1, 4)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree719 : Tree 7 :=
            (.node 5 6   -- 147
              (.node 1 3   -- 66
                (.node 1 6   -- 32
                  (.node 0 5   -- 15
                    (.node 1 5   -- 9
                      (.node 3 4   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(2, 5), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(2, 6), (2, 3), (2, 4), (2, 5)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(2, 6), (2, 4), (2, 3), (2, 5)]))
                          (.leaf (swapProd [(2, 6), (2, 3), (2, 5)]))
                        )
                      )
                      (.node 3 4   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 2), (1, 5), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(1, 2), (1, 6), (1, 3), (1, 4), (1, 5)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 4), (1, 3), (1, 5)]))
                            (.leaf (swapProd [(1, 2), (1, 6), (1, 3), (1, 5)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 5), (2, 6), (2, 4)]))
                        )
                      )
                    )
                    (.node 4 6   -- 6
                      (.node 0 4   -- 3
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 4), (0, 3), (0, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (2, 6), (2, 4)]))
                        )
                        (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 1), (0, 3), (0, 5)]))
                      )
                      (.node 2 4   -- 3
                        (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (3, 4), (3, 6)]))
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 3), (0, 4), (0, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 3), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 17
                    (.node 0 5   -- 9
                      (.node 2 4   -- 3
                        (.leaf (swapProd [(1, 3), (1, 4), (1, 6), (1, 2), (1, 5)]))
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 5), (2, 6)]))
                          (.leaf (swapProd [(1, 3), (1, 5), (2, 6)]))
                        )
                      )
                      (.node 0 6   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 6), (0, 2), (0, 5)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (2, 6)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 3), (1, 4), (1, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 3), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 3), (0, 5)]))
                          )
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 0 4   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 4), (1, 2), (1, 6), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 6), (0, 3), (0, 5)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 5), (1, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (1, 4), (2, 6)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 4), (1, 3), (1, 5), (2, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 5), (2, 6)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 4), (0, 3), (0, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (1, 4), (1, 2), (1, 6)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 2   -- 34
                  (.node 3 4   -- 17
                    (.node 0 5   -- 9
                      (.node 1 4   -- 3
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 4), (1, 6), (1, 2), (1, 5)]))
                          (.leaf (swapProd [(1, 4), (1, 5), (2, 6)]))
                        )
                        (.leaf (swapProd [(1, 5), (2, 6)]))
                      )
                      (.node 0 6   -- 6
                        (.node 1 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 2), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 6)]))
                        )
                        (.node 1 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (1, 4), (1, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 4), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 5)]))
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 0 4   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 5), (2, 6), (2, 3), (2, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 6), (2, 3), (2, 4)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 4), (0, 1), (0, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 5), (2, 6)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 5), (2, 6), (3, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 6), (3, 4)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 5), (3, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 6), (0, 1), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 3 4   -- 17
                    (.node 0 5   -- 9
                      (.node 1 4   -- 3
                        (.leaf (swapProd [(1, 5), (2, 4), (2, 6)]))
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 4), (1, 5)]))
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 5)]))
                        )
                      )
                      (.node 0 6   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (2, 4), (2, 6)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 5)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 1), (0, 5)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (1, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (1, 6)]))
                          )
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 0 4   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 6), (1, 3), (1, 4), (1, 2), (1, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (0, 4), (0, 2), (0, 5)]))
                        )
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 6), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 6), (0, 2), (0, 5)]))
                        )
                      )
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(1, 6), (1, 2), (1, 5), (3, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 5), (3, 4)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 6), (3, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 5), (1, 6)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 2 4   -- 81
                (.node 0 6   -- 37
                  (.node 1 5   -- 18
                    (.node 2 5   -- 9
                      (.node 1 3   -- 4
                        (.node 1 6   -- 2
                          (.leaf (swapProd [(2, 4), (2, 6)]))
                          (.leaf (swapProd [(1, 2), (1, 4), (1, 6)]))
                        )
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(1, 3), (1, 2), (1, 4), (1, 6)]))
                          (.leaf (swapProd [(1, 4), (1, 6), (2, 3)]))
                        )
                      )
                      (.node 1 6   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(2, 5), (2, 4), (2, 6)]))
                          (.leaf (swapProd [(2, 5), (2, 3), (2, 4), (2, 6)]))
                        )
                        (.node 1 3   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 4), (1, 6)]))
                            (.leaf (swapProd [(1, 2), (1, 5), (1, 3), (1, 4), (1, 6)]))
                          )
                          (.leaf (swapProd [(1, 3), (1, 2), (1, 5), (1, 4), (1, 6)]))
                        )
                      )
                    )
                    (.node 3 5   -- 9
                      (.node 1 4   -- 5
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(1, 4), (1, 6), (2, 5), (2, 3)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(1, 5), (1, 4), (1, 6), (2, 3)]))
                            (.leaf (swapProd [(1, 5), (1, 3), (1, 2), (1, 4), (1, 6)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(1, 6), (2, 3), (4, 5)]))
                          (.leaf (swapProd [(1, 6), (2, 4), (2, 5), (2, 3)]))
                        )
                      )
                      (.node 1 2   -- 4
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 6), (2, 5)]))
                          (.leaf (swapProd [(1, 4), (1, 6), (2, 5)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(1, 5), (1, 2), (1, 4), (1, 6)]))
                          (.leaf (swapProd [(1, 6), (2, 4), (2, 5)]))
                        )
                      )
                    )
                  )
                  (.node 1 2   -- 19
                    (.node 1 3   -- 10
                      (.node 1 5   -- 5
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 3), (0, 4), (0, 6)]))
                          )
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 6), (2, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 3), (0, 4), (0, 6)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 5), (0, 4), (0, 6)]))
                        )
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (2, 5), (2, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 4), (0, 6)]))
                        )
                      )
                    )
                    (.node 1 4   -- 9
                      (.node 2 5   -- 5
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 6), (2, 3)]))
                        )
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 2), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 4), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (1, 5)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6), (2, 3), (4, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 6), (2, 4), (2, 5), (2, 3)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 6), (2, 4), (2, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 1), (0, 6)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 4   -- 44
                  (.node 0 6   -- 22
                    (.node 1 5   -- 11
                      (.node 1 6   -- 7
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(2, 6), (4, 5)]))
                            (.leaf (swapProd [(2, 6), (3, 4), (3, 5)]))
                          )
                          (.leaf (swapProd [(2, 6), (3, 5)]))
                        )
                        (.node 3 5   -- 4
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(1, 2), (1, 6), (4, 5)]))
                            (.leaf (swapProd [(1, 3), (1, 2), (1, 6), (4, 5)]))
                          )
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(1, 2), (1, 6), (3, 4), (3, 5)]))
                            (.leaf (swapProd [(1, 2), (1, 6), (3, 5)]))
                          )
                        )
                      )
                      (.node 1 3   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(1, 3), (1, 4), (1, 5), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(1, 3), (1, 5), (1, 2), (1, 6)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 3), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(1, 4), (1, 5), (1, 2), (1, 6)]))
                        )
                      )
                    )
                    (.node 1 3   -- 11
                      (.node 1 5   -- 7
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (3, 4), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (3, 5)]))
                        )
                        (.node 0 5   -- 4
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 4), (0, 5), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (0, 5), (0, 2), (0, 6)]))
                          )
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (1, 3), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (1, 3), (1, 5)]))
                          )
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (0, 2), (0, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 3), (0, 2), (0, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 2), (0, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (1, 4), (1, 5)]))
                        )
                      )
                    )
                  )
                  (.node 3 4   -- 22
                    (.node 1 2   -- 10
                      (.node 0 6   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 5), (1, 3), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(1, 5), (1, 2), (1, 6)]))
                        )
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (1, 5)]))
                        )
                      )
                      (.node 0 6   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(1, 6), (2, 5), (2, 3)]))
                          (.leaf (swapProd [(1, 6), (2, 5)]))
                        )
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (2, 5), (2, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 6)]))
                        )
                      )
                    )
                    (.node 0 5   -- 12
                      (.node 0 6   -- 6
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(1, 4), (1, 3), (1, 5), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(1, 5), (1, 2), (1, 6), (3, 4)]))
                          )
                          (.leaf (swapProd [(1, 6), (2, 5), (3, 4)]))
                        )
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (0, 5), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 6), (3, 4)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 6), (2, 5), (3, 4)]))
                        )
                      )
                      (.node 0 4   -- 6
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (1, 4), (1, 3), (1, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (1, 5), (3, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 6), (3, 4)]))
                        )
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 4), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 6), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 5), (0, 1), (0, 6)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree720 : Tree 7 :=
          (.node 3 6   -- 315
            tree718
            tree719
          )

private def tree721 : Tree 7 :=
        (.node 4 5   -- 630
          tree717
          tree720
        )

private def tree722 : Tree 7 :=
            (.node 1 6   -- 168
              (.node 1 2   -- 84
                (.node 2 6   -- 42
                  (.node 0 4   -- 21
                    (.node 1 4   -- 10
                      (.node 2 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (4, 5), (4, 6)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 4), (0, 3)]))
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 4), (5, 6)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 5), (2, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 5), (0, 3)]))
                        )
                      )
                    )
                    (.node 1 5   -- 11
                      (.node 3 4   -- 6
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 1), (0, 3)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (1, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (1, 3)]))
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 1), (0, 4)]))
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 4), (2, 5)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (2, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 1), (0, 4)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 1 4   -- 10
                      (.node 2 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 6), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 6), (0, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 5), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 4), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 3)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 6), (2, 5), (2, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 6), (0, 5), (0, 3)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 5), (2, 6), (2, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 6), (2, 4)]))
                        )
                      )
                    )
                    (.node 1 5   -- 11
                      (.node 3 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 4), (0, 1), (0, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 4), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 1), (0, 3)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 4), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 4), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (1, 3)]))
                          )
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 3), (0, 1), (0, 4)]))
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 4), (2, 6), (2, 5)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (2, 6), (2, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 5), (0, 1), (0, 4)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 0 2   -- 42
                  (.node 0 4   -- 21
                    (.node 2 4   -- 10
                      (.node 1 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 3), (4, 5), (4, 6)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 3)]))
                        )
                      )
                      (.node 1 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 3), (5, 6)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (2, 4)]))
                        )
                      )
                    )
                    (.node 2 5   -- 11
                      (.node 3 4   -- 6
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (1, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (1, 5), (1, 4)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 4), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 5), (0, 4)]))
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 5), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (1, 5), (1, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 5), (1, 2), (1, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (1, 5)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 21
                    (.node 0 4   -- 11
                      (.node 1 4   -- 5
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (4, 5), (4, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 3), (5, 6)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 2)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 2), (5, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (1, 4), (5, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (5, 6)]))
                          )
                        )
                      )
                    )
                    (.node 0 5   -- 10
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
              )
              (.node 2 6   -- 84
                (.node 0 2   -- 42
                  (.node 0 4   -- 21
                    (.node 1 5   -- 10
                      (.node 4 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 4), (0, 2), (0, 3)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 3)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 3)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 4), (0, 2), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 2), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 3), (2, 4)]))
                        )
                      )
                    )
                    (.node 2 5   -- 11
                      (.node 3 4   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (1, 5), (1, 6), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (1, 6), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (1, 6), (1, 4)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 5), (0, 6), (0, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 6), (0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 6), (0, 4)]))
                          )
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 6), (0, 5), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (1, 6), (1, 5), (1, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 5), (1, 2), (1, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 5), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (1, 6), (1, 5)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 2 4   -- 21
                    (.node 0 4   -- 10
                      (.node 1 5   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 5), (0, 6), (0, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 6), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 6), (0, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 5), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 4), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 3)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 5), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 6), (0, 5), (0, 3)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 3), (1, 5), (1, 6), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 4), (1, 2)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 3 4   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 3), (1, 5), (1, 6), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 6), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(0, 3), (1, 6), (1, 4)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 6), (0, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 4)]))
                          )
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 5), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (1, 6), (1, 5), (1, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 5), (0, 2), (0, 3)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (1, 6), (1, 5), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 4), (1, 6), (1, 5), (2, 3)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 1 2   -- 42
                  (.node 0 4   -- 21
                    (.node 2 5   -- 10
                      (.node 1 4   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 4), (2, 5), (2, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 5), (2, 6)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 5), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (2, 5), (2, 6)]))
                        )
                      )
                      (.node 1 5   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 2), (0, 6), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (2, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (2, 6), (2, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 2), (0, 6), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 3), (2, 6)]))
                        )
                      )
                    )
                    (.node 3 4   -- 11
                      (.node 1 5   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (1, 4)]))
                        )
                        (.node 0 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 1), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (1, 5), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (1, 5), (1, 2), (1, 6), (1, 4)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (1, 5), (1, 3)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 2), (0, 6), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 4), (1, 5)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 3), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 1), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 1), (0, 5), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 1 5   -- 10
                      (.node 2 4   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 6), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 2), (0, 3)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 3), (2, 4)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 6), (0, 2), (0, 4), (0, 3)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (2, 4)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 4), (0, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 2), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (2, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 5), (0, 4), (0, 3)]))
                        )
                      )
                    )
                    (.node 3 4   -- 11
                      (.node 2 5   -- 5
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 5), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (0, 6), (0, 3)]))
                        )
                        (.node 0 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (1, 6), (1, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 1), (0, 6), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 4), (2, 5)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 1), (0, 6), (0, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 4), (2, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 1), (0, 6), (0, 4)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 4), (1, 5), (1, 6), (1, 3)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (1, 6), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (1, 6), (1, 3)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree723 : Tree 7 :=
            (.node 4 6   -- 147
              (.node 0 2   -- 66
                (.node 1 2   -- 34
                  (.node 0 5   -- 17
                    (.node 1 5   -- 9
                      (.node 2 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 4), (2, 5), (2, 6)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (2, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 6), (0, 1), (0, 4)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 4), (2, 6)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (2, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 1), (0, 4)]))
                          )
                        )
                      )
                      (.node 3 4   -- 3
                        (.leaf (swapProd [(0, 3), (1, 5), (1, 4), (2, 6)]))
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 4), (2, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 1), (0, 5), (0, 4)]))
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 3 5   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 2), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (1, 5), (1, 2), (1, 6), (1, 3)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (1, 5), (2, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 4), (1, 5), (2, 6)]))
                        )
                      )
                      (.node 3 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 3), (2, 6)]))
                          (.leaf (swapProd [(0, 4), (1, 5), (1, 3), (2, 6)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (1, 5), (1, 3), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(0, 4), (1, 5), (1, 2), (1, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 17
                    (.node 1 5   -- 9
                      (.node 3 4   -- 3
                        (.leaf (swapProd [(0, 3), (1, 5), (1, 6), (1, 2), (1, 4)]))
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 6), (0, 2), (0, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (1, 5), (1, 6)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 2), (1, 4)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (1, 6)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 2), (1, 5), (1, 4)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 2), (0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 4), (1, 6)]))
                          )
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 3 5   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 3), (2, 5)]))
                          (.leaf (swapProd [(0, 4), (1, 6), (1, 3), (2, 5)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (1, 6), (1, 3), (1, 2), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (1, 6), (1, 2), (1, 5)]))
                        )
                      )
                      (.node 3 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 2), (0, 5), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (1, 6), (1, 2), (1, 5), (1, 3)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (1, 6), (2, 5), (2, 3)]))
                          (.leaf (swapProd [(0, 4), (1, 6), (2, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 2 6   -- 32
                  (.node 0 5   -- 15
                    (.node 1 5   -- 6
                      (.node 2 4   -- 3
                        (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 5), (0, 6), (0, 3)]))
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (1, 5), (1, 6), (1, 3)]))
                        )
                      )
                      (.node 2 4   -- 3
                        (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 6), (0, 3)]))
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (1, 6), (1, 3)]))
                        )
                      )
                    )
                    (.node 3 4   -- 9
                      (.node 2 4   -- 5
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (1, 6), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 1), (0, 6), (0, 3)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (1, 6), (1, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 6), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (1, 6), (1, 4)]))
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 6), (1, 3)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 1), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 4), (2, 3)]))
                        )
                      )
                    )
                  )
                  (.node 2 5   -- 17
                    (.node 0 5   -- 9
                      (.node 1 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 6), (0, 2), (0, 3)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 5), (1, 6), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 4), (1, 5), (1, 6), (2, 3)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 2), (0, 3)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 6), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 4), (1, 6), (2, 3)]))
                          )
                        )
                      )
                      (.node 3 4   -- 3
                        (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 6), (0, 2), (0, 3)]))
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 6), (1, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 6), (2, 3)]))
                        )
                      )
                    )
                    (.node 5 6   -- 8
                      (.node 3 5   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 1), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (1, 6), (1, 3)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 3), (0, 2), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 2), (0, 4)]))
                        )
                      )
                      (.node 3 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (1, 6), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 6), (0, 2), (0, 4)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 4), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (1, 6)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 5   -- 81
                (.node 3 6   -- 37
                  (.node 2 4   -- 18
                    (.node 1 4   -- 9
                      (.node 0 2   -- 4
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 6), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (1, 4), (1, 5), (1, 6)]))
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 5), (1, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 5), (1, 6)]))
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 0 2   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (1, 5), (1, 6)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 5), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (1, 5), (1, 6)]))
                          )
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (1, 5), (1, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (1, 5), (1, 6)]))
                        )
                      )
                    )
                    (.node 0 4   -- 9
                      (.node 1 4   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 3)]))
                        )
                        (.node 1 2   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 1), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 4), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (1, 5), (1, 6)]))
                        )
                      )
                      (.node 1 2   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 2), (1, 5), (1, 6)]))
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 2), (1, 6)]))
                        )
                        (.node 0 2   -- 2
                          (.leaf (swapProd [(0, 3), (1, 5), (1, 6), (2, 4)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (1, 5), (1, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 19
                    (.node 1 2   -- 10
                      (.node 1 4   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 6), (1, 3)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (1, 3)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (1, 4), (1, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (1, 4), (1, 3)]))
                        )
                      )
                      (.node 0 2   -- 5
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 4), (0, 5), (0, 6)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 1), (0, 5), (0, 6)]))
                          )
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 6)]))
                        )
                      )
                    )
                    (.node 1 2   -- 9
                      (.node 2 5   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 2), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 6), (1, 4)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 2), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (1, 4)]))
                        )
                      )
                      (.node 0 2   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 6), (2, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 1), (0, 5), (0, 6)]))
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 5), (0, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 1), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 6), (2, 3)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 2 5   -- 44
                  (.node 2 4   -- 22
                    (.node 0 4   -- 11
                      (.node 0 2   -- 5
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 6)]))
                        )
                        (.node 2 6   -- 3
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 2)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6)]))
                          )
                        )
                      )
                      (.node 0 5   -- 6
                        (.node 2 6   -- 3
                          (.leaf (swapProd [(0, 4), (0, 3), (1, 6), (1, 2)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 6)]))
                          )
                        )
                        (.node 2 6   -- 3
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (1, 6), (1, 2)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 1), (0, 6)]))
                          )
                        )
                      )
                    )
                    (.node 0 2   -- 11
                      (.node 0 4   -- 5
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 1), (0, 6)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 6), (2, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 1), (0, 6)]))
                        )
                      )
                      (.node 0 5   -- 6
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (2, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 3), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 6), (2, 3)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 22
                    (.node 1 2   -- 10
                      (.node 0 4   -- 5
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 5), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (1, 5), (1, 4), (1, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 5), (1, 4), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 4), (0, 2), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (1, 5), (1, 4)]))
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 3), (0, 1), (0, 6)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 6), (2, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (2, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 4), (0, 1), (0, 6)]))
                        )
                      )
                    )
                    (.node 3 4   -- 12
                      (.node 3 6   -- 6
                        (.node 0 2   -- 3
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 1), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 3), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 3), (1, 6), (2, 4)]))
                        )
                        (.node 0 2   -- 3
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (1, 5), (1, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 3), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 6), (2, 4)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 0 2   -- 3
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 3), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (2, 5), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 4), (0, 1), (0, 6)]))
                        )
                        (.node 0 2   -- 3
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 1), (0, 6)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree724 : Tree 7 :=
          (.node 0 6   -- 315
            tree722
            tree723
          )

private def tree725 : Tree 7 :=
            (.node 1 6   -- 168
              (.node 1 2   -- 84
                (.node 2 6   -- 42
                  (.node 0 5   -- 21
                    (.node 1 5   -- 10
                      (.node 2 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (4, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 3), (4, 6)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 6), (0, 5), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 3)]))
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 4), (2, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 4), (2, 6), (2, 5)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (2, 5)]))
                        )
                      )
                    )
                    (.node 1 4   -- 11
                      (.node 3 5   -- 6
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 5), (0, 1), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 3)]))
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 5), (1, 3)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 3)]))
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 4), (1, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (1, 4), (1, 2), (1, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 2), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (1, 4)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 1 5   -- 10
                      (.node 2 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 4), (0, 6), (0, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 3), (4, 6)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 5), (0, 4), (0, 6), (0, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 5), (0, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 4), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 2), (0, 6), (0, 3), (4, 5)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 6), (2, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 3), (2, 6), (2, 5)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 6), (2, 4), (2, 5)]))
                        )
                      )
                    )
                    (.node 1 4   -- 11
                      (.node 3 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 3), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 5), (0, 1), (0, 3)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 3), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 5), (1, 3)]))
                          )
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 1), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (1, 4), (1, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (1, 4), (1, 2), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 2), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 5), (1, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 0 2   -- 42
                  (.node 0 5   -- 21
                    (.node 2 5   -- 10
                      (.node 1 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 3), (4, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 3), (4, 6)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 5), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3)]))
                        )
                      )
                      (.node 1 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 5), (0, 2), (0, 3)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 4), (0, 3)]))
                        )
                      )
                    )
                    (.node 2 4   -- 11
                      (.node 3 5   -- 6
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (1, 4), (1, 6), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (1, 5)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 4), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 5)]))
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 1), (0, 5)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (1, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 1), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 21
                    (.node 0 5   -- 11
                      (.node 1 5   -- 5
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (4, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 3), (4, 6)]))
                          )
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 5), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 6), (0, 5), (0, 3)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 5), (1, 2)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 5)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 6), (1, 5), (1, 2)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (1, 4), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 6), (0, 5)]))
                          )
                        )
                      )
                    )
                    (.node 0 4   -- 10
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
              (.node 2 6   -- 84
                (.node 0 2   -- 42
                  (.node 0 5   -- 21
                    (.node 1 4   -- 10
                      (.node 5 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (4, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 3), (4, 6)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 6), (0, 3)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (4, 5)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 2), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 5), (0, 2), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 5), (0, 2), (0, 4), (0, 3)]))
                        )
                      )
                    )
                    (.node 2 4   -- 11
                      (.node 3 5   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (1, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (1, 6), (1, 4), (1, 5)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 6), (0, 4), (0, 5)]))
                          )
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 1), (0, 6), (0, 5)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (1, 6), (1, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 1), (0, 6), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 5   -- 21
                    (.node 0 5   -- 10
                      (.node 1 4   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 4), (0, 6), (0, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 3), (4, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 5), (0, 4), (0, 6), (0, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 5), (0, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 4), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 1), (0, 6), (0, 3), (4, 5)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 5), (1, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (1, 6), (1, 5), (1, 2)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 3), (1, 5), (1, 2), (4, 6)]))
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 4), (1, 5), (1, 2)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 3 5   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 3), (1, 6), (1, 4), (1, 5)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (4, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 4), (0, 5)]))
                          )
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 6), (0, 5)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 1), (0, 6), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 5), (2, 3)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 2   -- 42
                  (.node 0 5   -- 21
                    (.node 2 4   -- 10
                      (.node 1 5   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 4), (2, 6)]))
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 5), (2, 4), (2, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 3), (2, 5)]))
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 2), (0, 5), (0, 3)]))
                        )
                      )
                      (.node 1 4   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 3), (2, 6), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 2), (0, 6), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 4), (0, 5), (0, 3), (2, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 6), (0, 4), (0, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 6), (0, 3)]))
                            (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (2, 6)]))
                          )
                        )
                      )
                    )
                    (.node 3 5   -- 11
                      (.node 1 4   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 4), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (1, 4), (1, 5)]))
                        )
                        (.node 0 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 3), (1, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (1, 5), (2, 6), (2, 4)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 3), (0, 1), (0, 5)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (2, 6), (2, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 4), (0, 1), (0, 5)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (1, 4), (1, 6), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 1), (0, 4), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 1), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 1 4   -- 10
                      (.node 2 5   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 1), (0, 4), (0, 6), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 4), (0, 6), (0, 2), (0, 3)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 2), (0, 4), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 1), (0, 5), (0, 3), (2, 4), (2, 6)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (2, 4), (2, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 4), (0, 5), (0, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 1), (0, 6), (0, 4), (0, 3), (2, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 3), (2, 5)]))
                            (.leaf (swapProd [(0, 1), (0, 6), (0, 2), (0, 5), (0, 3)]))
                          )
                        )
                      )
                    )
                    (.node 3 5   -- 11
                      (.node 2 4   -- 5
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 1), (0, 6), (0, 3)]))
                        )
                        (.node 0 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 6), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (0, 6), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 4), (1, 2), (1, 5)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 5), (1, 6), (1, 4), (1, 3)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 4), (0, 2), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (1, 6), (1, 4)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 3), (0, 1), (0, 5)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (1, 6), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (1, 6), (1, 3)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree726 : Tree 7 :=
            (.node 5 6   -- 147
              (.node 0 2   -- 66
                (.node 1 2   -- 34
                  (.node 0 4   -- 17
                    (.node 1 4   -- 9
                      (.node 2 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 6), (1, 2), (1, 5)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 6), (0, 2), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (1, 4), (1, 6)]))
                          )
                        )
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 5), (2, 6)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 1), (0, 4), (0, 5)]))
                          )
                        )
                      )
                      (.node 3 5   -- 3
                        (.leaf (swapProd [(0, 3), (1, 5), (2, 6)]))
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (2, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 1), (0, 5)]))
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 3 4   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 3), (0, 1), (0, 5)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (2, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 5), (2, 6)]))
                        )
                      )
                      (.node 3 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (1, 5), (2, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 5), (2, 6)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 6), (0, 1), (0, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 1), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 17
                    (.node 1 4   -- 9
                      (.node 3 5   -- 3
                        (.leaf (swapProd [(0, 3), (1, 5), (2, 4), (2, 6)]))
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (2, 4), (2, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 6), (0, 1), (0, 5)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 2), (1, 4), (1, 5)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 2), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 5), (1, 6)]))
                          )
                        )
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 2), (1, 5)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (0, 2), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (1, 6)]))
                          )
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 3 4   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 1), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (1, 6), (1, 3)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 3), (0, 2), (0, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 6), (0, 2), (0, 5)]))
                        )
                      )
                      (.node 3 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (1, 6), (1, 2), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 6), (0, 2), (0, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 5), (1, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (1, 6)]))
                        )
                      )
                    )
                  )
                )
                (.node 2 6   -- 32
                  (.node 0 4   -- 15
                    (.node 1 4   -- 6
                      (.node 2 5   -- 3
                        (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (1, 5), (1, 2)]))
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 1), (0, 5)]))
                        )
                      )
                      (.node 2 5   -- 3
                        (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 1), (0, 6), (0, 3)]))
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (1, 6), (1, 3)]))
                        )
                      )
                    )
                    (.node 3 5   -- 9
                      (.node 2 5   -- 5
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 6), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 6), (0, 3)]))
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 4), (0, 2), (0, 3)]))
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 4), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 3)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 4), (1, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 4), (2, 3)]))
                        )
                      )
                    )
                  )
                  (.node 2 4   -- 17
                    (.node 0 4   -- 9
                      (.node 1 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 3), (1, 5)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 3), (0, 1), (0, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 5), (2, 3)]))
                          )
                        )
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 6), (0, 2), (0, 3)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (1, 6), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (1, 6), (2, 3)]))
                          )
                        )
                      )
                      (.node 3 5   -- 3
                        (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 2), (0, 3)]))
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (2, 3)]))
                        )
                      )
                    )
                    (.node 4 6   -- 8
                      (.node 3 4   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 3), (2, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 3), (2, 4)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 3), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 2), (1, 4)]))
                        )
                      )
                      (.node 3 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (0, 2), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (1, 2), (1, 4), (1, 3)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (1, 6), (2, 4), (2, 3)]))
                          (.leaf (swapProd [(0, 5), (1, 6), (2, 4)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 4   -- 81
                (.node 3 6   -- 37
                  (.node 2 5   -- 18
                    (.node 1 5   -- 9
                      (.node 0 2   -- 4
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (1, 4), (1, 6)]))
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 6)]))
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 0 2   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (1, 5), (1, 4), (1, 6)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 5), (1, 4), (1, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (1, 5), (1, 4), (1, 6)]))
                          )
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 1), (0, 5), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 5), (0, 3)]))
                        )
                      )
                    )
                    (.node 0 5   -- 9
                      (.node 1 5   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 6), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 3), (4, 5)]))
                        )
                        (.node 1 2   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (1, 4), (1, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 4), (0, 5), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 1), (0, 5), (0, 3)]))
                        )
                      )
                      (.node 1 2   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 6), (2, 5)]))
                          (.leaf (swapProd [(0, 3), (1, 4), (1, 5), (1, 2), (1, 6)]))
                        )
                        (.node 0 2   -- 2
                          (.leaf (swapProd [(0, 3), (1, 5), (1, 2), (1, 4), (1, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 5), (0, 2), (0, 3)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 19
                    (.node 1 2   -- 10
                      (.node 1 5   -- 5
                        (.node 2 4   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (1, 3)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 6), (1, 3)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (1, 3), (4, 5)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 1), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (1, 4), (1, 5), (1, 3)]))
                        )
                      )
                      (.node 0 2   -- 5
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 4), (0, 6)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 5), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (1, 5), (1, 3)]))
                          )
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 4), (0, 6)]))
                        )
                      )
                    )
                    (.node 1 2   -- 9
                      (.node 2 4   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 6), (2, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 1), (0, 4), (0, 6)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 4), (0, 5), (0, 2), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (1, 4), (1, 5)]))
                        )
                      )
                      (.node 0 2   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 2), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 6), (1, 5)]))
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (1, 5), (1, 3)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (1, 5), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (1, 5), (2, 3)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 2 4   -- 44
                  (.node 2 5   -- 22
                    (.node 0 5   -- 11
                      (.node 0 2   -- 5
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (1, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (0, 6), (4, 5)]))
                        )
                        (.node 2 6   -- 3
                          (.leaf (swapProd [(0, 3), (1, 6), (1, 2), (4, 5)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (4, 5)]))
                          )
                        )
                      )
                      (.node 0 4   -- 6
                        (.node 2 6   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (1, 6), (1, 2)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 1), (0, 6)]))
                          )
                        )
                        (.node 2 6   -- 3
                          (.leaf (swapProd [(0, 5), (0, 3), (1, 6), (1, 2)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 6)]))
                          )
                        )
                      )
                    )
                    (.node 0 2   -- 11
                      (.node 0 5   -- 5
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 3), (0, 1), (0, 6)]))
                        )
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 6), (2, 4), (2, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (2, 4), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 5), (0, 1), (0, 6)]))
                        )
                      )
                      (.node 0 4   -- 6
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 3), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 6), (2, 3)]))
                        )
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (2, 3)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 22
                    (.node 1 2   -- 10
                      (.node 0 5   -- 5
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (0, 5), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (1, 5), (1, 3)]))
                        )
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 5), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 5), (0, 2), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (1, 5)]))
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 1), (0, 6)]))
                        )
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 6), (2, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 1), (0, 6)]))
                        )
                      )
                    )
                    (.node 3 5   -- 12
                      (.node 3 6   -- 6
                        (.node 0 2   -- 3
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (1, 5), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (1, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 3), (1, 6)]))
                        )
                        (.node 0 2   -- 3
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 5), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 3), (0, 1), (0, 6)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 0 2   -- 3
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 5), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (2, 4), (2, 3)]))
                        )
                        (.node 0 2   -- 3
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 1), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 6), (2, 4)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree727 : Tree 7 :=
          (.node 0 6   -- 315
            tree725
            tree726
          )

private def tree728 : Tree 7 :=
        (.node 4 5   -- 630
          tree724
          tree727
        )

private def tree729 : Tree 7 :=
      (.node 0 3   -- 1260
        tree721
        tree728
      )

private def tree730 : Tree 7 :=
    (.node 2 3   -- 2520
      tree714
      tree729
    )

private def tree731 : Tree 7 :=
            (.node 5 6   -- 147
              (.node 1 4   -- 81
                (.node 2 4   -- 44
                  (.node 0 4   -- 22
                    (.node 3 5   -- 12
                      (.node 3 4   -- 6
                        (.node 0 2   -- 3
                          (.leaf (swapProd [(0, 1)]))
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 2)]))
                          )
                        )
                        (.node 0 2   -- 3
                          (.leaf (swapProd [(0, 1), (3, 4)]))
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (3, 4)]))
                            (.leaf (swapProd [(0, 2), (3, 4)]))
                          )
                        )
                      )
                      (.node 3 6   -- 6
                        (.node 0 2   -- 3
                          (.leaf (swapProd [(0, 1), (3, 5), (3, 4)]))
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (3, 5), (3, 4)]))
                            (.leaf (swapProd [(0, 2), (3, 5), (3, 4)]))
                          )
                        )
                        (.node 0 2   -- 3
                          (.leaf (swapProd [(0, 1), (3, 6), (3, 5), (3, 4)]))
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (3, 6), (3, 5), (3, 4)]))
                            (.leaf (swapProd [(0, 2), (3, 6), (3, 5), (3, 4)]))
                          )
                        )
                      )
                    )
                    (.node 1 2   -- 10
                      (.node 0 5   -- 5
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 1)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 4), (0, 2), (0, 1)]))
                          )
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (3, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (3, 6), (3, 5)]))
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 4), (0, 2)]))
                          )
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (3, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (3, 6), (3, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 5   -- 22
                    (.node 0 2   -- 11
                      (.node 0 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 4)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 1), (2, 3), (2, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 1), (2, 3), (2, 6), (2, 5), (2, 4)]))
                          )
                        )
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 1)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 5), (0, 4), (0, 1)]))
                          )
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 4), (0, 1)]))
                          )
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (3, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (3, 6), (3, 5)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 0 4   -- 6
                        (.node 2 6   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 1), (2, 4), (3, 5)]))
                            (.leaf (swapProd [(0, 1), (2, 4), (3, 6), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 3), (2, 6), (2, 4)]))
                        )
                        (.node 2 6   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (3, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (3, 6), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 6), (0, 4), (0, 1)]))
                        )
                      )
                      (.node 0 2   -- 5
                        (.node 2 6   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 2), (0, 4), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 1), (2, 5)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (2, 3), (2, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (2, 3), (2, 6), (2, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 3 6   -- 37
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
                  (.node 2 5   -- 18
                    (.node 0 5   -- 9
                      (.node 1 2   -- 4
                        (.node 0 2   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 5), (0, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 4)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 4), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 4), (1, 2)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 4), (3, 6), (3, 5)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (3, 6), (3, 5)]))
                            (.leaf (swapProd [(0, 4), (1, 2), (3, 6), (3, 5)]))
                          )
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 6), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (1, 3), (1, 6), (1, 5), (1, 2)]))
                        )
                      )
                    )
                    (.node 1 5   -- 9
                      (.node 0 5   -- 5
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (3, 6), (3, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 6), (0, 4)]))
                        )
                        (.node 0 2   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 4), (2, 3), (2, 6), (2, 5)]))
                        )
                      )
                      (.node 0 2   -- 4
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 1), (0, 2), (0, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (1, 2), (1, 5)]))
                        )
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(0, 4), (1, 2), (1, 3), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (1, 3), (1, 6), (1, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 0 2   -- 66
                (.node 2 6   -- 32
                  (.node 2 4   -- 17
                    (.node 4 6   -- 8
                      (.node 3 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (5, 6)]))
                          (.leaf (swapProd [(0, 1), (3, 4), (5, 6)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (3, 5), (3, 6), (3, 4)]))
                          (.leaf (swapProd [(0, 1), (3, 6), (3, 4)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 1), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 1), (3, 4), (3, 5), (3, 6)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (3, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (3, 6)]))
                        )
                      )
                    )
                    (.node 0 4   -- 9
                      (.node 3 5   -- 3
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 4), (5, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 5), (2, 6), (2, 4)]))
                        )
                        (.leaf (swapProd [(0, 1), (2, 3), (2, 6), (2, 4)]))
                      )
                      (.node 1 4   -- 6
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 1), (5, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 6), (0, 4), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 4), (0, 1)]))
                        )
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (5, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 6), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 15
                    (.node 3 5   -- 9
                      (.node 2 4   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 4), (2, 5), (2, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 5), (2, 6)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 4), (3, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 3), (2, 5), (2, 6)]))
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (2, 4), (3, 6)]))
                            (.leaf (swapProd [(0, 1), (2, 4), (2, 3), (2, 6)]))
                          )
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 4), (2, 3), (2, 6)]))
                        )
                      )
                    )
                    (.node 1 4   -- 6
                      (.node 2 5   -- 3
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (3, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (3, 6)]))
                        )
                        (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 1), (3, 6)]))
                      )
                      (.node 2 5   -- 3
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (3, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (3, 6)]))
                        )
                        (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (3, 6)]))
                      )
                    )
                  )
                )
                (.node 1 2   -- 34
                  (.node 0 4   -- 17
                    (.node 4 6   -- 8
                      (.node 3 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (5, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 4), (5, 6)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 5), (3, 6), (3, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 6), (3, 4)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 4), (3, 5), (3, 6)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 6)]))
                        )
                      )
                    )
                    (.node 1 4   -- 9
                      (.node 2 4   -- 6
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 1), (5, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 4), (0, 2), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 2), (0, 1)]))
                        )
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (5, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 4), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 1)]))
                        )
                      )
                      (.node 3 5   -- 3
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (5, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 4)]))
                        )
                        (.leaf (swapProd [(0, 3), (0, 6), (0, 4)]))
                      )
                    )
                  )
                  (.node 0 4   -- 17
                    (.node 4 6   -- 8
                      (.node 3 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (5, 6)]))
                          (.leaf (swapProd [(0, 2), (3, 4), (5, 6)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (3, 5), (3, 6), (3, 4)]))
                          (.leaf (swapProd [(0, 2), (3, 6), (3, 4)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (3, 4), (3, 5), (3, 6)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (3, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 2), (3, 6)]))
                        )
                      )
                    )
                    (.node 1 4   -- 9
                      (.node 3 5   -- 3
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (5, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 4), (0, 2)]))
                        )
                        (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 2)]))
                      )
                      (.node 2 4   -- 6
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 2), (5, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 4), (0, 1), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 1), (0, 2)]))
                        )
                        (.node 3 5   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (1, 2), (5, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 4), (1, 2)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (1, 2)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree732 : Tree 7 :=
            (.node 1 6   -- 168
              (.node 2 6   -- 84
                (.node 1 2   -- 42
                  (.node 0 5   -- 21
                    (.node 3 5   -- 11
                      (.node 4 6   -- 6
                        (.node 1 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (3, 5), (3, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (3, 5), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (3, 5), (3, 6)]))
                        )
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 6), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 2), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 6), (0, 2), (0, 1)]))
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 1)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (3, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 2), (0, 1)]))
                          )
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (3, 6)]))
                          (.leaf (swapProd [(0, 4), (3, 6)]))
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 2 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 4), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 1), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 6), (0, 2), (0, 1)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 6), (0, 4), (0, 1)]))
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (3, 6)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 3), (0, 6), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 3 5   -- 11
                      (.node 4 6   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (3, 5), (3, 6)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (3, 5), (3, 6)]))
                            (.leaf (swapProd [(0, 4), (1, 2), (3, 5), (3, 6)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 6), (0, 2)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (3, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 2)]))
                          )
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (3, 6)]))
                          (.leaf (swapProd [(0, 4), (1, 2), (3, 6)]))
                        )
                      )
                    )
                    (.node 2 4   -- 10
                      (.node 1 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 6), (0, 2)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 4), (0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 2), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (1, 3), (1, 6), (1, 4)]))
                        )
                      )
                      (.node 1 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 4), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 2), (3, 6)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 3), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 6), (0, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 0 2   -- 42
                  (.node 2 5   -- 21
                    (.node 0 4   -- 11
                      (.node 2 4   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 1)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 6), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 1)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 5), (0, 6), (0, 1)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 6), (0, 1)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 2), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 1), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 2), (0, 4)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 4)]))
                        )
                      )
                    )
                    (.node 0 5   -- 10
                      (.node 4 6   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 5), (0, 4), (0, 1)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 5), (0, 4)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 3), (0, 6), (0, 1)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (2, 5), (2, 4)]))
                        )
                      )
                      (.node 1 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (2, 5), (3, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (2, 5), (2, 3), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 3), (0, 6), (0, 1)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (2, 5), (3, 6)]))
                            (.leaf (swapProd [(0, 4), (2, 5), (2, 3), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (1, 2), (1, 5), (3, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 2 4   -- 11
                      (.node 0 4   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 6), (0, 1)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 1)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 6), (0, 1)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 1)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (2, 3), (2, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 5), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (2, 3), (2, 5), (2, 6)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (2, 3), (2, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (2, 3), (2, 6)]))
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 2 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 6), (0, 1)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (2, 3), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 3), (0, 6), (0, 1)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 1), (3, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 2), (0, 4), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 1), (2, 4)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 4), (3, 6)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (2, 3), (2, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 2), (0, 4)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 2   -- 84
                (.node 0 2   -- 42
                  (.node 1 4   -- 21
                    (.node 0 4   -- 10
                      (.node 2 4   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 6)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 3), (0, 6)]))
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (2, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (2, 4)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 6), (2, 5), (2, 4)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 3), (0, 6)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 4 6   -- 6
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 1), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 2), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 2), (0, 5), (0, 4)]))
                        )
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (1, 2), (1, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (1, 2), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (1, 2), (1, 5), (1, 4)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 4), (1, 2), (1, 5), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 5), (0, 3), (0, 6)]))
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 3), (1, 6), (1, 2), (1, 5)]))
                            (.leaf (swapProd [(0, 4), (1, 3), (1, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 6), (2, 5)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 2 4   -- 11
                      (.node 0 4   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 6)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 5), (0, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 2), (1, 3), (1, 5), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 2), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 3), (0, 6)]))
                          )
                        )
                      )
                    )
                    (.node 2 5   -- 10
                      (.node 1 4   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 3), (0, 6)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 2), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 2), (0, 3), (0, 6)]))
                        )
                      )
                      (.node 1 5   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (2, 4)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 1), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (1, 2), (1, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 6), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (1, 3), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 1), (0, 3), (0, 6)]))
                        )
                      )
                    )
                  )
                )
                (.node 2 6   -- 42
                  (.node 0 5   -- 21
                    (.node 1 4   -- 11
                      (.node 0 4   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 6), (0, 1), (0, 2)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 2)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 6), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 1), (0, 2)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 5), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (1, 3), (1, 5), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (1, 3), (1, 5), (1, 6), (1, 2)]))
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (1, 3), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (1, 3), (1, 6), (1, 2)]))
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 4 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 3), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 3), (1, 6), (1, 2)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 6), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (1, 3), (1, 6)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (1, 4), (3, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 2), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 1), (0, 4), (0, 2)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 4), (3, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 2), (0, 1), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (3, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 1 4   -- 11
                      (.node 0 4   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 6), (1, 2)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (1, 2)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (1, 2)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 3), (0, 5), (0, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 3), (1, 5), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 5), (0, 6)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 3), (0, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 6)]))
                          )
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 2 4   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 1), (0, 3), (0, 6)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 3), (0, 6)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (1, 4), (1, 2)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (1, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (2, 3), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 6), (0, 1), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 6), (1, 4)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree733 : Tree 7 :=
          (.node 0 6   -- 315
            tree731
            tree732
          )

private def tree734 : Tree 7 :=
            (.node 4 6   -- 147
              (.node 1 5   -- 81
                (.node 2 5   -- 44
                  (.node 0 5   -- 22
                    (.node 3 4   -- 12
                      (.node 3 5   -- 6
                        (.node 0 2   -- 3
                          (.leaf (swapProd [(0, 1), (4, 5)]))
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (4, 5)]))
                            (.leaf (swapProd [(0, 2), (4, 5)]))
                          )
                        )
                        (.node 0 2   -- 3
                          (.leaf (swapProd [(0, 1), (3, 4), (3, 5)]))
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (3, 4), (3, 5)]))
                            (.leaf (swapProd [(0, 2), (3, 4), (3, 5)]))
                          )
                        )
                      )
                      (.node 3 6   -- 6
                        (.node 0 2   -- 3
                          (.leaf (swapProd [(0, 1), (3, 5)]))
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (3, 5)]))
                            (.leaf (swapProd [(0, 2), (3, 5)]))
                          )
                        )
                        (.node 0 2   -- 3
                          (.leaf (swapProd [(0, 1), (3, 6), (3, 5)]))
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 2), (0, 1), (3, 6), (3, 5)]))
                            (.leaf (swapProd [(0, 2), (3, 6), (3, 5)]))
                          )
                        )
                      )
                    )
                    (.node 1 2   -- 10
                      (.node 0 4   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 2), (0, 1)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 2), (0, 1)]))
                          )
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 2), (0, 1)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 5), (0, 2), (0, 1)]))
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 2)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 2)]))
                          )
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 5), (0, 2)]))
                        )
                      )
                    )
                  )
                  (.node 2 4   -- 22
                    (.node 0 2   -- 11
                      (.node 0 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 4), (2, 5)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 1), (2, 3), (2, 5)]))
                            (.leaf (swapProd [(0, 1), (2, 3), (2, 6), (2, 5)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 5), (0, 1)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 5), (0, 1)]))
                          )
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 1)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 1)]))
                          )
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 1)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 5), (0, 1)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 0 5   -- 6
                        (.node 2 6   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 1), (2, 4), (2, 3), (2, 5)]))
                            (.leaf (swapProd [(0, 1), (2, 4), (2, 3), (2, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 1), (2, 5), (3, 6), (3, 4)]))
                        )
                        (.node 2 6   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 6), (0, 5), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (3, 6), (3, 4)]))
                        )
                      )
                      (.node 0 2   -- 5
                        (.node 2 6   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (2, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 1), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 2), (0, 5), (0, 1)]))
                        )
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 5), (0, 1)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 6), (0, 5), (0, 1)]))
                        )
                      )
                    )
                  )
                )
                (.node 3 6   -- 37
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
                  (.node 2 4   -- 18
                    (.node 0 4   -- 9
                      (.node 1 2   -- 4
                        (.node 0 2   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 5)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (1, 2)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 5)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 5), (0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 5), (1, 2)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (1, 3), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 3), (0, 6), (0, 5)]))
                        )
                      )
                    )
                    (.node 1 4   -- 9
                      (.node 0 4   -- 5
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 6), (0, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 5), (3, 6), (3, 4)]))
                        )
                        (.node 0 2   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 2), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 6), (0, 5)]))
                        )
                      )
                      (.node 0 2   -- 4
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 5), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 1), (0, 2), (0, 5)]))
                        )
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 3), (0, 6), (0, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 6), (0, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 0 2   -- 66
                (.node 2 6   -- 32
                  (.node 2 5   -- 17
                    (.node 5 6   -- 8
                      (.node 3 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 1), (3, 4), (3, 6), (3, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (3, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 1), (3, 6), (3, 4), (3, 5)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 1), (4, 6)]))
                          (.leaf (swapProd [(0, 1), (3, 4), (3, 6)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 1), (3, 5), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (3, 6), (4, 5)]))
                        )
                      )
                    )
                    (.node 0 5   -- 9
                      (.node 3 4   -- 3
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 4), (2, 6), (2, 5)]))
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 5), (4, 6)]))
                        )
                        (.leaf (swapProd [(0, 1), (2, 3), (2, 6), (2, 4), (2, 5)]))
                      )
                      (.node 1 5   -- 6
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 6), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 1), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 4), (0, 5), (0, 1)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 4), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 15
                    (.node 3 4   -- 9
                      (.node 2 5   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 4), (2, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 5), (2, 4), (2, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 6), (2, 3), (2, 5)]))
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 6), (3, 5)]))
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 1), (2, 3), (2, 6), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (2, 4), (2, 5), (3, 6)]))
                            (.leaf (swapProd [(0, 1), (2, 4), (2, 5), (2, 3), (2, 6)]))
                          )
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 5), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 3), (2, 6)]))
                        )
                      )
                    )
                    (.node 1 5   -- 6
                      (.node 2 4   -- 3
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 3), (0, 5), (0, 1)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 1), (3, 6)]))
                        )
                        (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (3, 6)]))
                      )
                      (.node 2 4   -- 3
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 3), (0, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (3, 6)]))
                        )
                        (.leaf (swapProd [(0, 2), (0, 5), (3, 6)]))
                      )
                    )
                  )
                )
                (.node 1 2   -- 34
                  (.node 0 5   -- 17
                    (.node 5 6   -- 8
                      (.node 3 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 4), (3, 6), (3, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 6), (3, 4), (3, 5)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 4), (3, 6)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 5), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 1), (3, 6), (4, 5)]))
                        )
                      )
                    )
                    (.node 1 5   -- 9
                      (.node 2 5   -- 6
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 5), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 1), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 5), (0, 2), (0, 1)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 5), (0, 1)]))
                        )
                      )
                      (.node 3 4   -- 3
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (4, 6)]))
                        )
                        (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 5)]))
                      )
                    )
                  )
                  (.node 0 5   -- 17
                    (.node 5 6   -- 8
                      (.node 3 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 2), (3, 4), (3, 6), (3, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (3, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (3, 6), (3, 4), (3, 5)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (3, 4), (3, 6)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (3, 5), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 2), (3, 6), (4, 5)]))
                        )
                      )
                    )
                    (.node 1 5   -- 9
                      (.node 3 4   -- 3
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (4, 6)]))
                        )
                        (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 5), (0, 2)]))
                      )
                      (.node 2 5   -- 6
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 5), (0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 2), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 5), (0, 1), (0, 2)]))
                        )
                        (.node 3 4   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 5), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (1, 2), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 4), (0, 5), (1, 2)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree735 : Tree 7 :=
            (.node 1 6   -- 168
              (.node 2 6   -- 84
                (.node 1 2   -- 42
                  (.node 0 4   -- 21
                    (.node 3 4   -- 11
                      (.node 5 6   -- 6
                        (.node 1 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 5), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 5), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 5)]))
                        )
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 6), (0, 2), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 1), (3, 5)]))
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 1), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 1), (3, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 6), (0, 2), (0, 1)]))
                          )
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (3, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (3, 6)]))
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 2 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (3, 6), (3, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (3, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 2), (0, 1)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (3, 6), (3, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (2, 3), (2, 6), (2, 4)]))
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (3, 6), (3, 4)]))
                          (.leaf (swapProd [(0, 5), (3, 6)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (2, 3), (2, 6), (2, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 3), (1, 6), (1, 4)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 3 4   -- 11
                      (.node 5 6   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 5), (0, 2)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 5), (0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 5), (1, 2)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 6), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (3, 5)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (3, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 6), (0, 2)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 2), (3, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (1, 2), (3, 6)]))
                        )
                      )
                    )
                    (.node 2 5   -- 10
                      (.node 1 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (3, 6), (3, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (3, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 2)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (3, 6), (3, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (3, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 6), (0, 4), (0, 2)]))
                        )
                      )
                      (.node 1 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 2), (3, 6), (3, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 2), (3, 6)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 6), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 6), (1, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 0 2   -- 42
                  (.node 2 4   -- 21
                    (.node 0 5   -- 11
                      (.node 2 5   -- 5
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 6), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 4), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (0, 1), (4, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 1), (3, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 3), (0, 6), (0, 1)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (2, 4), (2, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 4), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 5), (2, 4), (2, 6)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 4), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (2, 4), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 4), (0, 5)]))
                        )
                      )
                    )
                    (.node 0 4   -- 10
                      (.node 5 6   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 5), (0, 1)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 2), (0, 5)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 6), (0, 1)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (2, 5)]))
                        )
                      )
                      (.node 1 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 1), (3, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 2), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 1), (2, 5)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (3, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 2), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 5), (3, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 2 5   -- 11
                      (.node 0 5   -- 5
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (4, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (3, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 6), (0, 1)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 3), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (2, 3), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 3), (0, 5)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (2, 3), (2, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 3), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 5), (2, 3), (2, 6)]))
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 2 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 1)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (2, 3), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 6), (0, 1)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (0, 1), (2, 4), (3, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (2, 4), (2, 3), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 3), (0, 6), (0, 1)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (2, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 4), (3, 6)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 5), (2, 3), (2, 6)]))
                          (.leaf (swapProd [(0, 5), (2, 4), (2, 3), (2, 6)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 2   -- 84
                (.node 0 2   -- 42
                  (.node 1 5   -- 21
                    (.node 0 5   -- 10
                      (.node 2 5   -- 6
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 5), (0, 4), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 6), (4, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (3, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 3), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 6)]))
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 6), (2, 4), (2, 5)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 6), (2, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (2, 5)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 5 6   -- 6
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (1, 2), (1, 4), (1, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 2), (0, 4), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 2), (0, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 2), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 6), (1, 2), (1, 4), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (1, 2), (1, 5)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (0, 1), (0, 2), (0, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 6), (1, 2), (1, 5)]))
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 6), (0, 2), (0, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 1), (0, 3), (0, 6)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 2 5   -- 11
                      (.node 0 5   -- 5
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (4, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (3, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 6)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (2, 3), (2, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 2), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (1, 2), (1, 3), (1, 5)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 3), (0, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (1, 2), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 2), (0, 3), (0, 6)]))
                          )
                        )
                      )
                    )
                    (.node 2 4   -- 10
                      (.node 1 5   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 3), (0, 6)]))
                        )
                      )
                      (.node 1 4   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 3), (0, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 2), (1, 4), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 4), (0, 3), (0, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 6), (1, 2), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 3), (1, 6), (2, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 6), (2, 4)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 2 6   -- 42
                  (.node 0 4   -- 21
                    (.node 1 5   -- 11
                      (.node 0 5   -- 5
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 6), (0, 1), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (0, 1), (0, 2), (4, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 2), (3, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 6), (0, 1), (0, 2)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (1, 3), (1, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 3), (0, 5), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 1), (0, 3), (0, 5)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 3), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (1, 3), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 5), (1, 3), (1, 6), (1, 2)]))
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 5 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 6), (1, 2)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (1, 3), (1, 6)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 2), (3, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 3), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (1, 4), (1, 3), (1, 6)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 4), (1, 2), (3, 6)]))
                            (.leaf (swapProd [(0, 5), (1, 4), (1, 3), (1, 6), (1, 2)]))
                          )
                          (.leaf (swapProd [(0, 5), (1, 4), (3, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 1 5   -- 11
                      (.node 0 5   -- 5
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (1, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 6), (1, 2)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 6), (1, 2), (4, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (1, 2), (3, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 6), (1, 2)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (1, 3), (1, 5), (1, 2)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (1, 3), (1, 5)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 1), (0, 3), (0, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 3), (0, 6)]))
                          )
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 2 5   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 3), (0, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 6)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 4), (0, 3), (0, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 4), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 3), (0, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (1, 4), (2, 3), (2, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 4), (1, 2), (1, 3), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 2), (0, 3), (0, 6)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree736 : Tree 7 :=
          (.node 0 6   -- 315
            tree734
            tree735
          )

private def tree737 : Tree 7 :=
        (.node 4 5   -- 630
          tree733
          tree736
        )

private def tree738 : Tree 7 :=
            (.node 5 6   -- 147
              (.node 2 4   -- 81
                (.node 1 4   -- 44
                  (.node 3 4   -- 22
                    (.node 0 5   -- 12
                      (.node 0 4   -- 6
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 2)]))
                          )
                        )
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 1)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 2)]))
                          )
                        )
                      )
                      (.node 0 6   -- 6
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 2), (0, 1)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 1), (0, 2)]))
                          )
                        )
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 3), (0, 2), (0, 1)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 3), (0, 1), (0, 2)]))
                          )
                        )
                      )
                    )
                    (.node 1 2   -- 10
                      (.node 0 6   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 1)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 2), (0, 1)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 2), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 4), (0, 2), (0, 1)]))
                        )
                      )
                      (.node 0 6   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 2)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 4), (0, 2)]))
                        )
                      )
                    )
                  )
                  (.node 0 6   -- 22
                    (.node 1 3   -- 11
                      (.node 3 5   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 2)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (1, 3), (1, 4)]))
                        )
                      )
                      (.node 1 5   -- 7
                        (.node 0 5   -- 4
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 2)]))
                          )
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 3), (0, 2)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 4), (0, 2)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (1, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (1, 4)]))
                          )
                        )
                      )
                    )
                    (.node 1 5   -- 11
                      (.node 1 3   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 4), (0, 1), (0, 2)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 1), (0, 3), (0, 2)]))
                        )
                      )
                      (.node 1 6   -- 7
                        (.node 3 5   -- 4
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 1), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 2), (1, 4)]))
                          )
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (1, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (1, 4)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (1, 5), (1, 3)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 5), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 5), (0, 2)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 0 6   -- 37
                  (.node 1 2   -- 19
                    (.node 1 4   -- 9
                      (.node 3 5   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 1)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 4), (0, 1)]))
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 4)]))
                          )
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 3), (0, 4)]))
                        )
                      )
                    )
                    (.node 1 3   -- 10
                      (.node 1 5   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (1, 2)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (1, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (1, 2)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 3), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 4)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (1, 3), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 3), (1, 2)]))
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
                  (.node 1 5   -- 18
                    (.node 3 5   -- 9
                      (.node 1 2   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4)]))
                        )
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (1, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (1, 3), (1, 2)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 4), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 3), (0, 4), (0, 1)]))
                        )
                        (.node 1 2   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 3), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 4), (1, 2)]))
                        )
                      )
                    )
                    (.node 2 5   -- 9
                      (.node 1 6   -- 5
                        (.node 1 3   -- 3
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 1), (0, 3), (0, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 2), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 1), (0, 4)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 5), (1, 3), (1, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 5), (1, 2)]))
                        )
                      )
                      (.node 1 3   -- 4
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 2), (0, 3), (0, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 3), (0, 4)]))
                        )
                        (.node 1 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 3   -- 66
                (.node 1 2   -- 34
                  (.node 3 4   -- 17
                    (.node 4 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (5, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 1), (5, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 3), (0, 2), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 2), (0, 1)]))
                        )
                      )
                      (.node 0 4   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 3), (0, 2), (0, 1)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 2), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 1)]))
                        )
                      )
                    )
                    (.node 0 5   -- 9
                      (.node 0 6   -- 6
                        (.node 1 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (5, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (5, 6)]))
                        )
                        (.node 1 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4)]))
                        )
                      )
                      (.node 1 4   -- 3
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1)]))
                        )
                        (.leaf (swapProd [(0, 6), (0, 4)]))
                      )
                    )
                  )
                  (.node 3 4   -- 17
                    (.node 4 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (5, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (5, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 3), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 2)]))
                        )
                      )
                      (.node 0 4   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 3), (0, 2)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2)]))
                        )
                      )
                    )
                    (.node 0 5   -- 9
                      (.node 0 6   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (5, 6)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (5, 6)]))
                            (.leaf (swapProd [(0, 4), (1, 2), (5, 6)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 2)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (1, 2)]))
                          )
                        )
                      )
                      (.node 1 4   -- 3
                        (.leaf (swapProd [(0, 6), (0, 4), (0, 2)]))
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 2)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 6   -- 32
                  (.node 1 4   -- 17
                    (.node 4 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (5, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 2), (5, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 3), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 1), (0, 2)]))
                        )
                      )
                      (.node 0 4   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 3), (0, 1), (0, 2)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 2)]))
                        )
                      )
                    )
                    (.node 0 5   -- 9
                      (.node 0 6   -- 6
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (1, 3), (5, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 2), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (1, 3), (1, 2), (5, 6)]))
                        )
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 1), (0, 3), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (1, 3), (1, 2)]))
                        )
                      )
                      (.node 2 4   -- 3
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 3), (0, 2)]))
                        )
                        (.leaf (swapProd [(0, 6), (0, 4), (1, 3), (1, 2)]))
                      )
                    )
                  )
                  (.node 0 5   -- 15
                    (.node 4 6   -- 6
                      (.node 2 4   -- 3
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 1), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 2), (1, 4)]))
                        )
                        (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 2), (0, 1), (0, 4)]))
                      )
                      (.node 0 4   -- 3
                        (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 2), (1, 3)]))
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (1, 4), (1, 3)]))
                        )
                      )
                    )
                    (.node 1 5   -- 9
                      (.node 3 4   -- 5
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (1, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 4), (1, 3)]))
                          )
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (1, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 1), (0, 4)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 5), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (1, 5), (1, 4), (1, 3)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (1, 5), (1, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 1), (0, 5), (0, 4)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree739 : Tree 7 :=
            (.node 2 6   -- 168
              (.node 1 6   -- 84
                (.node 1 2   -- 42
                  (.node 2 4   -- 21
                    (.node 0 5   -- 10
                      (.node 3 4   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 2), (0, 1)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 1)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 4), (0, 2), (0, 1)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 1), (3, 4)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (3, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 1), (3, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 4), (0, 2), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (3, 5), (3, 4)]))
                        )
                      )
                    )
                    (.node 1 4   -- 11
                      (.node 3 5   -- 5
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 4), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 1)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (3, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 4), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (2, 3), (2, 5)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 1 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (3, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 4), (2, 3), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 2), (1, 3), (1, 5)]))
                        )
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 4)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 21
                    (.node 0 5   -- 10
                      (.node 3 4   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 4), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (3, 4)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (3, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (3, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 4), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (3, 5), (3, 4)]))
                        )
                      )
                    )
                    (.node 2 4   -- 11
                      (.node 3 5   -- 5
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 4), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 1), (0, 2)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 2), (3, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 4), (0, 1), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 3), (0, 5), (0, 2)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 2), (3, 5)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (1, 3), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 4), (1, 3), (1, 5)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 4), (1, 2)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 4), (1, 2)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 42
                  (.node 3 5   -- 21
                    (.node 0 5   -- 11
                      (.node 1 4   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 1), (0, 2)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 2), (3, 4)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (1, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 3), (0, 4), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 1), (0, 3), (0, 4)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (3, 4)]))
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 4), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 3), (0, 4)]))
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 4 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (1, 3), (1, 5), (1, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 3), (0, 5), (0, 4)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (3, 5), (3, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 5), (0, 4), (0, 2)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 2), (1, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 4), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 2), (3, 5)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 2), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 4), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 1), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 21
                    (.node 0 5   -- 11
                      (.node 3 4   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 1), (0, 3), (0, 2)]))
                          (.node 1 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 4), (0, 3), (0, 2)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (1, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 4), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 1), (0, 4)]))
                        )
                      )
                      (.node 3 4   -- 5
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 3), (0, 2)]))
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 4)]))
                        )
                      )
                    )
                    (.node 2 4   -- 10
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 4), (0, 3), (0, 2)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 5), (1, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 4), (0, 2)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 1), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 5), (1, 3), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 3), (0, 4), (0, 2)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (1, 5), (1, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (1, 5)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 5), (0, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 5), (0, 3), (0, 4)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 2   -- 84
                (.node 1 6   -- 42
                  (.node 3 5   -- 21
                    (.node 0 5   -- 11
                      (.node 2 4   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 1)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (3, 4)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 3), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (2, 3), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 3), (0, 4)]))
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (3, 4)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (2, 3), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 4)]))
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 2 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 1), (3, 5), (3, 4)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 5), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (2, 3), (2, 5), (2, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 2), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 1), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 1), (2, 4), (3, 5)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 2), (0, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 1), (0, 2), (0, 4)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 5), (0, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (3, 5)]))
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 21
                    (.node 0 5   -- 10
                      (.node 3 4   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 6)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (3, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (2, 3), (2, 4)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (3, 4)]))
                            (.leaf (swapProd [(0, 6), (3, 5), (3, 4)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (2, 3), (2, 4)]))
                            (.leaf (swapProd [(0, 6), (2, 3), (2, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (2, 4), (3, 5)]))
                        )
                      )
                    )
                    (.node 2 5   -- 11
                      (.node 4 6   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 2), (0, 3), (0, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 3), (0, 5), (0, 4)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (1, 2), (1, 3), (1, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (1, 2), (1, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 6), (1, 2), (1, 3), (1, 5), (1, 4)]))
                          )
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 4), (3, 5)]))
                          (.leaf (swapProd [(0, 6), (1, 2), (1, 4), (3, 5)]))
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (1, 3), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 5), (0, 2), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (1, 3), (1, 5), (1, 2), (1, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 42
                  (.node 2 4   -- 21
                    (.node 0 5   -- 10
                      (.node 3 4   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (1, 2)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (1, 2), (3, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (1, 3), (1, 4), (1, 2)]))
                        )
                      )
                      (.node 1 4   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6), (1, 2)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (1, 2), (3, 4)]))
                            (.leaf (swapProd [(0, 6), (1, 2), (3, 5), (3, 4)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 4), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 5), (1, 4), (1, 2)]))
                          )
                          (.leaf (swapProd [(0, 6), (1, 4), (1, 2), (3, 5)]))
                        )
                      )
                    )
                    (.node 1 5   -- 11
                      (.node 4 6   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 3), (0, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 5), (0, 4)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (1, 3), (1, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 5), (1, 4)]))
                          )
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (3, 5)]))
                          (.leaf (swapProd [(0, 6), (1, 4), (3, 5)]))
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 5), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (2, 3), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (1, 4), (2, 3), (2, 5)]))
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 21
                    (.node 0 5   -- 11
                      (.node 3 4   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (1, 3), (1, 2)]))
                          (.node 1 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (1, 3), (1, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (1, 4), (1, 3), (1, 2)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (1, 4), (1, 2)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (1, 4)]))
                          )
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 6), (1, 3), (1, 2)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (1, 4), (1, 3), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (1, 4), (1, 2)]))
                          )
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 4)]))
                          (.leaf (swapProd [(0, 6), (1, 4)]))
                        )
                      )
                    )
                    (.node 3 5   -- 10
                      (.node 2 4   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 4), (1, 3), (1, 2)]))
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 4), (1, 2)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 4)]))
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 4)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 3), (1, 4), (1, 2)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (1, 5), (1, 3), (1, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 2), (0, 3), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 2), (1, 3), (1, 4)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree740 : Tree 7 :=
          (.node 3 6   -- 315
            tree738
            tree739
          )

private def tree741 : Tree 7 :=
            (.node 4 6   -- 147
              (.node 2 5   -- 81
                (.node 1 5   -- 44
                  (.node 3 5   -- 22
                    (.node 0 4   -- 12
                      (.node 0 5   -- 6
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (4, 5)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (4, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (4, 5)]))
                          )
                        )
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 2), (0, 1)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 1), (0, 2)]))
                          )
                        )
                      )
                      (.node 0 6   -- 6
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 1)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 2)]))
                          )
                        )
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 2), (0, 1)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 1), (0, 2)]))
                          )
                        )
                      )
                    )
                    (.node 1 2   -- 10
                      (.node 0 6   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 1)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (3, 4)]))
                          )
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 1), (3, 4)]))
                        )
                      )
                      (.node 0 6   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 2)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (3, 4)]))
                          )
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (3, 4)]))
                        )
                      )
                    )
                  )
                  (.node 0 6   -- 22
                    (.node 1 3   -- 11
                      (.node 3 4   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (3, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 4), (0, 2)]))
                        )
                      )
                      (.node 1 4   -- 7
                        (.node 0 4   -- 4
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 3), (0, 2)]))
                          )
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 2)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (1, 4), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 3), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 2)]))
                        )
                      )
                    )
                    (.node 1 4   -- 11
                      (.node 1 3   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 2), (3, 4)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 3), (0, 2)]))
                        )
                      )
                      (.node 1 6   -- 7
                        (.node 3 4   -- 4
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (1, 4), (1, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 4), (0, 3), (0, 2)]))
                          )
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 3), (0, 4), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 4), (0, 2)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 1), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 2), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (1, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 0 6   -- 37
                  (.node 1 2   -- 19
                    (.node 1 5   -- 9
                      (.node 3 4   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1)]))
                          (.leaf (swapProd [(0, 5), (0, 1)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (3, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (2, 3), (2, 4)]))
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5)]))
                            (.leaf (swapProd [(0, 5), (3, 4)]))
                          )
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (2, 3), (2, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 3), (1, 4)]))
                        )
                      )
                    )
                    (.node 1 3   -- 10
                      (.node 1 4   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (1, 2)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (1, 2)]))
                            (.leaf (swapProd [(0, 5), (1, 2), (3, 4)]))
                          )
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 4)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (1, 3), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 2)]))
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
                  (.node 1 4   -- 18
                    (.node 3 4   -- 9
                      (.node 1 2   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 5)]))
                        )
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 3), (1, 2)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (3, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (2, 3), (2, 4)]))
                        )
                        (.node 1 2   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (3, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (2, 3), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 2), (3, 4)]))
                        )
                      )
                    )
                    (.node 2 4   -- 9
                      (.node 1 6   -- 5
                        (.node 1 3   -- 3
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 3), (1, 4), (1, 2)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (1, 4), (1, 3), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (1, 4), (1, 2)]))
                          )
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 2), (0, 1), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 1), (0, 5)]))
                        )
                      )
                      (.node 1 3   -- 4
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 2), (1, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 3), (1, 4)]))
                        )
                        (.node 1 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 3   -- 66
                (.node 1 2   -- 34
                  (.node 3 5   -- 17
                    (.node 5 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 3), (0, 2), (0, 1)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 1), (4, 6)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 3), (0, 2), (0, 1)]))
                        )
                      )
                      (.node 0 5   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 1), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 2), (0, 1)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 3), (0, 2), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 1), (4, 5)]))
                        )
                      )
                    )
                    (.node 0 4   -- 9
                      (.node 0 6   -- 6
                        (.node 1 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5)]))
                        )
                        (.node 1 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (4, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (4, 6)]))
                        )
                      )
                      (.node 1 5   -- 3
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 2), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 1)]))
                        )
                        (.leaf (swapProd [(0, 6), (0, 4), (0, 5)]))
                      )
                    )
                  )
                  (.node 3 5   -- 17
                    (.node 5 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 3), (0, 2)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (4, 6)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 3), (0, 2)]))
                        )
                      )
                      (.node 0 5   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 2)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 3), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (4, 5)]))
                        )
                      )
                    )
                    (.node 0 4   -- 9
                      (.node 0 6   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 2)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (1, 2)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (4, 6)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (4, 6)]))
                            (.leaf (swapProd [(0, 5), (1, 2), (4, 6)]))
                          )
                        )
                      )
                      (.node 1 5   -- 3
                        (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 2)]))
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (1, 2)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 6   -- 32
                  (.node 1 5   -- 17
                    (.node 5 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 3), (0, 1), (0, 2)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 2), (4, 6)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 3), (0, 1), (0, 2)]))
                        )
                      )
                      (.node 0 5   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 1), (0, 2)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 3), (0, 1), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 2), (4, 5)]))
                        )
                      )
                    )
                    (.node 0 4   -- 9
                      (.node 0 6   -- 6
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 1), (0, 3), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (1, 3), (1, 2)]))
                        )
                        (.node 2 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (1, 3), (4, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 2), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 2), (4, 6)]))
                        )
                      )
                      (.node 2 5   -- 3
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 1), (0, 3), (0, 2)]))
                        )
                        (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (1, 3), (1, 2)]))
                      )
                    )
                  )
                  (.node 0 4   -- 15
                    (.node 5 6   -- 6
                      (.node 2 5   -- 3
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (1, 4), (1, 6), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 6), (0, 3), (0, 2)]))
                        )
                        (.leaf (swapProd [(0, 5), (1, 4), (1, 6), (1, 3), (1, 2)]))
                      )
                      (.node 0 5   -- 3
                        (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (1, 3)]))
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 4), (0, 6), (0, 2)]))
                        )
                      )
                    )
                    (.node 1 4   -- 9
                      (.node 3 5   -- 5
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (1, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 4), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 4), (1, 5), (1, 3)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (1, 4), (1, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 1), (0, 4), (0, 5)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 5), (0, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (1, 5), (1, 3)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (1, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 1), (0, 5)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree742 : Tree 7 :=
            (.node 2 6   -- 168
              (.node 1 6   -- 84
                (.node 1 2   -- 42
                  (.node 2 5   -- 21
                    (.node 0 4   -- 10
                      (.node 3 5   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 1)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 2), (0, 1)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 6), (0, 2), (0, 1)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 5), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (3, 4), (3, 5)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 5), (0, 2), (0, 1)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 2), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (3, 5)]))
                          )
                        )
                      )
                    )
                    (.node 1 5   -- 11
                      (.node 3 4   -- 5
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 5), (0, 1)]))
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 3), (0, 5), (0, 1)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 1 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 3), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 2), (0, 3), (0, 5)]))
                        )
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 5), (3, 4), (3, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 21
                    (.node 0 4   -- 10
                      (.node 3 5   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 2)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 6), (0, 2)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (3, 4), (3, 5)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 5), (0, 2)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (3, 5)]))
                          )
                        )
                      )
                    )
                    (.node 2 5   -- 11
                      (.node 3 4   -- 5
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 5), (0, 1), (0, 2)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 5), (0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 1), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (1, 3), (1, 5)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 5), (1, 2)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 1), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 3), (0, 5)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 5), (1, 2), (3, 4), (3, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 5), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (1, 2)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 42
                  (.node 3 4   -- 21
                    (.node 0 4   -- 11
                      (.node 1 5   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 2)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 1), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 6), (0, 1), (0, 2)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 4), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (1, 3), (1, 4), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 4), (1, 6), (1, 2)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (4, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (3, 4), (3, 5)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 3), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 4), (0, 5), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 3), (0, 4), (0, 5)]))
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 5 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (1, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 3), (0, 5)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (3, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 5), (0, 2)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 1), (0, 4), (0, 2)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 4), (1, 3), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 3), (0, 5), (0, 2)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (1, 4), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 4), (0, 3), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (1, 4)]))
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 21
                    (.node 0 4   -- 11
                      (.node 3 5   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 3), (0, 2)]))
                          (.node 1 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 1), (0, 3), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (1, 4), (1, 6)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 6), (0, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (1, 4), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (1, 4), (1, 6), (1, 2)]))
                        )
                      )
                      (.node 3 5   -- 5
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 2), (4, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 5), (0, 3), (0, 2)]))
                        )
                        (.node 2 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 5), (0, 2)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 4), (0, 5)]))
                        )
                      )
                    )
                    (.node 2 5   -- 10
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 3), (0, 2)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 2)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 2), (1, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (1, 5), (3, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 2), (3, 4)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 2), (0, 1), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 1), (0, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 5), (3, 4)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 2   -- 84
                (.node 1 6   -- 42
                  (.node 3 4   -- 21
                    (.node 0 4   -- 11
                      (.node 2 5   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 6), (0, 1)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (2, 3), (2, 4), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 4), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 5), (2, 3), (2, 4), (2, 6)]))
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (4, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (3, 4), (3, 5)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 4), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (2, 3), (2, 4), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 4), (0, 5)]))
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 2 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 6), (0, 1), (3, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (2, 3), (2, 5)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (0, 1), (2, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 3), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (2, 4), (2, 3), (2, 5)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (2, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 5), (1, 2), (1, 4)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 3), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 21
                    (.node 0 4   -- 10
                      (.node 3 5   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 4), (0, 6)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 6), (3, 4), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (3, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (2, 3), (2, 4), (2, 5)]))
                            (.leaf (swapProd [(0, 6), (2, 3), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (2, 4), (2, 3), (2, 5)]))
                        )
                      )
                    )
                    (.node 2 4   -- 11
                      (.node 5 6   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 3), (1, 4), (1, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 3), (0, 5)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 3), (0, 4), (0, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (1, 2), (1, 3), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (1, 2), (1, 3), (1, 5)]))
                          )
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 4), (0, 3), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (1, 2), (1, 4), (1, 3), (1, 5)]))
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 1), (0, 3), (0, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 5), (2, 4)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 42
                  (.node 2 5   -- 21
                    (.node 0 4   -- 10
                      (.node 3 5   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (1, 2)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 6), (1, 2)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 3), (0, 4), (0, 6)]))
                        )
                      )
                      (.node 1 5   -- 6
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (1, 2), (4, 5)]))
                            (.leaf (swapProd [(0, 6), (1, 2), (3, 4), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (1, 2), (3, 5)]))
                        )
                        (.node 1 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 4), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 5), (1, 2)]))
                          )
                          (.leaf (swapProd [(0, 6), (1, 4), (1, 3), (1, 5), (1, 2)]))
                        )
                      )
                    )
                    (.node 1 4   -- 11
                      (.node 5 6   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 4), (1, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 5)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 4), (0, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 5)]))
                          )
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 3), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (1, 4), (1, 3), (1, 5)]))
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 5), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 2), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (1, 4), (1, 2), (1, 3), (1, 5)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 21
                    (.node 0 4   -- 11
                      (.node 3 5   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (1, 3), (1, 2)]))
                          (.node 1 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (1, 3), (1, 2)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 1), (0, 4), (0, 6)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 4), (0, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 4), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 6)]))
                          )
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 6), (1, 3), (1, 2), (4, 5)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (1, 4), (1, 5), (1, 3), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (1, 4), (1, 5), (1, 2)]))
                          )
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (1, 4), (1, 5)]))
                        )
                      )
                    )
                    (.node 3 4   -- 10
                      (.node 2 5   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 3), (1, 2)]))
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 2)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (1, 5)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 2), (3, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (3, 4)]))
                            (.leaf (swapProd [(0, 6), (1, 5), (3, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 4), (0, 1), (0, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (2, 3), (2, 4)]))
                            (.leaf (swapProd [(0, 6), (1, 5), (2, 3), (2, 4)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree743 : Tree 7 :=
          (.node 3 6   -- 315
            tree741
            tree742
          )

private def tree744 : Tree 7 :=
        (.node 4 5   -- 630
          tree740
          tree743
        )

private def tree745 : Tree 7 :=
      (.node 0 3   -- 1260
        tree737
        tree744
      )

private def tree746 : Tree 7 :=
            (.node 5 6   -- 147
              (.node 1 4   -- 81
                (.node 3 4   -- 44
                  (.node 0 4   -- 22
                    (.node 2 5   -- 12
                      (.node 2 4   -- 6
                        (.node 0 3   -- 3
                          (.leaf (swapProd [(0, 1), (2, 3)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 3)]))
                          )
                        )
                        (.node 0 3   -- 3
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 3)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 3)]))
                          )
                        )
                      )
                      (.node 2 6   -- 6
                        (.node 0 3   -- 3
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 4), (2, 3)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 3)]))
                          )
                        )
                        (.node 0 3   -- 3
                          (.leaf (swapProd [(0, 1), (2, 6), (2, 5), (2, 4), (2, 3)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 4), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 4), (0, 3)]))
                          )
                        )
                      )
                    )
                    (.node 1 3   -- 10
                      (.node 0 5   -- 5
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 1), (2, 4)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 6), (2, 5), (2, 4)]))
                          )
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 3), (0, 1)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 5), (0, 3), (0, 1)]))
                        )
                      )
                      (.node 0 5   -- 5
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 3), (2, 4)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (2, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 3), (2, 6), (2, 5), (2, 4)]))
                          )
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 5), (0, 3)]))
                        )
                      )
                    )
                  )
                  (.node 2 6   -- 22
                    (.node 0 3   -- 11
                      (.node 0 4   -- 7
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 1), (2, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 1), (2, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 1), (2, 5), (2, 3), (2, 4)]))
                          )
                        )
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
                    (.node 0 5   -- 11
                      (.node 0 4   -- 7
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 1), (2, 6), (2, 5), (2, 4)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 1), (2, 6), (2, 5), (2, 3), (2, 4)]))
                            (.leaf (swapProd [(0, 1), (2, 6), (2, 4), (3, 5)]))
                          )
                        )
                        (.node 3 5   -- 4
                          (.node 0 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 5), (0, 4), (0, 1)]))
                          )
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 3), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 1), (3, 5)]))
                          )
                        )
                      )
                      (.node 0 3   -- 4
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (2, 6), (2, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 6), (0, 4), (0, 1)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (2, 6), (2, 5), (2, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (2, 6), (2, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 2 6   -- 37
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
                  (.node 3 5   -- 18
                    (.node 0 5   -- 9
                      (.node 1 3   -- 4
                        (.node 0 3   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 5), (0, 4)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 3), (1, 2), (1, 6), (1, 5), (1, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 6), (0, 5), (0, 4)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 1 3   -- 3
                          (.leaf (swapProd [(0, 4), (2, 6), (2, 5), (2, 3)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 6), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 4), (1, 2), (1, 6), (1, 5), (1, 3)]))
                          )
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (2, 6), (2, 5)]))
                          (.leaf (swapProd [(0, 4), (1, 3), (2, 6), (2, 5)]))
                        )
                      )
                    )
                    (.node 1 5   -- 9
                      (.node 0 5   -- 5
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 3), (0, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (3, 5)]))
                        )
                        (.node 0 3   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (2, 6), (2, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 6), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 4), (2, 6), (2, 5)]))
                        )
                      )
                      (.node 0 3   -- 4
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (1, 2), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 2), (0, 6), (0, 4)]))
                        )
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(0, 4), (1, 2), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(0, 4), (1, 3), (1, 2), (1, 6), (1, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 0 3   -- 66
                (.node 3 6   -- 32
                  (.node 3 4   -- 17
                    (.node 4 6   -- 8
                      (.node 2 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 1), (2, 3), (5, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 3), (5, 6)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 6), (2, 4), (2, 3)]))
                          (.leaf (swapProd [(0, 1), (2, 6), (2, 4), (2, 3)]))
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 3), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 5), (2, 6), (2, 3)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 1), (2, 6), (2, 3)]))
                        )
                      )
                    )
                    (.node 0 4   -- 9
                      (.node 2 5   -- 3
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 4), (5, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 6), (2, 4)]))
                        )
                        (.leaf (swapProd [(0, 1), (2, 6), (2, 4)]))
                      )
                      (.node 1 4   -- 6
                        (.node 2 5   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 1), (5, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 4), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 1)]))
                        )
                        (.node 2 5   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (5, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 15
                    (.node 2 5   -- 9
                      (.node 3 4   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 5), (2, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 6)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 6), (2, 3), (2, 4)]))
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 6), (3, 4)]))
                        )
                      )
                      (.node 3 5   -- 5
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 1), (2, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 1), (2, 6), (2, 3), (2, 4)]))
                            (.leaf (swapProd [(0, 1), (2, 6), (3, 4)]))
                          )
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 6), (2, 3), (2, 5), (2, 4)]))
                          (.leaf (swapProd [(0, 1), (2, 6), (3, 5), (3, 4)]))
                        )
                      )
                    )
                    (.node 1 4   -- 6
                      (.node 2 5   -- 3
                        (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 3), (0, 4), (0, 1)]))
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 4), (0, 1)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 5), (0, 4), (0, 1)]))
                        )
                      )
                      (.node 2 5   -- 3
                        (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 3), (0, 4)]))
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 5), (0, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 34
                  (.node 0 4   -- 17
                    (.node 4 6   -- 8
                      (.node 2 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (5, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (0, 1), (5, 6)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 4), (0, 3), (0, 1)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 3), (0, 1)]))
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 6), (0, 3), (0, 1)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 3), (0, 1)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 1)]))
                        )
                      )
                    )
                    (.node 1 4   -- 9
                      (.node 3 4   -- 6
                        (.node 2 5   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 4), (5, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 5), (2, 6), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 1), (2, 6), (2, 4)]))
                        )
                        (.node 2 5   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 1), (5, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 6), (0, 4), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 4), (0, 1)]))
                        )
                      )
                      (.node 2 5   -- 3
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (5, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 6), (0, 4)]))
                        )
                        (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 4)]))
                      )
                    )
                  )
                  (.node 0 4   -- 17
                    (.node 4 6   -- 8
                      (.node 2 6   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (5, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 3), (5, 6)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 3)]))
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 6), (0, 3)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3)]))
                        )
                      )
                    )
                    (.node 1 4   -- 9
                      (.node 2 5   -- 3
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (2, 4), (5, 6)]))
                          (.leaf (swapProd [(0, 3), (2, 5), (2, 6), (2, 4)]))
                        )
                        (.leaf (swapProd [(0, 3), (2, 6), (2, 4)]))
                      )
                      (.node 3 4   -- 6
                        (.node 2 5   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 2), (1, 4), (5, 6)]))
                            (.leaf (swapProd [(0, 3), (1, 2), (1, 5), (1, 6), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (1, 2), (1, 6), (1, 4)]))
                        )
                        (.node 2 5   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 4), (5, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 5), (0, 6), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 6), (0, 4)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree747 : Tree 7 :=
            (.node 1 6   -- 168
              (.node 3 6   -- 84
                (.node 1 3   -- 42
                  (.node 0 5   -- 21
                    (.node 2 5   -- 11
                      (.node 4 6   -- 6
                        (.node 1 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 6), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (2, 5), (2, 6), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 4), (2, 5), (2, 6), (2, 3)]))
                        )
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 4), (2, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 5), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (2, 5), (2, 6)]))
                        )
                      )
                      (.node 3 4   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 1), (2, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (2, 6)]))
                          )
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (2, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 4), (2, 6), (2, 3)]))
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (2, 6), (2, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 6), (0, 3), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 1), (2, 6)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 6), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (2, 6), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 4), (0, 1)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (2, 6), (2, 3)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 6), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 2 5   -- 11
                      (.node 4 6   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 6), (0, 3)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 5), (0, 6), (0, 3)]))
                            (.leaf (swapProd [(0, 4), (1, 2), (1, 5), (1, 6), (1, 3)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 3), (2, 4), (2, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 3), (2, 5), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 3), (2, 5), (2, 6)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 3), (2, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (2, 6)]))
                          )
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (1, 2), (1, 6), (1, 3)]))
                        )
                      )
                    )
                    (.node 3 4   -- 10
                      (.node 1 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (2, 6), (2, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 6), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (2, 6)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (1, 2), (1, 6), (1, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 2), (0, 6), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 4), (0, 1), (0, 3)]))
                        )
                      )
                      (.node 1 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 2), (0, 6), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 2), (1, 6), (1, 3)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 4), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 2), (0, 6), (0, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 0 3   -- 42
                  (.node 3 5   -- 21
                    (.node 0 4   -- 11
                      (.node 2 5   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 6), (0, 1)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (0, 1), (3, 4)]))
                          )
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (3, 4)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (2, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 5), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 4), (2, 5), (2, 6)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (2, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 4), (2, 6)]))
                        )
                      )
                    )
                    (.node 0 5   -- 10
                      (.node 4 6   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 1), (2, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (2, 6)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (3, 5), (3, 4)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 2), (0, 6), (0, 1)]))
                        )
                      )
                      (.node 1 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (2, 6), (2, 3), (2, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (2, 6), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 1), (3, 5)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (2, 6), (2, 3), (2, 5)]))
                            (.leaf (swapProd [(0, 4), (2, 6), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 4), (1, 2), (1, 6), (1, 3), (1, 5)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 2 5   -- 11
                      (.node 3 4   -- 6
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 5), (0, 6), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 5), (0, 6), (0, 1)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (2, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (2, 5), (2, 6)]))
                        )
                      )
                      (.node 3 4   -- 5
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 1)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 6), (0, 1)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (2, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (2, 6)]))
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 2), (0, 6), (0, 1)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 6), (0, 1)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 3), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 1), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 2), (0, 6), (0, 1)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 3), (0, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 6), (0, 3), (0, 4)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (2, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (2, 6)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 3   -- 84
                (.node 0 3   -- 42
                  (.node 1 4   -- 21
                    (.node 0 4   -- 10
                      (.node 2 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 6), (3, 4)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 2), (0, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (3, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (3, 5), (3, 4)]))
                          )
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 2), (0, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (3, 5)]))
                        )
                      )
                    )
                    (.node 0 5   -- 11
                      (.node 4 6   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (1, 2), (1, 5), (1, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (1, 2), (1, 6)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 2), (0, 5), (0, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 4), (0, 1), (0, 2), (0, 6)]))
                          )
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 4), (1, 2), (1, 6), (3, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 6), (3, 5)]))
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 3), (1, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 4), (1, 3), (1, 5), (1, 2), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 5), (0, 2), (0, 6)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 2 5   -- 11
                      (.node 3 4   -- 6
                        (.node 0 4   -- 3
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 5), (0, 6)]))
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 2), (1, 5), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 5), (0, 6)]))
                          )
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 6)]))
                          )
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 4), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 6)]))
                        )
                      )
                    )
                    (.node 3 5   -- 10
                      (.node 1 4   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 2), (0, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 6)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 2), (0, 6)]))
                        )
                      )
                      (.node 1 5   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 2), (0, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 4), (0, 1), (0, 2), (0, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 4), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 1), (0, 3), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (1, 3), (1, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 3 6   -- 42
                  (.node 0 5   -- 21
                    (.node 1 4   -- 11
                      (.node 0 4   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (1, 2), (1, 4), (1, 5), (1, 6)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (1, 2), (1, 5), (1, 6)]))
                            (.leaf (swapProd [(0, 3), (1, 2), (1, 6)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (1, 2), (1, 5), (1, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (1, 2), (1, 6)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (2, 5), (2, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 6), (0, 1), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 4), (1, 3), (2, 5), (2, 6)]))
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (2, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 1), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 4), (1, 3), (2, 6)]))
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 4 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 3), (2, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 3), (2, 6)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 6), (0, 1), (0, 3)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (1, 4), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 3), (1, 4), (1, 2), (1, 6)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 3), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 4), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (2, 6), (2, 3)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 21
                    (.node 1 4   -- 11
                      (.node 0 4   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 5), (0, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 6)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 2), (0, 5), (0, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 2), (0, 6)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 5), (0, 6), (1, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 3), (1, 2), (1, 5), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 2), (0, 5), (0, 6)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (1, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (1, 3), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 2), (0, 6)]))
                          )
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 3 4   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 1), (0, 2), (0, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 6), (1, 3)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 3), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 3), (0, 2), (0, 6)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 4), (0, 2), (0, 6)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 6), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 6), (1, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 1), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (1, 4)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree748 : Tree 7 :=
          (.node 0 6   -- 315
            tree746
            tree747
          )

private def tree749 : Tree 7 :=
            (.node 4 6   -- 147
              (.node 1 5   -- 81
                (.node 3 5   -- 44
                  (.node 0 5   -- 22
                    (.node 2 4   -- 12
                      (.node 2 5   -- 6
                        (.node 0 3   -- 3
                          (.leaf (swapProd [(0, 1), (2, 3), (4, 5)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (4, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 3), (4, 5)]))
                          )
                        )
                        (.node 0 3   -- 3
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 5), (2, 3)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 5), (0, 3)]))
                          )
                        )
                      )
                      (.node 2 6   -- 6
                        (.node 0 3   -- 3
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 3)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 3)]))
                          )
                        )
                        (.node 0 3   -- 3
                          (.leaf (swapProd [(0, 1), (2, 6), (2, 5), (2, 3)]))
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 3)]))
                          )
                        )
                      )
                    )
                    (.node 1 3   -- 10
                      (.node 0 4   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 1), (2, 4), (2, 5)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 6), (2, 5)]))
                          )
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (2, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (2, 6), (2, 5)]))
                        )
                      )
                      (.node 0 4   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (2, 4), (2, 5)]))
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (2, 5)]))
                            (.leaf (swapProd [(0, 3), (2, 6), (2, 5)]))
                          )
                        )
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (2, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (2, 6), (2, 5)]))
                        )
                      )
                    )
                  )
                  (.node 2 6   -- 22
                    (.node 0 3   -- 11
                      (.node 0 5   -- 7
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 5)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 1), (2, 5)]))
                            (.leaf (swapProd [(0, 1), (2, 5), (3, 4)]))
                          )
                        )
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
                    (.node 0 4   -- 11
                      (.node 0 5   -- 7
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 1), (2, 6), (2, 5)]))
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 1), (2, 6), (2, 5), (3, 4)]))
                            (.leaf (swapProd [(0, 1), (2, 6), (2, 4), (2, 3), (2, 5)]))
                          )
                        )
                        (.node 3 4   -- 4
                          (.node 0 3   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 5), (0, 1)]))
                          )
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (0, 1), (3, 4)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 3), (0, 5), (0, 1)]))
                          )
                        )
                      )
                      (.node 0 3   -- 4
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 6), (0, 5), (0, 1)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (2, 6), (2, 4)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 6), (0, 5), (0, 1)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 5), (0, 1)]))
                        )
                      )
                    )
                  )
                )
                (.node 2 6   -- 37
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
                  (.node 3 4   -- 18
                    (.node 0 4   -- 9
                      (.node 1 3   -- 4
                        (.node 0 3   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 5)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 3), (1, 2), (1, 6), (1, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 6), (0, 5)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 1 3   -- 3
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 2), (0, 6), (0, 5)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (1, 2), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (0, 2), (0, 6), (0, 5)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 5), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 5), (1, 3)]))
                        )
                      )
                    )
                    (.node 1 4   -- 9
                      (.node 0 4   -- 5
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 5), (3, 4)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 3), (0, 5)]))
                        )
                        (.node 0 3   -- 3
                          (.node 3 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 2), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (2, 6), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 5)]))
                        )
                      )
                      (.node 0 3   -- 4
                        (.node 3 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 1), (0, 2), (0, 6), (0, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (1, 2), (1, 6), (1, 4)]))
                        )
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 6), (0, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 2), (0, 6), (0, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 0 3   -- 66
                (.node 3 6   -- 32
                  (.node 3 5   -- 17
                    (.node 5 6   -- 8
                      (.node 2 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 1), (2, 3), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 6), (2, 5), (2, 3)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 3), (4, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 6), (2, 4), (2, 5), (2, 3)]))
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 3), (4, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 6), (2, 3)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 4), (2, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 1), (2, 6), (2, 3), (4, 5)]))
                        )
                      )
                    )
                    (.node 0 5   -- 9
                      (.node 2 4   -- 3
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 6), (2, 5)]))
                          (.leaf (swapProd [(0, 1), (2, 5), (4, 6)]))
                        )
                        (.leaf (swapProd [(0, 1), (2, 6), (2, 4), (2, 5)]))
                      )
                      (.node 1 5   -- 6
                        (.node 2 4   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 5), (0, 1)]))
                        )
                        (.node 2 4   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 15
                    (.node 2 4   -- 9
                      (.node 3 5   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 1), (2, 4), (2, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 4), (2, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 5), (3, 4), (3, 6)]))
                          (.leaf (swapProd [(0, 1), (2, 5), (2, 3), (2, 4), (2, 6)]))
                        )
                      )
                      (.node 3 4   -- 5
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 1), (2, 6), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 1), (2, 6), (2, 3), (2, 4), (2, 5)]))
                            (.leaf (swapProd [(0, 1), (2, 6), (3, 4), (3, 5)]))
                          )
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 1), (2, 6), (2, 3), (2, 5)]))
                          (.leaf (swapProd [(0, 1), (2, 6), (3, 5)]))
                        )
                      )
                    )
                    (.node 1 5   -- 6
                      (.node 2 4   -- 3
                        (.leaf (swapProd [(0, 2), (0, 5), (0, 1), (3, 4), (3, 6)]))
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 4), (0, 5), (0, 1)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 5), (0, 1)]))
                        )
                      )
                      (.node 2 4   -- 3
                        (.leaf (swapProd [(0, 2), (0, 5), (3, 4), (3, 6)]))
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 4), (0, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 3   -- 34
                  (.node 0 5   -- 17
                    (.node 5 6   -- 8
                      (.node 2 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 5), (0, 3), (0, 1)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 1), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 5), (0, 3), (0, 1)]))
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (0, 1), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 3), (0, 1)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 6), (0, 3), (0, 1)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (0, 1), (4, 5)]))
                        )
                      )
                    )
                    (.node 1 5   -- 9
                      (.node 3 5   -- 6
                        (.node 2 4   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 4), (2, 6), (2, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 5), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 1), (2, 6), (2, 4), (2, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 6), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 1), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 4), (0, 5), (0, 1)]))
                        )
                      )
                      (.node 2 4   -- 3
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 6), (0, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (4, 6)]))
                        )
                        (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 4), (0, 5)]))
                      )
                    )
                  )
                  (.node 0 5   -- 17
                    (.node 5 6   -- 8
                      (.node 2 6   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 5), (0, 3)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 4), (0, 5), (0, 3)]))
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 2), (0, 3), (4, 6)]))
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 3)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 3), (4, 5)]))
                        )
                      )
                    )
                    (.node 1 5   -- 9
                      (.node 2 4   -- 3
                        (.node 2 6   -- 2
                          (.leaf (swapProd [(0, 3), (2, 4), (2, 6), (2, 5)]))
                          (.leaf (swapProd [(0, 3), (2, 5), (4, 6)]))
                        )
                        (.leaf (swapProd [(0, 3), (2, 6), (2, 4), (2, 5)]))
                      )
                      (.node 3 5   -- 6
                        (.node 2 4   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (1, 2), (1, 4), (1, 6), (1, 5)]))
                            (.leaf (swapProd [(0, 3), (1, 2), (1, 5), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (1, 2), (1, 6), (1, 4), (1, 5)]))
                        )
                        (.node 2 4   -- 3
                          (.node 2 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 4), (0, 6), (0, 5)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 5), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 6), (0, 4), (0, 5)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree750 : Tree 7 :=
            (.node 1 6   -- 168
              (.node 3 6   -- 84
                (.node 1 3   -- 42
                  (.node 0 4   -- 21
                    (.node 2 4   -- 11
                      (.node 5 6   -- 6
                        (.node 1 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 1), (2, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 2), (0, 5), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 2), (0, 5)]))
                        )
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 4), (2, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (2, 5), (2, 4), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 5), (0, 3), (0, 1)]))
                        )
                      )
                      (.node 3 5   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 1), (2, 6), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 6), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 1), (2, 6)]))
                          )
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (2, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (2, 6), (2, 3)]))
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 4), (0, 3), (0, 1)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (2, 6)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (2, 6), (2, 4), (2, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (2, 6), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (2, 6), (2, 4)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (2, 6), (2, 4), (2, 3)]))
                          (.leaf (swapProd [(0, 5), (2, 6), (2, 3)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (2, 6), (2, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 6), (1, 4)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 2 4   -- 11
                      (.node 5 6   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (2, 5)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (1, 2), (1, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 1), (0, 2), (0, 5)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (2, 4), (2, 6)]))
                            (.leaf (swapProd [(0, 3), (2, 5), (2, 4), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 5), (0, 3)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 3), (2, 6), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 6), (0, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (2, 6)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 2), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (1, 2), (1, 6), (1, 3)]))
                        )
                      )
                    )
                    (.node 3 5   -- 10
                      (.node 1 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 4), (0, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (2, 6)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 6), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 6), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (2, 6), (2, 4)]))
                        )
                      )
                      (.node 1 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 6), (1, 4), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 6), (1, 3)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (1, 3), (2, 6), (2, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 2), (1, 6), (1, 4)]))
                        )
                      )
                    )
                  )
                )
                (.node 0 3   -- 42
                  (.node 3 4   -- 21
                    (.node 0 5   -- 11
                      (.node 2 4   -- 5
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6), (0, 1)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 6), (0, 1)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 4), (0, 6), (0, 1)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (4, 5)]))
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (3, 4), (3, 5)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 2), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 1), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 2), (0, 5)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 1), (2, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 2), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (2, 6)]))
                        )
                      )
                    )
                    (.node 0 4   -- 10
                      (.node 5 6   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (2, 6)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (2, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 2), (0, 6), (0, 1), (3, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 6), (0, 1)]))
                        )
                      )
                      (.node 1 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 3), (0, 5), (0, 1)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 1), (2, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 2), (0, 6), (0, 1)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 6), (0, 3), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 2 4   -- 11
                      (.node 3 5   -- 6
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 6), (0, 1)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 4), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (2, 5), (2, 3)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 5)]))
                        )
                      )
                      (.node 3 5   -- 5
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (0, 1), (4, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 2), (0, 6), (0, 1)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (2, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 5), (2, 6)]))
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 6), (0, 1)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 1)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (0, 1), (2, 6), (2, 3), (2, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (2, 6), (3, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 1), (3, 4)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (2, 6), (2, 3), (2, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 6), (1, 3), (1, 4)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (2, 6)]))
                          (.leaf (swapProd [(0, 5), (2, 6), (3, 4)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 3   -- 84
                (.node 0 3   -- 42
                  (.node 1 5   -- 21
                    (.node 0 5   -- 10
                      (.node 2 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 2), (0, 4), (0, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 2), (0, 5), (0, 3), (0, 4), (0, 6)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 2), (0, 6), (4, 5)]))
                            (.leaf (swapProd [(0, 2), (0, 6), (3, 4), (3, 5)]))
                          )
                          (.leaf (swapProd [(0, 2), (0, 6), (3, 5)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (2, 5)]))
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 2), (0, 6)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 5), (0, 2), (0, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 2), (0, 6)]))
                        )
                      )
                    )
                    (.node 0 4   -- 11
                      (.node 5 6   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (0, 1), (0, 2), (0, 5)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (1, 2), (1, 6)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 3), (0, 4), (0, 6), (1, 2), (1, 5)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 3), (0, 4), (0, 5), (0, 1), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 5), (0, 1), (0, 2), (0, 6)]))
                          )
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 5), (0, 1), (0, 2), (0, 6)]))
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (0, 5), (2, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (0, 1), (0, 3), (0, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 6), (1, 3), (1, 5)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 2 4   -- 11
                      (.node 3 5   -- 6
                        (.node 0 5   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 2), (0, 5), (0, 4), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (2, 5), (2, 3)]))
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (2, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 2), (0, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (1, 2), (1, 5)]))
                          )
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 3), (0, 2), (0, 6), (4, 5)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 2), (0, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 6)]))
                          )
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 2), (0, 6)]))
                        )
                      )
                    )
                    (.node 3 4   -- 10
                      (.node 1 5   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 6)]))
                        )
                      )
                      (.node 1 4   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (3, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 2), (1, 6), (3, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 6), (3, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 4), (2, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 3), (1, 4), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 4), (0, 2), (0, 6)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 3 6   -- 42
                  (.node 0 4   -- 21
                    (.node 1 5   -- 11
                      (.node 0 5   -- 5
                        (.node 2 4   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (1, 2), (1, 4), (1, 6)]))
                            (.leaf (swapProd [(0, 3), (1, 2), (1, 5), (1, 4), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (1, 2), (1, 6), (4, 5)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 2), (0, 5), (0, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (1, 2), (1, 6)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 5), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 3), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 5), (1, 3)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 3), (2, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 6), (0, 1), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 5), (1, 3), (2, 6)]))
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 5 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (2, 6)]))
                          (.leaf (swapProd [(0, 5), (1, 3), (2, 6)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 1), (0, 3)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 2), (0, 6), (0, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 3), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (0, 1), (0, 4), (0, 3)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 4), (1, 2), (1, 6), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (1, 4), (1, 3), (2, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (1, 4), (2, 6), (2, 3)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 21
                    (.node 1 5   -- 11
                      (.node 0 5   -- 5
                        (.node 2 4   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 4), (0, 6)]))
                            (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 5), (0, 4), (0, 6)]))
                          )
                          (.leaf (swapProd [(0, 3), (0, 1), (0, 2), (0, 6), (4, 5)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (1, 2), (1, 5), (1, 3)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 1), (0, 2), (0, 6)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (1, 3), (2, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 3), (0, 2), (0, 5)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (1, 3), (1, 2), (1, 5)]))
                          )
                        )
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 6), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (1, 3), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 3), (0, 2), (0, 6)]))
                          )
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 3 5   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 2), (0, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (1, 3)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 2), (1, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 2), (0, 6)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 6), (1, 4), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 4), (1, 3), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 3), (0, 2), (0, 6)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 5), (1, 4), (2, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 4), (1, 2), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 2), (0, 6)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree751 : Tree 7 :=
          (.node 0 6   -- 315
            tree749
            tree750
          )

private def tree752 : Tree 7 :=
        (.node 4 5   -- 630
          tree748
          tree751
        )

private def tree753 : Tree 7 :=
            (.node 5 6   -- 147
              (.node 3 4   -- 81
                (.node 1 4   -- 44
                  (.node 2 4   -- 22
                    (.node 0 5   -- 12
                      (.node 0 4   -- 6
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 3)]))
                          )
                          (.leaf (swapProd [(0, 3), (1, 2)]))
                        )
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 4), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 3), (1, 2)]))
                        )
                      )
                      (.node 0 6   -- 6
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 3), (1, 2)]))
                        )
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 3), (1, 2)]))
                        )
                      )
                    )
                    (.node 1 3   -- 10
                      (.node 0 6   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 1)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (2, 4)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 2), (0, 3), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 1), (2, 4)]))
                        )
                      )
                      (.node 0 6   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 3)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (2, 4)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (2, 4)]))
                        )
                      )
                    )
                  )
                  (.node 0 6   -- 22
                    (.node 1 2   -- 11
                      (.node 2 5   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 2), (0, 3)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 1), (0, 3)]))
                        )
                      )
                      (.node 1 5   -- 7
                        (.node 0 5   -- 4
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3)]))
                          )
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 2), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (0, 3)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 3), (1, 4), (1, 2)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (1, 4)]))
                          )
                        )
                      )
                    )
                    (.node 1 5   -- 11
                      (.node 1 2   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 1), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (1, 2), (1, 4)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 2), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 1), (0, 3)]))
                        )
                      )
                      (.node 1 6   -- 7
                        (.node 2 5   -- 4
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (1, 4), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (1, 4)]))
                          )
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 4), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 3), (1, 4)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 1), (0, 5), (0, 3)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 5), (0, 2), (0, 3)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 0 6   -- 37
                  (.node 1 3   -- 19
                    (.node 1 4   -- 9
                      (.node 2 5   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 1), (2, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 1), (2, 3)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 4), (0, 1)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 1)]))
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (2, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (2, 3)]))
                        )
                        (.node 1 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 4)]))
                        )
                      )
                    )
                    (.node 1 2   -- 10
                      (.node 1 5   -- 5
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (1, 2), (1, 3)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 2), (0, 4)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 2), (0, 4)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (1, 3)]))
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 4)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (2, 3)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 18
                    (.node 2 5   -- 9
                      (.node 1 3   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (0, 1), (2, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (2, 3)]))
                        )
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (1, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 4), (1, 3)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 2), (0, 4), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 4), (0, 1)]))
                        )
                        (.node 1 3   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 1), (0, 2), (0, 4)]))
                        )
                      )
                    )
                    (.node 3 5   -- 9
                      (.node 1 6   -- 5
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 4), (1, 3)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 3), (0, 1), (0, 4)]))
                          )
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 5), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 5), (1, 2), (1, 3)]))
                        )
                      )
                      (.node 1 2   -- 4
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 2), (0, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 3), (0, 2), (0, 4)]))
                        )
                        (.node 1 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 4), (2, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 5), (2, 3)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 2   -- 66
                (.node 1 3   -- 34
                  (.node 2 4   -- 17
                    (.node 4 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (5, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (0, 1), (5, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 3), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 1)]))
                        )
                      )
                      (.node 0 4   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 3), (0, 1)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 1)]))
                        )
                      )
                    )
                    (.node 0 5   -- 9
                      (.node 0 6   -- 6
                        (.node 1 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (0, 1), (5, 6)]))
                            (.leaf (swapProd [(0, 4), (0, 1), (2, 3), (5, 6)]))
                          )
                          (.leaf (swapProd [(0, 4), (2, 3), (5, 6)]))
                        )
                        (.node 1 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 2), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 1), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (2, 3)]))
                        )
                      )
                      (.node 1 4   -- 3
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 3), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (2, 3)]))
                        )
                        (.leaf (swapProd [(0, 6), (0, 4), (2, 3)]))
                      )
                    )
                  )
                  (.node 2 4   -- 17
                    (.node 4 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 3), (5, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (5, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3)]))
                        )
                      )
                      (.node 0 4   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 3)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 3)]))
                        )
                      )
                    )
                    (.node 0 5   -- 9
                      (.node 0 6   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 3), (5, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 2), (0, 3), (5, 6)]))
                            (.leaf (swapProd [(0, 4), (1, 2), (1, 3), (5, 6)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 2), (0, 3)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 1), (0, 2), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (1, 2), (1, 3)]))
                          )
                        )
                      )
                      (.node 1 4   -- 3
                        (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 3)]))
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 2), (1, 3)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 6   -- 32
                  (.node 1 4   -- 17
                    (.node 4 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 3), (1, 2), (5, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 3), (1, 2), (5, 6)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 3), (1, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (1, 2)]))
                        )
                      )
                      (.node 0 4   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (1, 2), (4, 5), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 3), (1, 2)]))
                        )
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (1, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 2)]))
                        )
                      )
                    )
                    (.node 0 5   -- 9
                      (.node 0 6   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 2), (0, 1), (0, 3), (5, 6)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 4), (0, 1), (0, 3), (5, 6)]))
                            (.leaf (swapProd [(0, 4), (1, 3), (5, 6)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 2), (0, 1), (0, 3)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 4), (1, 3)]))
                          )
                        )
                      )
                      (.node 2 4   -- 3
                        (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 1), (0, 3)]))
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 3)]))
                        )
                      )
                    )
                  )
                  (.node 0 5   -- 15
                    (.node 4 6   -- 6
                      (.node 2 4   -- 3
                        (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (1, 4), (1, 2)]))
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 1), (0, 4)]))
                        )
                      )
                      (.node 0 4   -- 3
                        (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 2), (0, 1), (0, 3)]))
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 1), (0, 4), (0, 3)]))
                        )
                      )
                    )
                    (.node 1 5   -- 9
                      (.node 2 4   -- 5
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (1, 4), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 4), (0, 3)]))
                          )
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 4)]))
                        )
                      )
                      (.node 2 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 5), (1, 4), (1, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 5), (0, 4), (0, 3)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 5), (1, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 5), (0, 4)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree754 : Tree 7 :=
            (.node 3 6   -- 168
              (.node 1 6   -- 84
                (.node 1 3   -- 42
                  (.node 2 5   -- 21
                    (.node 0 5   -- 11
                      (.node 4 6   -- 6
                        (.node 1 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 1), (2, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 2), (0, 4), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 2), (0, 4)]))
                        )
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 2), (0, 3), (0, 1)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 4), (0, 3), (0, 1)]))
                          )
                        )
                      )
                      (.node 3 4   -- 5
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 1)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (2, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 3), (0, 1)]))
                          )
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 4), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 4)]))
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 5), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (2, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 4), (0, 3), (0, 1)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (2, 5), (2, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 5), (0, 4), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (2, 5)]))
                        )
                      )
                      (.node 3 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (2, 5), (2, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 5), (0, 4)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (2, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 2), (1, 5)]))
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 21
                    (.node 0 5   -- 10
                      (.node 2 4   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 3)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (2, 4)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 4), (0, 3)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (2, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (2, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 4), (0, 3)]))
                        )
                      )
                    )
                    (.node 3 4   -- 11
                      (.node 2 5   -- 5
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 2), (1, 4)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 2), (0, 5), (0, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (1, 2), (1, 5), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 3), (2, 5)]))
                        )
                      )
                      (.node 5 6   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 6), (0, 4), (1, 2), (1, 5), (1, 3)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (1, 3), (2, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 4), (1, 3), (1, 2), (1, 5)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 3), (0, 1), (0, 2), (0, 4)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 2), (0, 5), (0, 4)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 1 2   -- 42
                  (.node 2 5   -- 21
                    (.node 0 5   -- 11
                      (.node 1 4   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 1), (0, 2), (0, 3)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 2), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 2), (0, 4), (0, 3)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 4), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 3), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 4), (1, 3)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 4), (0, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (1, 3)]))
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 4 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 4), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 4), (1, 3)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 5), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (2, 5), (2, 4)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (1, 4), (2, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 3), (1, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 2), (0, 5), (0, 3)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 4), (2, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 3), (0, 1), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 5), (0, 1), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 21
                    (.node 0 5   -- 11
                      (.node 2 4   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 1), (0, 3)]))
                          (.node 1 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 4), (0, 3)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 4), (0, 2), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 3), (0, 1), (0, 4)]))
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (1, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 2), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 1), (0, 4)]))
                        )
                      )
                    )
                    (.node 2 5   -- 10
                      (.node 4 6   -- 4
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (1, 5), (1, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 1), (0, 5), (0, 4)]))
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 4), (0, 2), (0, 3)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (1, 5), (1, 2), (1, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 1), (0, 5), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 3), (2, 4)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 5), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (1, 5), (1, 3)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 4), (1, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 3   -- 84
                (.node 1 6   -- 42
                  (.node 2 5   -- 21
                    (.node 0 5   -- 11
                      (.node 3 4   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (0, 1), (2, 3)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (2, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (2, 4), (2, 3)]))
                          )
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 2), (0, 4)]))
                        )
                      )
                      (.node 3 4   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (2, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (2, 4), (2, 3)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 4)]))
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 1), (2, 5), (2, 4), (2, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 4), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (2, 5), (2, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 1), (2, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 3), (0, 4), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 1), (2, 5), (2, 3), (2, 4)]))
                        )
                      )
                      (.node 5 6   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (2, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (1, 2), (1, 5)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 3), (0, 4)]))
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 21
                    (.node 0 5   -- 10
                      (.node 2 4   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (2, 3)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 6), (2, 4), (2, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 6), (2, 4)]))
                        )
                      )
                      (.node 2 5   -- 6
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 6), (2, 3)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (2, 4), (2, 3)]))
                            (.leaf (swapProd [(0, 6), (2, 4)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6), (2, 5), (2, 4), (2, 3)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (2, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 6), (2, 5), (2, 3), (2, 4)]))
                          )
                        )
                      )
                    )
                    (.node 3 5   -- 11
                      (.node 4 6   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 2), (0, 4)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 5), (0, 4)]))
                          )
                        )
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (1, 2), (1, 4)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 6), (1, 2), (1, 4)]))
                            (.leaf (swapProd [(0, 6), (1, 2), (1, 5), (1, 4)]))
                          )
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 5), (0, 3), (0, 4)]))
                          (.leaf (swapProd [(0, 6), (1, 2), (1, 5), (1, 3), (1, 4)]))
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 1), (0, 3), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 4), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (1, 3), (1, 4), (2, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 2   -- 42
                  (.node 2 5   -- 21
                    (.node 0 5   -- 11
                      (.node 1 4   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (1, 2), (1, 3)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (1, 2), (1, 4), (1, 3)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (1, 3), (2, 4)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 3), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (1, 3), (1, 2), (1, 4)]))
                          )
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (1, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (1, 2), (1, 4), (1, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6), (1, 3), (2, 4)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 2), (1, 4)]))
                          )
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 3 4   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (1, 2), (1, 5), (1, 4), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (1, 3), (2, 5), (2, 4)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 2), (0, 5), (0, 4)]))
                          (.leaf (swapProd [(0, 6), (1, 3), (1, 2), (1, 5), (1, 4)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6), (1, 4), (1, 2), (1, 5), (1, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (2, 5), (2, 3)]))
                            (.leaf (swapProd [(0, 6), (1, 4), (2, 5), (2, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 1), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (1, 4), (2, 5)]))
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 21
                    (.node 0 5   -- 11
                      (.node 2 4   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 6), (1, 3)]))
                          (.node 1 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (1, 4), (1, 3)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 6), (1, 4), (1, 2), (1, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 6), (0, 1), (0, 4), (2, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 6), (1, 4), (2, 3)]))
                          )
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (1, 4), (1, 3)]))
                        )
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6), (1, 4), (1, 2), (1, 3)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (2, 3)]))
                            (.leaf (swapProd [(0, 6), (1, 4), (2, 3)]))
                          )
                        )
                      )
                    )
                    (.node 2 5   -- 10
                      (.node 3 4   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 4), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 4), (1, 2), (1, 3)]))
                        )
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 4), (2, 3)]))
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 4), (2, 3)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 3 4   -- 3
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 3), (2, 4)]))
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 3), (0, 2), (0, 4)]))
                            (.leaf (swapProd [(0, 6), (1, 5), (1, 3), (1, 2), (1, 4)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 2), (0, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 2), (1, 4)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree755 : Tree 7 :=
          (.node 2 6   -- 315
            tree753
            tree754
          )

private def tree756 : Tree 7 :=
            (.node 4 6   -- 147
              (.node 3 5   -- 81
                (.node 1 5   -- 44
                  (.node 2 5   -- 22
                    (.node 0 4   -- 12
                      (.node 0 5   -- 6
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 3), (0, 1), (4, 5)]))
                            (.leaf (swapProd [(0, 3), (4, 5)]))
                          )
                          (.leaf (swapProd [(0, 3), (1, 2), (4, 5)]))
                        )
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 3), (1, 2)]))
                        )
                      )
                      (.node 0 6   -- 6
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 3), (1, 2)]))
                        )
                        (.node 1 2   -- 3
                          (.node 1 3   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 3), (1, 2)]))
                        )
                      )
                    )
                    (.node 1 3   -- 10
                      (.node 0 6   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 3), (0, 1)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 3), (0, 1)]))
                          )
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 3), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 4), (0, 3), (0, 1)]))
                        )
                      )
                      (.node 0 6   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 3)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 3)]))
                          )
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 4), (0, 3)]))
                        )
                      )
                    )
                  )
                  (.node 0 6   -- 22
                    (.node 1 2   -- 11
                      (.node 2 4   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 3)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 4), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (2, 4)]))
                        )
                      )
                      (.node 1 4   -- 7
                        (.node 0 4   -- 4
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 2), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (0, 3)]))
                          )
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 3)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 2), (0, 3)]))
                        )
                      )
                    )
                    (.node 1 4   -- 11
                      (.node 1 2   -- 4
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 2), (0, 4), (0, 3)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 3)]))
                        )
                      )
                      (.node 1 6   -- 7
                        (.node 2 4   -- 4
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 2), (0, 1), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 4), (0, 3)]))
                          )
                          (.node 1 2   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 3), (2, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (0, 4), (0, 2), (0, 3)]))
                          )
                        )
                        (.node 2 4   -- 3
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 3), (1, 5)]))
                        )
                      )
                    )
                  )
                )
                (.node 0 6   -- 37
                  (.node 1 3   -- 19
                    (.node 1 5   -- 9
                      (.node 2 4   -- 4
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (0, 1), (2, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (2, 3)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (2, 4), (2, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 1), (2, 4)]))
                        )
                      )
                      (.node 2 4   -- 5
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (2, 3)]))
                          (.leaf (swapProd [(0, 5), (2, 3)]))
                        )
                        (.node 1 4   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (2, 4), (2, 3)]))
                            (.leaf (swapProd [(0, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 4)]))
                        )
                      )
                    )
                    (.node 1 2   -- 10
                      (.node 1 4   -- 5
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 4), (0, 5), (1, 2), (1, 3)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 5), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (1, 2), (1, 4), (1, 3)]))
                          )
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 5), (1, 3), (2, 4)]))
                          (.leaf (swapProd [(0, 5), (1, 3), (1, 2), (1, 4)]))
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 4), (0, 5), (1, 3)]))
                          (.leaf (swapProd [(0, 5), (1, 3)]))
                        )
                        (.node 2 4   -- 3
                          (.leaf (swapProd [(0, 5), (1, 4), (1, 3)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 5), (1, 4), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (1, 4), (2, 3)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 18
                    (.node 2 4   -- 9
                      (.node 1 3   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (2, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (2, 3)]))
                        )
                        (.node 1 2   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 2), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 3)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (2, 4), (2, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (0, 1), (2, 4)]))
                        )
                        (.node 1 3   -- 3
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (2, 4), (2, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (2, 4)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 2), (1, 4), (1, 3)]))
                        )
                      )
                    )
                    (.node 3 4   -- 9
                      (.node 1 6   -- 5
                        (.node 1 2   -- 3
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 3), (2, 4)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 5), (1, 4), (1, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 5), (1, 4), (1, 2), (1, 3)]))
                          )
                        )
                        (.node 2 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 1), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 3), (0, 1), (0, 5)]))
                        )
                      )
                      (.node 1 2   -- 4
                        (.node 1 3   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 2), (1, 4)]))
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 3), (1, 2), (1, 4)]))
                        )
                        (.node 1 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 5), (1, 4), (2, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 5), (2, 3)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 2   -- 66
                (.node 1 3   -- 34
                  (.node 2 5   -- 17
                    (.node 5 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 3), (0, 1)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (4, 6)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 3), (0, 1)]))
                        )
                      )
                      (.node 0 5   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (0, 1), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (0, 1)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 3), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (4, 5)]))
                        )
                      )
                    )
                    (.node 0 4   -- 9
                      (.node 0 6   -- 6
                        (.node 1 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 2), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 1), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (2, 3)]))
                        )
                        (.node 1 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 1), (4, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (2, 3), (4, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (2, 3), (4, 6)]))
                        )
                      )
                      (.node 1 5   -- 3
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 2), (0, 3), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 1), (2, 3)]))
                        )
                        (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (2, 3)]))
                      )
                    )
                  )
                  (.node 2 5   -- 17
                    (.node 5 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 3), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 3)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (4, 6)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 3)]))
                        )
                      )
                      (.node 0 5   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (4, 5)]))
                        )
                      )
                    )
                    (.node 0 4   -- 9
                      (.node 0 6   -- 6
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 2), (0, 3)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 1), (0, 2), (0, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (1, 2), (1, 3)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (4, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 3), (4, 6)]))
                            (.leaf (swapProd [(0, 5), (1, 2), (1, 3), (4, 6)]))
                          )
                        )
                      )
                      (.node 1 5   -- 3
                        (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 2), (0, 3)]))
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 1), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (1, 2), (1, 3)]))
                        )
                      )
                    )
                  )
                )
                (.node 1 6   -- 32
                  (.node 1 5   -- 17
                    (.node 5 6   -- 8
                      (.node 0 6   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 3), (1, 2), (4, 6), (4, 5)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 3), (1, 2)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (1, 2), (4, 6)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 3), (1, 2)]))
                        )
                      )
                      (.node 0 5   -- 4
                        (.node 0 6   -- 2
                          (.leaf (swapProd [(0, 3), (1, 2), (4, 6)]))
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 3), (1, 2)]))
                        )
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 3), (1, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 2), (4, 5)]))
                        )
                      )
                    )
                    (.node 0 4   -- 9
                      (.node 0 6   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 2), (0, 1), (0, 3)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 4), (0, 6), (0, 5), (1, 3)]))
                          )
                        )
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 3), (4, 6)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (4, 6)]))
                            (.leaf (swapProd [(0, 5), (1, 3), (4, 6)]))
                          )
                        )
                      )
                      (.node 2 5   -- 3
                        (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 2), (0, 1), (0, 3)]))
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 5), (1, 3)]))
                        )
                      )
                    )
                  )
                  (.node 0 4   -- 15
                    (.node 5 6   -- 6
                      (.node 2 5   -- 3
                        (.leaf (swapProd [(0, 5), (0, 2), (0, 1), (0, 4), (0, 6), (0, 3)]))
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (1, 4), (1, 6), (1, 3)]))
                        )
                      )
                      (.node 0 5   -- 3
                        (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 1), (0, 3)]))
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 2), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 3), (1, 4), (1, 6), (1, 2)]))
                        )
                      )
                    )
                    (.node 1 4   -- 9
                      (.node 2 5   -- 5
                        (.node 1 5   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (1, 4), (1, 5), (1, 2)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 4), (0, 5), (0, 3)]))
                          )
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 4), (1, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 4), (0, 5)]))
                        )
                      )
                      (.node 2 5   -- 4
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 5), (1, 2)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 1), (0, 5), (0, 3)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 5)]))
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree757 : Tree 7 :=
            (.node 3 6   -- 168
              (.node 1 6   -- 84
                (.node 1 3   -- 42
                  (.node 2 4   -- 21
                    (.node 0 4   -- 11
                      (.node 5 6   -- 6
                        (.node 1 5   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 6), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (2, 4), (2, 6), (2, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (2, 4), (2, 6), (2, 3)]))
                        )
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 3), (0, 1)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 2), (0, 3), (0, 1)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (2, 4), (2, 6)]))
                          )
                        )
                      )
                      (.node 3 5   -- 5
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 1), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (2, 4), (2, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 5), (0, 3), (0, 1)]))
                          )
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 4), (0, 5), (0, 1)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 4), (0, 5)]))
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 1), (2, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (2, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 3), (0, 1)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 2), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 5), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 5), (0, 1)]))
                        )
                      )
                      (.node 3 4   -- 4
                        (.node 4 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 2), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 5)]))
                        )
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 2), (0, 5)]))
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 21
                    (.node 0 4   -- 10
                      (.node 2 5   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 2), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 2), (0, 3)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 3), (2, 4), (2, 6)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (4, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (2, 4), (2, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 5), (0, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (2, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (2, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 3)]))
                          )
                        )
                      )
                    )
                    (.node 3 5   -- 11
                      (.node 2 4   -- 5
                        (.node 0 4   -- 2
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 4), (0, 6), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 2), (1, 4), (1, 5)]))
                        )
                        (.node 1 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (1, 2), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (1, 2), (1, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 5), (0, 1), (0, 3)]))
                        )
                      )
                      (.node 4 6   -- 6
                        (.node 1 4   -- 3
                          (.leaf (swapProd [(0, 6), (0, 4), (0, 3), (0, 1), (0, 2), (0, 5)]))
                          (.node 3 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 2), (0, 5), (1, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 4), (0, 1), (0, 3), (0, 2), (0, 5)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 4), (1, 6), (1, 3)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 2), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 2), (0, 5)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 1 2   -- 42
                  (.node 2 4   -- 21
                    (.node 0 4   -- 11
                      (.node 1 5   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 2), (0, 3)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 1), (0, 2), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (1, 2), (1, 4), (1, 6)]))
                          )
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (2, 4), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 6), (0, 1), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 5), (1, 3), (2, 4), (2, 6)]))
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 3), (4, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 4), (0, 5), (0, 3)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 5), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (2, 4), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 5), (1, 3)]))
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 5 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 1), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (1, 3)]))
                        )
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 5), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (2, 5)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 4), (1, 2), (1, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 1), (0, 4), (0, 3)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 3), (2, 5)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 4), (0, 2), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (1, 4), (1, 3)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 5), (1, 4)]))
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 21
                    (.node 0 4   -- 11
                      (.node 2 5   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (0, 3)]))
                          (.node 1 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 1), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (1, 4), (1, 6)]))
                          )
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 6), (0, 2), (0, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (1, 4), (1, 6)]))
                          )
                          (.leaf (swapProd [(0, 5), (1, 4), (1, 6), (1, 2), (1, 3)]))
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (4, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 5), (0, 3)]))
                        )
                        (.node 3 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 5), (0, 2), (0, 3)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 1), (0, 4), (0, 5)]))
                        )
                      )
                    )
                    (.node 2 4   -- 10
                      (.node 5 6   -- 4
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (1, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 3), (0, 1), (0, 5)]))
                        )
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 3)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 2), (0, 3)]))
                        )
                      )
                      (.node 3 5   -- 6
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 3), (1, 5), (2, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 3), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (0, 2), (0, 4), (0, 3)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 4 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 3), (0, 1), (0, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 3), (0, 1), (0, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 2), (0, 4), (0, 1), (0, 5)]))
                        )
                      )
                    )
                  )
                )
              )
              (.node 1 3   -- 84
                (.node 1 6   -- 42
                  (.node 2 4   -- 21
                    (.node 0 4   -- 11
                      (.node 3 5   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (0, 1), (2, 3)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (0, 1), (2, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 4), (0, 6), (0, 1)]))
                          )
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (0, 1), (2, 4), (2, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 6), (0, 1)]))
                          )
                          (.leaf (swapProd [(0, 5), (2, 4), (2, 6)]))
                        )
                      )
                      (.node 3 5   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (2, 3), (4, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 1), (2, 4), (2, 5), (2, 3)]))
                        )
                        (.node 1 5   -- 3
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (2, 4), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 5)]))
                        )
                      )
                    )
                    (.node 1 5   -- 10
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 6), (0, 1), (2, 5), (2, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 1)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (2, 5)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 2), (0, 5), (0, 1)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (0, 1), (3, 4)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (2, 5), (3, 4)]))
                          )
                        )
                      )
                      (.node 4 6   -- 4
                        (.node 1 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 2), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 3), (0, 4), (0, 1), (0, 2), (0, 5)]))
                        )
                        (.node 3 4   -- 2
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (3, 4)]))
                        )
                      )
                    )
                  )
                  (.node 1 5   -- 21
                    (.node 0 4   -- 10
                      (.node 2 5   -- 4
                        (.node 0 5   -- 2
                          (.leaf (swapProd [(0, 4), (0, 6), (2, 3)]))
                          (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (2, 3)]))
                        )
                        (.node 3 5   -- 2
                          (.leaf (swapProd [(0, 5), (0, 3), (0, 2), (0, 4), (0, 6)]))
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 6)]))
                        )
                      )
                      (.node 2 4   -- 6
                        (.node 2 5   -- 3
                          (.leaf (swapProd [(0, 6), (2, 3), (4, 5)]))
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (2, 4), (2, 5), (2, 3)]))
                            (.leaf (swapProd [(0, 6), (2, 4), (2, 5)]))
                          )
                        )
                        (.node 3 4   -- 3
                          (.node 3 5   -- 2
                            (.leaf (swapProd [(0, 6), (2, 5), (2, 3)]))
                            (.leaf (swapProd [(0, 6), (2, 5)]))
                          )
                          (.leaf (swapProd [(0, 6), (2, 5), (3, 4)]))
                        )
                      )
                    )
                    (.node 3 4   -- 11
                      (.node 5 6   -- 6
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 5), (1, 2), (1, 4), (1, 6)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 5)]))
                          )
                        )
                        (.node 0 4   -- 3
                          (.leaf (swapProd [(0, 5), (0, 1), (0, 2), (0, 4), (0, 6)]))
                          (.node 2 4   -- 2
                            (.leaf (swapProd [(0, 6), (1, 2), (1, 4), (1, 5)]))
                            (.leaf (swapProd [(0, 6), (1, 2), (1, 5)]))
                          )
                        )
                      )
                      (.node 1 4   -- 5
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 2), (0, 5), (3, 4)]))
                          (.leaf (swapProd [(0, 6), (1, 2), (1, 5), (3, 4)]))
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (1, 3), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 4), (0, 2), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 4), (1, 2), (1, 5)]))
                          )
                        )
                      )
                    )
                  )
                )
                (.node 1 2   -- 42
                  (.node 2 4   -- 21
                    (.node 0 4   -- 11
                      (.node 1 5   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (1, 2), (1, 3)]))
                          (.node 2 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (1, 2), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 2), (0, 4), (0, 6)]))
                          )
                        )
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 4), (0, 6), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 3), (1, 2), (1, 4), (1, 6)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 3), (0, 2), (0, 4), (0, 6)]))
                          )
                        )
                      )
                      (.node 1 5   -- 5
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (1, 2), (1, 3), (4, 5)]))
                          (.leaf (swapProd [(0, 6), (1, 2), (1, 4), (1, 5), (1, 3)]))
                        )
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 6), (1, 3), (2, 4), (2, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 2), (0, 4), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (1, 3), (1, 2), (1, 4), (1, 5)]))
                          )
                        )
                      )
                    )
                    (.node 1 4   -- 10
                      (.node 3 5   -- 4
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (1, 2), (1, 5), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (1, 3), (2, 5)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 3), (0, 2), (0, 5)]))
                          (.leaf (swapProd [(0, 6), (1, 3), (1, 2), (1, 5)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 6), (1, 4), (1, 3), (2, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 3), (0, 2), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (1, 4), (1, 3), (1, 2), (1, 5)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 5), (1, 4)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 2), (0, 5)]))
                            (.leaf (swapProd [(0, 6), (1, 4), (1, 2), (1, 5)]))
                          )
                        )
                      )
                    )
                  )
                  (.node 1 4   -- 21
                    (.node 0 4   -- 11
                      (.node 2 5   -- 6
                        (.node 0 5   -- 3
                          (.leaf (swapProd [(0, 4), (0, 6), (1, 3)]))
                          (.node 1 5   -- 2
                            (.leaf (swapProd [(0, 5), (0, 4), (0, 6), (1, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 3), (0, 1), (0, 4), (0, 6)]))
                          )
                        )
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 5), (0, 2), (0, 3), (0, 1), (0, 4), (0, 6)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 5), (1, 4), (1, 6), (2, 3)]))
                            (.leaf (swapProd [(0, 5), (0, 1), (0, 4), (0, 6), (2, 3)]))
                          )
                        )
                      )
                      (.node 2 5   -- 5
                        (.node 1 5   -- 2
                          (.leaf (swapProd [(0, 6), (1, 3), (4, 5)]))
                          (.leaf (swapProd [(0, 6), (1, 4), (1, 5), (1, 3)]))
                        )
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 6), (1, 4), (1, 5), (1, 2), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 4), (0, 5), (2, 3)]))
                            (.leaf (swapProd [(0, 6), (1, 4), (1, 5), (2, 3)]))
                          )
                        )
                      )
                    )
                    (.node 2 4   -- 10
                      (.node 3 5   -- 4
                        (.node 2 5   -- 2
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 3)]))
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 2), (1, 3)]))
                        )
                        (.node 5 6   -- 2
                          (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (2, 3)]))
                          (.leaf (swapProd [(0, 6), (1, 5), (2, 3)]))
                        )
                      )
                      (.node 3 4   -- 6
                        (.node 3 5   -- 3
                          (.leaf (swapProd [(0, 6), (1, 5), (1, 2), (1, 4), (1, 3)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (2, 4), (2, 3)]))
                            (.leaf (swapProd [(0, 6), (1, 5), (2, 4), (2, 3)]))
                          )
                        )
                        (.node 4 6   -- 3
                          (.leaf (swapProd [(0, 6), (0, 2), (0, 4), (0, 1), (0, 5)]))
                          (.node 5 6   -- 2
                            (.leaf (swapProd [(0, 6), (0, 1), (0, 5), (2, 4)]))
                            (.leaf (swapProd [(0, 6), (1, 5), (2, 4)]))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )

private def tree758 : Tree 7 :=
          (.node 2 6   -- 315
            tree756
            tree757
          )

private def tree759 : Tree 7 :=
        (.node 4 5   -- 630
          tree755
          tree758
        )

private def tree760 : Tree 7 :=
      (.node 0 2   -- 1260
        tree752
        tree759
      )

private def tree761 : Tree 7 :=
    (.node 2 3   -- 2520
      tree745
      tree760
    )

private def tree762 : Tree 7 :=
  (.node 0 1   -- 5040
    tree730
    tree761
  )

/-- A `13`-comparison decision tree sorting seven positions.  A node
`.node i j l r` compares positions `i` and `j`: `l` is taken when `x i < x j`,
`r` otherwise.  The comment on each internal node is the number of orderings of
the seven positions consistent with the answers that lead to it. -/
def tree7 : Tree 7 :=
  tree762

/-- The depth is `13`: thirteen comparisons always suffice.  (`depth` is the
maximum over leaves, so some leaf sits exactly at depth `13`.) -/
theorem tree7_depth : depth tree7 = 13 := by decide

/-- As many leaves as there are orderings of seven elements. -/
theorem tree7_numLeaves : numLeaves tree7 = 5040 := by decide

-- `decide` folds over the `7! = 5040` canonical inputs listed by `allPerms 7`
-- (`Verify.lean`), so this no longer touches the `Fintype (Equiv.Perm (Fin 7))`
-- instance that filters the `7 ^ 7 = 823543` functions `Fin 7 → Fin 7`.  The fold
-- is still `5040` elements deep, past the elaborator's default recursion limit of
-- 1000, and far past the default heartbeat budget, so both limits are lifted.
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
/-- The tree sorts: on all `7! = 5040` canonical inputs it outputs the sorting
permutation, hence on every input with distinct values. -/
theorem tree7_correct : Correct (α := ℕ) tree7 :=
  correct_of_allPerms (by decide)

/-- **`S 7 = 13`**: thirteen comparisons sort seven elements, and counting rules
out twelve. -/
theorem S_seven : S 7 = 13 := by
  refine le_antisymm ?_ ?_
  · -- upper bound: the adaptive tree
    refine (S_le_iff 7 13).2 ⟨tree7, tree7_correct, ?_⟩
    rw [tree7_depth]
  · -- lower bound: `Nat.clog 2 7! = 13`
    have h := S_lower 7
    have h5040 : Nat.clog 2 (Nat.factorial 7) = 13 := by decide
    omega

/-- **Thirteen comparisons are necessary in the *comparison-count* reading too**:
no correct tree keeps every input at `≤ 12` comparisons. -/
theorem seven_needs_thirteen_comparisons :
    ¬ ∃ t : Tree 7, Correct (α := ℕ) t ∧
      ∀ x : Fin 7 → ℕ, Function.Injective x → cost t x ≤ 12 := by
  rintro ⟨t, ht, hcost⟩
  have hwc : worstCase t ≤ 12 := by
    apply Finset.sup_le
    intro p _
    exact hcost (xOfPerm p) (xOfPerm_injective p)
  have hlb := logb_factorial_le_worstCase ht
  have h5040 : (12 : ℝ) < Real.logb 2 (Nat.factorial 7) := by
    have hfac : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num [Nat.factorial]
    rw [hfac]
    have hpow : (2 : ℝ) ^ 12 < 5040 := by norm_num
    calc (12 : ℝ) = Real.logb 2 ((2 : ℝ) ^ 12) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
      _ < Real.logb 2 (5040 : ℝ) :=
          Real.logb_lt_logb (b := 2) (by norm_num : (1 : ℝ) < 2) (by positivity) hpow
  have : (worstCase t : ℝ) ≤ 12 := by exact_mod_cast hwc
  linarith

end SortBounds.Projects.SN
