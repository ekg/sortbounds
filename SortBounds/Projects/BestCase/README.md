# Lane: BestCase — `n − 1` comparisons are needed on *every* input

**Question.** The repository proves the worst case (`Ω(n log n)`) and the average
case (`≥ log₂ n!` over random orderings).  The third corner is the **best case**:
`n − 1`.  The README asserts it —

> "The already-sorted input forces `n − 1` comparisons of any correct sort, so no
> correct comparison sort's best case is below `n − 1`."

— and it is **not proved**, and it is stated *less* strongly than the truth: the
bound holds for **every** injective input, not only for the sorted one.  Formalise
it and fix the wording.

## Why it is true (the argument to formalise)

Run a correct tree on an injective `x`.  Let `G` be the graph on `Fin n` whose edges
are the *distinct* pairs compared along the path taken by `x`.  If `G` were
disconnected, split `Fin n` into two blocks and define
`x' i = x i + if i ∈ B then C else 0` for a large `C`.  Then

* every comparison *made* on the path has the same answer for `x'` as for `x`
  (within a block the values are unchanged; across blocks nothing was compared),
* so the tree reaches the same leaf, i.e. the same output permutation `r`,
* but `x'` is a different linear order (the block `B` has been pushed above the
  rest), so no single `r` can sort both — contradicting `Correct` on `x'`
  (which is injective).

Hence `G` is connected, and a connected graph on `n` vertices has at least `n − 1`
edges; the number of *distinct* edges is at most the number of comparisons made.

## Contract (exact target signatures)

```lean
namespace SortBounds.Projects.BestCase

open SortBounds

/-- The distinct pairs compared on the path taken by `x`. -/
def comparedPairs (t : Tree n) (x : Fin n → ℕ) : Finset (Sym2 (Fin n))

theorem card_comparedPairs_le_cost (t : Tree n) (x : Fin n → ℕ) :
    (comparedPairs t x).card ≤ cost t x

/-- The graph of comparisons along a path is connected, for a correct tree. -/
theorem connected_comparedPairs {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) : (comparedPairs t x : SimpleGraph (Fin n)).Connected

/-- **The best case is `n − 1`**: every correct comparison sort makes at least `n − 1`
comparisons on *every* input with distinct values. -/
theorem pred_le_cost {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) : n - 1 ≤ cost t x

end SortBounds.Projects.BestCase
```

## Milestones

* **M0** `comparedPairs` and `card_comparedPairs_le_cost` (structural recursion along
  the path: at a node, the pair is either already in the set or new).
* **M1** `connected_comparedPairs` — the perturbation argument above.  Two
  ingredients: (a) `run` depends only on the answers to the comparisons made
  (a "same answers ⟹ same leaf" lemma, by induction on the tree — the repository
  already has `run_eq_of_pattern` for *all* comparisons, which is stronger and may
  be usable, but a path-local version is cleaner); (b) `Sorts` against two different
  orders for the same permutation is impossible.
* **M2** `pred_le_cost` — connected ⟹ `n − 1 ≤ #edges`.  `SimpleGraph` has
  connectedness lemmas; if `card_edgeFinset` bookkeeping gets awkward, an induction
  on the edge list ("each edge merges at most two components, so `#components ≥
  n − #edges`") is fine — state whichever you prove.
* **M3 (stretch)** the matching upper bound for a *specific* tree: a correct tree
  and an input with `cost = n − 1` (linear insertion sort's tree on the sorted
  input), which would make `n − 1` exactly the best case.  Not required.

## Rules

Own only `SortBounds/Projects/BestCase/`.  `lake env lean`, no `lake build`, no git,
oleans in `/tmp`, no python.  No `sorry`/`axiom`/`native_decide`.  Edge cases:
`n = 0, 1` (`n - 1 = 0`, vacuous) — say what you prove there.  If a target is false
as stated, prove the true version and report exactly what changed.

## Prior art

This is folklore ("each element must be compared at least once, and the comparison
graph must be connected"), stated e.g. in Knuth TAOCP 5.3.1.  Not formalised
anywhere we know of.

## Log

* (empty)
