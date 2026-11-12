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

**Status: M0–M3 done.**  Files: `Compared.lean`, `Connected.lean`, `Main.lean`,
`Attain.lean`, `Sharp.lean` (in that import order).  No
`sorry`/`admit`/`axiom`/`native_decide`;
`#print axioms` on the headline results gives only `propext`, `Classical.choice`,
`Quot.sound`.

### Signatures, verbatim

Contract targets (M0–M2) — `comparedPairs`, `card_comparedPairs_le_cost` and
`pred_le_cost` are exactly as contracted:

```lean
def comparedPairs (t : Tree n) (x : Fin n → ℕ) : Finset (Sym2 (Fin n))
 theorem card_comparedPairs_le_cost (t : Tree n) (x : Fin n → ℕ) :
    (comparedPairs t x).card ≤ cost t x
 theorem pred_le_cost {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) : n - 1 ≤ cost t x
```

**Two changes to `connected_comparedPairs`, both forced** (the contracted form is
not typable, resp. false at `n = 0`):

1. `(comparedPairs t x : SimpleGraph (Fin n))` does not elaborate — Mathlib has no
   `Coe (Finset (Sym2 V)) (SimpleGraph V)`.  The graph is named instead:
   `def comparisonGraph (t : Tree n) (x : Fin n → ℕ) : SimpleGraph (Fin n) :=
   SimpleGraph.fromEdgeSet (comparedPairs t x : Set (Sym2 (Fin n)))`.
2. `SimpleGraph.Connected` is `Preconnected ∧ Nonempty V`, so at `n = 0` it is
   *false* for every graph on `Fin 0` (while `Correct` is vacuously true there).
   The true statement is `Preconnected`, landed unconditionally, plus the
   contracted `Connected` under `0 < n`:

```lean
theorem preconnected_comparisonGraph {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) : (comparisonGraph t x).Preconnected
 theorem connected_comparedPairs {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) (hn : 0 < n) : (comparisonGraph t x).Connected
```

Supporting lemmas (all landed and used):

```lean
theorem run_eq_of_agree (t : Tree n) (x y : Fin n → ℕ)
    (h : ∀ i j, s(i, j) ∈ comparedPairs t x → (x i < x j ↔ y i < y j)) :
    run t x = run t y
theorem symm_lt_of_sorts {x : Fin n → ℕ} {r : Equiv.Perm (Fin n)} (h : Sorts x r) {a b : Fin n}
    (hab : x a < x b) : r.symm a < r.symm b
theorem run_eq_of_add_const (t : Tree n) (x : Fin n → ℕ) (c : Fin n → ℕ) {B : Set (Fin n)}
    (hB : ∀ i j, s(i, j) ∈ comparedPairs t x → (i ∈ B ↔ j ∈ B))
    (hc : ∀ i j, (i ∈ B ↔ j ∈ B) → c i = c j) :
    run t x = run t fun i => x i + c i
theorem injective_add_of_two_values {x c : Fin n → ℕ} (hx : Function.Injective x) {C : ℕ}
    (hC : ∀ i, x i < C) (hc : ∀ i, c i = 0 ∨ c i = C) :
    Function.Injective fun i => x i + c i
theorem no_cross_pair {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) {B : Set (Fin n)}
    (hB : ∀ i j, s(i, j) ∈ comparedPairs t x → (i ∈ B ↔ j ∈ B))
    {i j : Fin n} (hi : i ∈ B) (hj : j ∉ B) (hlt : x i < x j) : False
theorem pred_le_card_comparedPairs {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) : n - 1 ≤ (comparedPairs t x).card
```

`n - 1 ≤ #edges` is obtained from Mathlib's
`SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one` (nothing about edges was
re-proved), specialised to the comparison graph; no component-counting induction was
needed.

Extras tied to the rest of the tree (cheap corollaries, same proof):

```lean
theorem pred_le_cost_id {t : Tree n} (h : Correct (α := ℕ) t) :
    n - 1 ≤ cost t (fun i : Fin n => (i : ℕ))
theorem pred_le_cost_xOfPerm {t : Tree n} (h : Correct (α := ℕ) t)
    (p : Equiv.Perm (Fin n)) : n - 1 ≤ cost t (xOfPerm p)
theorem pred_le_worstCase {t : Tree n} (h : Correct (α := ℕ) t) : n - 1 ≤ worstCase t
theorem pred_le_depth {t : Tree n} (h : Correct (α := ℕ) t) : n - 1 ≤ depth t
```

### M3 (stretch) — the bound is attained, `Attain.lean`

The sharpness witness is **not** insertion sort; it is the "sorted chain": compare
`x 0 < x 1`, `x 1 < x 2`, … in order, answer the identity permutation when all
answers are "yes", and hand every input that breaks the chain to an arbitrary
correct tree `T`.  That is correct (the all-yes path forces `x` strictly increasing;
any other input is sorted by `T`) and costs exactly `n - 1` on the sorted input.

```lean
noncomputable def chainAux (T : Tree n) : (k : ℕ) → k < n → Tree n
noncomputable def sortedChain : (n : ℕ) → Tree n → Tree n
theorem chainAux_sorts {T : Tree (m + 1)} (hT : Correct (α := ℕ) T) {x : Fin (m + 1) → ℕ}
    (hx : Function.Injective x) (k : ℕ) (hk : k < m + 1)
    (hinv : ∀ i : Fin m, k ≤ i.val → x i.castSucc < x i.succ) :
    Sorts x (run (chainAux T k hk) x)
theorem sortedChain_correct {T : Tree n} (hT : Correct (α := ℕ) T) :
    Correct (α := ℕ) (sortedChain n T)
theorem cost_chainAux_id (T : Tree n) (k : ℕ) (hk : k < n) :
    cost (chainAux T k hk) (fun i : Fin n => (i : ℕ)) = k
theorem exists_correct_cost_id_eq {T : Tree n} (hT : Correct (α := ℕ) T) :
    ∃ t : Tree n, Correct (α := ℕ) t ∧ cost t (fun i : Fin n => (i : ℕ)) = n - 1
```

`Correct T` is a carried hypothesis (a correct tree for every `n` exists:
`Projects.SN.exists_correct_tree`); the lane does not construct one, so `Attain.lean`
does not import the SN lane.  Non-vacuity of `Correct` is also exhibited inside the
lane: `def sortTwo : Tree 2`, `theorem sortTwo_correct : Correct (α := ℕ) sortTwo`,
`theorem sortTwo_cost : cost sortTwo (fun i : Fin 2 => (i : ℕ)) = 1` (= `2 - 1`).

`Sharp.lean` discharges that hypothesis with `Projects/SN.exists_correct_tree`, so the
statement is unconditional there:

```lean
theorem exists_correct_cost_id_eq' (n : ℕ) :
    ∃ t : Tree n, Correct (α := ℕ) t ∧ cost t (fun i : Fin n => (i : ℕ)) = n - 1
```

With `pred_le_cost` that pins the best case at `n - 1` for every `n`.

### Edge cases

* `n = 0`: `n - 1 = 0`, so `pred_le_cost` is trivially true (proved by `simp`), and
  `Correct` holds for every tree.  `connected_comparedPairs` is the only statement
  that needs `0 < n` (see above).
* `n = 1`: `n - 1 = 0`; the comparison graph has one vertex and no edges and is
  connected, so `connected_comparedPairs` applies.
* The perturbed input in the M1 argument may not be `0/1`-valued or bounded by
  `n - 1`; it is `x` plus `sup x + 1` on one block, and the argument only needs
  injectivity plus agreement on the compared pairs.

### Validation

`lake env lean` on each file, in import order, with oleans written to `/tmp`
(never into the repo): all four compile, no warnings.

### Integrator TODOs

1. Add to the umbrella `SortBounds.lean`:
   `import SortBounds.Projects.BestCase.Compared` … `.Connected` … `.Main` …
   `.Attain` … `.Sharp` (or just `import SortBounds.Projects.BestCase.Main`
   and `.Sharp` — `Sharp` pulls in `Attain`).  `Sharp.lean` imports
   `SortBounds.Projects.SN.Basic` (for `exists_correct_tree`); if the lane should
   not depend on SN, import every file except `Sharp` and use the hypothesis form
   `exists_correct_cost_id_eq`.
2. **Fix the weaker wording** in the root `README.md` (lines 99–101): it says the
   *already-sorted* input forces `n - 1`.  Suggested replacement, quoting what is
   proved:
   > "Best case" is not the claim.  `pred_le_cost` (`Projects/BestCase`) says every
   > correct comparison sort makes at least `n − 1` comparisons on **every** input
   > with pairwise distinct values, not only on the sorted one; `Attain.lean` shows
   > the bound is attained by a correct tree, so `n − 1` is exactly the best case.
   > What is `Θ(n log n)` is …
3. `docs/PROGRESS.md`: the BestCase row (`PROGRESS.md:157` already states the strong
   form) can now cite `pred_le_cost`, `connected_comparedPairs`,
   `exists_correct_cost_id_eq`.
