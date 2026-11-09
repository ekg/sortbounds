# sortbounds — Lean 4 formalization of the comparison-sorting lower bound

Machine-checked proof, in Lean 4 + Mathlib, that **no comparison-based sorting
algorithm can beat `Θ(n log n)` comparisons**, together with a formalization of
**radix/counting sort** showing exactly how and why it escapes that bound.

* **Lower bound.** Every correct comparison sort has a decision tree with at
  least `n!` leaves; a binary tree of depth `d` has at most `2^d` leaves. Hence
  some input needs at least `log₂(n!)` comparisons, and since `n! ≥ (n/2)^(n/2)`
  this is `Ω(n log n)`.
* **Radix sort.** Stable counting sort + LSD radix sort, proved correct (sorted
  by the lexicographic key), proved **comparison-free** (it never inspects any
  order on the elements), with its cost `d·(n+b)` made explicit.

Everything below is proved with no `sorry`, no `axiom`, and no `native_decide`
in the main results (see [`#print axioms`](#axioms)).

## What exactly is proved

| Theorem | Statement |
| --- | --- |
| `SortBounds.factorial_le_two_pow_depth` | a correct comparison sort's decision tree has `n! ≤ 2 ^ depth` |
| `SortBounds.factorial_le_two_pow_worstCase` | `n! ≤ 2 ^ (worst-case comparisons over inputs)` |
| `SortBounds.exists_input_cost_ge` | **there is an input** with distinct keys needing `≥ log₂(n!)` comparisons |
| `SortBounds.depth_ge_quarter` | `n ≥ 64 → depth ≥ n/4 · log₂ n` |
| `SortBounds.exists_input_cost_ge_quarter` | `n ≥ 64 → some input needs `≥ n/4 · log₂ n` comparisons |
| `SortBounds.not_forall_cost_lt_quarter` | no correct sort stays below `n/4 · log₂ n` on all inputs |
| `SortBounds.avg_cost_ge_log2_factorial` | expected comparisons over a uniform random ordering is `≥ log₂(n!)` |
| `SortBounds.max_cost_ge_log2_factorial` | the maximum over inputs is `≥ log₂(n!)` |
| `SortBounds.half_pow_le_factorial` | `(n/2)^(n/2) ≤ n!` |
| `SortBounds.logb_factorial_ge_quarter` | `n ≥ 64 → n/4 · log₂ n ≤ log₂(n!)` |
| `SortBounds.radixSort_sorted` / `radixSort_perm` | LSD radix sort sorts (lexicographically) and moreover is a permutation |
| `SortBounds.countingSort_stable` | counting sort is stable |
| `SortBounds.radixSort_ignores_comparison` | radix sort makes **zero** element comparisons |
| `SortBounds.radixCost_eq_passes` | radix sort costs exactly `d` passes of `n + b` unit operations |
| `SortBounds.radixSort_strict_sorted` | distinct keys are output in strict lexicographic order |
| `SortBounds.radixSort_keys_congr` | the output depends only on the key vectors, not on the elements |
| `SortBounds.msortCount_sorted` / `msortCount_perm` | counted merge sort sorts and is a permutation |
| `SortBounds.msortCount_le` | merge sort uses at most `2·n·(⌈log₂ n⌉+1)` comparisons |

Together, `msortCount_le` and `exists_input_cost_ge_quarter` say that the optimal
worst case is `Θ(n log n)`: no algorithm does better than `n/4 · log₂ n`, and
merge sort does `≤ 2n(⌈log₂ n⌉+1)`.

## The model

A deterministic comparison-based algorithm **is** a binary decision tree
(`SortBounds.Tree`): internal nodes ask `x i < x j?`, leaves carry a candidate
output permutation. `run` executes the tree on an input, `cost` counts the
comparisons on that input, `depth` is the worst case over the tree, and
`Correct` says that on every input with pairwise distinct values the output is
the unique sorting permutation (`Sorts`).

This is model-faithful without any programming-language semantics or step
counting: every comparison sort — quicksort, mergesort, heapsort, a handwritten
Fortran routine — compiles to such a tree, and every such tree is a comparison
sort.

### Two subtleties that are handled, not waved away

1. **Reachability.** A tree can have a leaf that *no consistent input* ever
   reaches (e.g. the outcome sequence `x₁<x₂, x₂<x₃, x₃<x₁`). Bounding `depth`
   alone therefore bounds the tree, not the algorithm's behaviour on inputs.
   `WorstCase.lean` closes the gap by proving the bound directly for
   `worstCase t = max over the n! canonical inputs of cost`, using the fact that
   distinct permutations reach distinct leaves (a `2^c` counting argument split
   at the root: `card_le_pow_of_cost_le`). The Isabelle/AFP formalization
   defines the worst case as a maximum over linear orders and *deliberately
   drops* reachability; CLRS's height argument assumes a tree that no input
   follows. Here both the tree statement and the "some input" statement are
   proved, so nothing is lost.
2. **Randomized algorithms.** A randomized comparison sort is a distribution
   over deterministic comparison trees; fixing the coin tosses gives a tree `t`,
   so for every instantiation the worst case is `≥ log₂(n!)` by the theorems
   here, hence so is the expected worst case. (Not formalized separately: it is
   a two-line argument over the deterministic statement.)
3. **"Best case" is not the claim.** Every comparison sort's *per-input* best
   case is `n − 1` comparisons (already sorted input). What is `Θ(n log n)` is
   the **optimal worst case** — the minimum over algorithms of the maximum over
   inputs — and, as proved here, the **average case** over uniformly random
   orderings. The lower bound is a statement about *all* correct algorithms,
   not about a particular one's lucky input.

### Where `log₂(n!)` comes from

`Basic.lean`: for an injective input the sorting permutation is unique
(`Sorts.unique`), and there is one canonical input `xOfPerm p` per permutation
`p`. So the map `p ↦ leaf reached` is injective on the `n!` permutations, the
tree has `≥ n!` leaves, and `#leaves ≤ 2^depth`. No adversary argument, no
consistency/constructibility lemma, no Stirling approximation is needed for the
exact form; the elementary `n! ≥ (n/2)^(n/2)` (`Stirling.lean`) is only used to
pass to the familiar `Ω(n log n)` form.

## Radix sort: why it does not contradict the lower bound

`Radix.lean` proves that LSD radix sort is correct, stable, and makes **no
comparisons between elements at all** — it only distributes elements into `b`
buckets `d` times, using the digits of their keys. Its cost is `d·(n+b)`
elementary operations.

Formally, `radixSort` takes no comparison argument at all and `radixSort_ignores_comparison`
shows the output is independent of any comparison oracle (the honest content is
`radixSort_keys_congr`: only the key vectors matter), while `radixSort_sorted`
and `radixSort_perm`/`radixSort_strict_sorted` say it really sorts.

That is not a counterexample to the lower bound, and the formalization makes
the reason precise: the lower bound is a theorem about **comparison trees**
(`Tree n`), i.e. algorithms whose only access to the data is a comparison
oracle. Radix sort instead *reads the key* — it uses the structure of a key
space of size `b^d`, which is extra information a comparison sort may not use.
The information-theoretic content (`n! ≤ 2^depth`) is still true: radix sort's
decisions are not binary comparisons, so the counting argument simply does not
apply to it. In the unit-cost word-RAM with `w`-bit keys, taking base
`b = 2^r` gives cost `(w/r)(n + 2^r)`, which for `r = Θ(log log n)` is
`o(n log n)` — comparison sorts cannot follow, because a comparison sort's only
inputs in that model are still *orderings*, of which there are `n!`.

## Prior art (checked, not re-invented)

* **Isabelle/HOL (AFP)**, M. Eberl, *Lower bound on comparison-based sorting
  algorithms*, 2017 — <https://isa-afp.org/entries/Comparison_Sort_Lower_Bound.html>.
  Central theorem: `fact (length xs) ≤ 2 ^ count_wc_queries Rs sorter` and
  `log 2 (fact n) ≤ count_wc_queries`, with an `Ω(n ln n)` corollary. It models
  a sorter as `Query a b (bool ⇒ sorter) | Return (list)` and defines the worst
  case as a maximum over linear orders (dropping reachability).
* **Coq/Rocq (MathComp)**, A. Azevedo de Amorim, 2015 —
  <https://poleiro.info/posts/2015-03-25-analyzing-sorting-algorithms.html>:
  `Inductive sort_alg (n:nat) := Compare (i j : 'I_n) (l r : sort_alg n) | Done of 'S_n`,
  with `Lemma card_perms : #|perms a| <= 2 ^ comparisons a` and the
  Stirling-free `(n * log2 n)./2 <= comparisons a`.
* **Lean 4 outside Mathlib.** CLRS-Lean (Ch. 8) proves
  `height_le_logb_factorial` and `comparisonSort_worstCase_lowerBound`;
  G. Irving's `Comp/Sort.lean` proves an oracle-cost *average-case* bound
  (`Sorts.le_cost`). Mathlib itself has sorting *correctness*
  (`List.mergeSort`, `List.insertionSort`) but **no** lower bound.
* **Textbook statements.** CLRS Theorem 8.1: "Any comparison sort algorithm
  requires `Ω(n lg n)` comparisons in the worst case"; Corollary 8.2
  (mergesort/heapsort asymptotically optimal); Problem 8-1 for the
  probabilistic (randomized/average) version. Knuth TAOCP vol. 3 §5.3.1
  ("Minimum-Comparison Sorting") treats `⌈lg n!⌉` as the information-theoretic
  bound.
* **Radix/counting sort.** Isabelle/HOL `HOL-ex/Radix_Sort` (Nipkow; locale
  `Radix_Sort` with `stable_sort_key`, `sorted_radix_sort`) — correctness only;
  KeY (de Gouw, de Boer, Rot, JAR 2014, and the LNCS 10001 chapter) verifies
  counting/radix sort; CLRS-Lean proves an `O(d(n+k))` cost bound.

So: the result is classical and has been machine-checked before (in Isabelle and
Coq); what this repository adds is a small, readable Lean 4 + Mathlib version
that (a) proves the bound **on actual inputs** (reachability handled), (b) proves
the **average-case** bound, and (c) formalizes radix sort's correctness,
comparison-freeness and cost ledger side by side with the lower bound, so the
"why doesn't radix sort break the bound" question is answered by the code.

## Files

```
SortBounds/Basic.lean       sorting permutations, uniqueness, canonical inputs
SortBounds/Tree.lean        decision trees, run/cost/depth/leaves, n! ≤ 2^depth
SortBounds/Aggregate.lean   2^c and (1/2)^cost counting lemmas
SortBounds/WorstCase.lean   worst case over actual inputs, log₂(n!) bound
SortBounds/Stirling.lean    (n/2)^(n/2) ≤ n!, log₂(n!) ≥ n/4·log₂ n
SortBounds/LowerBound.lean  headline Ω(n log n) theorems
SortBounds/Average.lean     expected comparisons over random ordering
SortBounds/Examples.lean    concrete trees: n = 2 sharp, n = 3 needs 3
SortBounds/Radix.lean       counting sort, radix sort, no comparisons, cost
SortBounds/UpperBound.lean  matching upper bound: a counted O(n log n) sort
```

See [`docs/PRIOR-ART.md`](docs/PRIOR-ART.md) for the Isabelle, Coq and Lean 4
prior art with exact theorem statements.

## Build

```sh
lake exe cache get   # prebuilt Mathlib oleans (zero downloads if already in ~/.cache/mathlib)
lake build           # Lean 4.35.0-rc2 (lean-toolchain) + Mathlib (pinned in lake-manifest.json)
make check           # build + grep for sorry/admit/axiom
make axioms          # print the axioms each headline theorem depends on
```

## Axioms

Each headline theorem is checked to depend only on Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`); see
`scripts/axioms.lean`.

## License

MIT.
