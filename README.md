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
| **the frame** | |
| `Core.card_le_pow_of_prefixFree` | prefix-free `b`-ary transcripts of length `≤ c` number at most `b ^ c` (a corollary of Mathlib's Kraft inequality) |
| `Core.logb_le_of_le_pow` | hence `log_b N ≤ c`: bits per probe |
| `Core.mean_cost_ge_logb` | Kraft sum `≤ 1` ⇒ mean cost `≥ log_b N`, for **any** branching factor |
| **comparison sorting** | |
| `Comparison.factorial_le_two_pow_depth` | a correct comparison sort's tree has `n! ≤ 2 ^ depth` |
| `Comparison.exists_input_cost_ge` | **there is an input** with distinct keys needing `≥ log₂(n!)` comparisons |
| `Comparison.exists_input_cost_ge_quarter` | `n ≥ 64 → some input needs ≥ n/4 · log₂ n` comparisons |
| `Comparison.avg_cost_ge_log2_factorial` | expected comparisons over a uniform random ordering is `≥ log₂(n!)` |
| `Comparison.exists_input_cost_ge_of_orderEmb` | the same for **any** linear order with `n` values in increasing order (`ℚ`, `ℝ`, …) |
| `Comparison.exists_depth_le_of_cost_le` | a tree whose every input costs `≤ d` can be replaced by one of depth `≤ d` — so "least depth" = "fewest comparisons that suffice" |
| **the best case** | |
| **`Projects.BestCase.pred_le_cost`** | **`n − 1 ≤ cost t x` for every injective `x`** — the best case is `n − 1`, on *every* input, not just the sorted one |
| `Projects.BestCase.exists_correct_cost_id_eq'` | and it is attained: a correct tree with `cost = n − 1` on a specific input |
| **the two halves, in one model** | |
| `SortTree.sortTree_depth_le` | an explicit `Correct` tree of depth `≤ n(⌈log₂ n⌉+1)` |
| `SortTree.S_sandwich` | **`⌈log₂ n!⌉ ≤ S n ≤ n(⌈log₂ n⌉+1)`**, both statements about `Tree n` |
| **models where the bound changes** | |
| `Instances.factorial_le_two_pow_length_of_sortsAll` | a sorting network needs `≥ log₂(n!)` **comparators** (it wins on depth, not work) |
| `Instances.sortsAll_of_sorts_zeroOne` | the 0-1 principle, stated over `Fin n → Fin 2` so it is **decidable** |
| `Instances.netTree_correct` | a verified network yields a correct `Tree n` of depth = #comparators |
| `Instances.radixSort_sorted` / `radixSort_perm` / `radixSort_keys_congr` | radix sort is correct, and its output depends only on the key vectors — hence zero element comparisons |
| **`Projects.Domain.probes_tight`** | **`log_b U` probes are necessary and `d = log_b U` suffice** for `b`-ary digit access on a domain of `b^d` keys — structure buys speed, and radix attains the bound *exactly*. (Model: a per-key digest plan, `KeyProc`; a general list algorithm over an array is **not** covered) |
| `Projects.Domain.wordram_probes` | with `w`-bit words: `n` word reads necessary and sufficient for `n` digits, and `log_{2^w}(b^d) = d` |
| **exact comparison counts** | |
| **`Projects.FjTree.S_eq_clog`** | **`S n = ⌈log₂ n!⌉` for `4 ≤ n ≤ 11`** — merge-insertion verified optimal; `S_eq_clog_large` the same for `n = 20, 21`; `S_pin` pins `S n` to within one for every `n ≤ 22` |
| `Projects.FordJohnson.fjCountJ_table` | `F(4..11) = 5,7,10,13,16,19,22,26`, i.e. `⌈log₂ n!⌉` at each; `fjCountJ_attains` says the count is attained by an explicit input |
| `Projects.SN.S_four` … `S_seven` | `S 4 = 5, S 5 = 7, S 6 = 10, S 7 = 13` by explicit kernel-checked trees — an independent route to the same values; `four_needs_five_comparisons` etc. give the comparison-count reading |
| `Projects.FjTree.fjCountJ_not_attained` | where the counting bound stops being tight: `fjCountJ 12 = 30 > 29 = ⌈log₂ 12!⌉`, `fjCountJ 22 = 71 > 70` |
| `Projects.FjTree.S_twelve_le` / `S_twenty_two_le` | **30 comparisons suffice for 12 elements** (Wells 1965) and **71 suffice for 22** (Peczarski), from FJA's tree; the literature's exact values `S 12 = 30`, `S 22 = 71` differ from what is proved here only in the lower bound |
| **the topological ingredient** | |
| **`Projects.BenOr.numComponents_distinctSet`** | **the distinctness set has exactly `n!` connected components** (`componentsEquivPerm`) — what Ben-Or's bound consumes; the bound itself (components ⇒ height, Milnor–Thom) is still a statement, not a proof |
| **open lanes (what is *not* proved)** | |
| `Projects.SN.S_twelve` (`S 12 = 30`) | open, and **not reachable by counting**: `12! < 2^29`, so any `L ≤ 2^d` is a tree of depth `≤ d` and leaf counting gives only `⌈log₂ 12!⌉ = 29`.  The known proofs are pruned searches (Wells 1971; Peczarski 2004) |
| `Projects.BenOr.exists_decidesReal_distinct` | an algebraic decision tree of degree `n(n-1)` decides element distinctness (non-vacuity for the semantics) |
| **`Projects.SAIS.kasai_cost_le` / `checkOn_computed_cost`** | Kasai builds the LCP array in `≤ 2n` character comparisons and a candidate suffix array is then verified in exactly `n − 1` inspections **reading that computed array**. Two separate bounds — the counters use different conventions for a scan that runs off the end, so they must not be added as one figure (`PROGRESS.md` says which unit each is in), versus `Θ(n²)` naive (proved on `aⁿ`); `kasai_lcp_correct` is the correctness of the array, `compare_lt_iff_saRank_lt` says a verified candidate *is* the suffix array, and `checkSaCounted_cost` ties the `n − 1` to an executable counter |
| `Projects.SAIS.inf'_lcpAt_le_lcp` | along *text* positions the LCP array gives only a sound lower bound (that is what licenses skipping); along a *sorted* chain it is the true LCP — `lcp_suffix_eq_inf'_of_increasing`. The naive/guided contrast on `aⁿ` is cubic-vs-quadratic; **sorting** in `O(n log n)` inspections is not formalised |
| `Projects.XY.pairSums` | the `X+Y` problem is modelled; the generic `N`-item bound is *not* a bound on it (Fredman's `O(n²)` scheme is why) |

Informally: the optimal worst case is `Θ(n log n)`, and that is now a *single-model*
statement — `S_sandwich` bounds the least tree depth from both sides.  A list-model
upper bound (`Instances.msortCount_le`) also exists and is not needed for that.

## The model

A deterministic comparison-based algorithm **is** a binary decision tree
(`SortBounds.Tree`): internal nodes ask `x i < x j?`, leaves carry a candidate
output permutation. `run` executes the tree on an input, `cost` counts the
comparisons on that input, `depth` is an upper bound on the comparisons made on
any input (`cost_le_depth`), and `Correct` says that on every input with pairwise
distinct values the output is the unique sorting permutation (`Sorts`).

This is model-faithful without any programming-language semantics or step
counting: every comparison sort — quicksort, mergesort, heapsort, a handwritten
Fortran routine — compiles to such a tree, and every such *correct* tree is a
comparison sort.  The headline theorems are stated for `ℕ`-valued inputs; the
transfer to any other value type is `SortBounds/General.lean`
(`exists_input_cost_ge_of_orderEmb`, `…_of_finset`), which uses the fact that
`run` and `cost` depend only on the input's comparison pattern
(`run_eq_of_pattern`, `cost_eq_of_pattern`).

### Three subtleties that are handled, not waved away

1. **Reachability.** A tree can have a leaf that *no consistent input* ever
   reaches (e.g. the outcome sequence `x₁<x₂, x₂<x₃, x₃<x₁`). Bounding `depth`
   alone therefore bounds the tree, not the algorithm's behaviour on inputs.
   `WorstCase.lean` closes the gap by proving the bound directly for
   `worstCase t = max over the n! canonical inputs of cost`, using the fact that
   distinct permutations reach distinct leaves (a `2^c` counting argument split
   at the root: `card_le_pow_of_cost_le`), and `exists_input_cost_ge` names an
   attaining input.  CLRS's height argument instead bounds the tree's longest
   path, which can be longer than any input's run; Eberl's AFP entry takes the
   same input-attained route (its worst case is a maximum over linear orders).
   Here the depth form is *also* derived, from the same elementary counting
   argument (`factorial_le_two_pow_depth`), so both statements are available.
2. **Randomized algorithms.** A randomized comparison sort is a distribution
   over deterministic comparison trees; fixing the coin tosses gives a tree `t`,
   so for every instantiation the worst case is `≥ log₂(n!)` by the theorems
   here, hence so is the expected worst case. (Not formalized separately: it is
   a two-line argument over the deterministic statement.)
3. **"Best case" is not the claim — and it is not `n log n`.** The best case is
   `n − 1`, and that is a theorem about *every* input, not about a lucky one:
   `BestCase.pred_le_cost` shows every correct comparison sort makes at least
   `n − 1` comparisons on every input with distinct values (if a comparison were
   missing, pushing one block of values above the other leaves every answer
   unchanged but both orders unsortable by the same permutation), and
   `BestCase.exists_correct_cost_id_eq'` exhibits a correct tree attaining it. So
   `n − 1` is exactly the best case, `≥ log₂ n!` the average over random orderings,
   and `Ω(n log n)` the optimal worst case — the three corners of the `Θ` picture,
   all in one model.

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
apply to it. In the unit-cost word-RAM with keys of `w = Θ(log n)` bits
(the usual case: keys bounded by a polynomial in `n`), taking base `b = 2^r`
gives cost `(w/r)(n + 2^r)`; with `r = Θ(log log n)` this is
`Θ(n log n / log log n) = o(n log n)`.  Comparison sorts cannot follow, because
a comparison sort's only access to its input is the `n!` possible orderings,
regardless of how the keys are represented.

## Prior art (checked, not re-invented)

* **Isabelle/HOL (AFP)**, M. Eberl, *Lower bound on comparison-based sorting
  algorithms*, 2017 — <https://isa-afp.org/entries/Comparison_Sort_Lower_Bound.html>.
  Central theorem: `fact (length xs) ≤ 2 ^ count_wc_queries Rs sorter` and
  `log 2 (fact n) ≤ count_wc_queries`, with an `Ω(n ln n)` corollary. It models
  a sorter as `Query a b (bool ⇒ sorter) | Return (list)`; its worst case
  `count_wc_queries` is a maximum over the `n!` linear orders, i.e. already the
  input-attained form (leaves no order reaches simply never contribute).
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

**What is genuinely new here** (as of 2026-11-11, and stated modestly):

1. **`S n = ⌈log₂ n!⌉` for `4 ≤ n ≤ 11`, and `n = 20, 21`** — merge-insertion
   (Ford–Johnson) proved correct *as a decision tree* and shown to have depth
   equal to the counting lower bound.  No formalization of this exists elsewhere
   that we could find.  With `S_pin`, `S n` is pinned to within one comparison for
   every `n ≤ 22`, and `S_eq_of_fjCountJ_eq` transfers any future size.
2. **`Θ(n log n)` inside a single model** — `⌈log₂ n!⌉ ≤ S n ≤ n(⌈log₂ n⌉+1)`,
   both halves about `Tree n`, with no list-model detour (`SortTree`).
3. **The frame, as a library** — one inequality (Kraft, from Mathlib) gives the
   worst case for any branching factor, and Gibbs gives the average case for any
   branching factor; the models it has been instantiated in (comparison trees,
   sorting networks + the 0-1 principle, radix, `X+Y`, algebraic decision trees,
   LCP-guided string comparison) are listed with their escape hatches in
   [`docs/MODELS.md`](docs/MODELS.md).
4. **Trust machinery** — `make check` fails on a `sorry` in any declaration, on an
   `axiom` or `native_decide` anywhere in `SortBounds/`, and on any listed theorem
   depending on `sorryAx`; 79 theorems are audited; CI runs it on every push.  That
   gate found a real silent failure (a renamed lemma left the audit erroring out
   while still "passing").

**What is not new**: the `Ω(n log n)` theorem itself (Isabelle 2017, Coq 2015,
CLRS Thm 8.1), radix sort's correctness (Isabelle, KeY), SA-IS (Isabelle AFP),
the 0-1 principle (Coq), AKS sorting networks (Lean, `girving/aks`), and the
literature's exact `S(n)` table — we *re-derive* and cross-check, we do not
discover.  `S 12 = 30` and the other non-counting lower bounds remain open here
and everywhere else short of a pruned search.

## Layout

The comparison-model result is **frozen**; work now happens in research lanes.
See [`docs/PROGRESS.md`](docs/PROGRESS.md) for the live dashboard and
[`docs/STRUCTURE.md`](docs/STRUCTURE.md) for the layout rules.

```
SortBounds/Core/Branching.lean      bits per probe: #outcomes ≤ b ^ #steps (Mathlib-only)
SortBounds/Comparison/              the comparison model and its Ω(n log n)
  Basic Tree Aggregate WorstCase Stirling LowerBound Average General Examples
SortBounds/Instances/               models where the bound changes
  Radix.lean MergeSort.lean
SortBounds/Projects/                research lanes, one directory each
  FordJohnson/  verified merge-insertion + exact comparison count
  SN/           certified minimum comparison counts S(n)
  XY/           sorting X+Y (Fredman/Berlekamp)
  BenOr/        algebraic decision trees
  SAIS/         suffix arrays: cost model (queued)
```

See [`docs/MODELS.md`](docs/MODELS.md) for the reusable frame — one inequality,
the models it has been instantiated in, what the bound becomes in each, and how
each model escapes it — and [`docs/PRIOR-ART.md`](docs/PRIOR-ART.md) for the
Isabelle, Coq and Lean 4 prior art with exact theorem statements — including what is *already done* and
therefore not worth redoing.

## Build

```sh
lake exe cache get   # prebuilt Mathlib oleans (zero downloads if already in ~/.cache/mathlib)
lake build           # Lean 4.35.0-rc2 (lean-toolchain) + Mathlib (pinned in lake-manifest.json)
make check           # build + no sorry + no axiom/native_decide + all listed theorems axiom-standard
make trust           # the axiom audit alone, with a count
```

CI runs `make check` and `make trust` on every push (`.github/workflows/lean.yml`).

## Axioms

The theorems listed in `scripts/axioms.lean` (every headline result plus the
radix/upper-bound statements) are checked to depend only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — in particular
no `sorryAx` and no `Lean.ofReduceBool`.  `msortCount_sorted`/`_perm`/`_le` and
the general-value-type theorems are included; `radixCost_eq_passes` and
`radixSort_ignores_comparison` are definitional (`rfl`) and add nothing.

## License

MIT.
