# Prior art: machine-checked lower bounds for comparison sorting

Notes gathered before writing the formalization, so that the repository states
clearly what is new and what is a re-derivation.  Claims marked *unverified*
were not checked against a primary source.

## Full formalizations of the `log₂(n!)` / `Ω(n log n)` bound

* **Isabelle/HOL (AFP)**, Manuel Eberl, *Lower bound on comparison-based
  sorting algorithms*, 15 Mar 2017.
  <https://isa-afp.org/entries/Comparison_Sort_Lower_Bound.html> ·
  theory rendering:
  <https://isa-afp.org/browser_info/current/AFP/Comparison_Sort_Lower_Bound/Comparison_Sort_Lower_Bound.html>

  Model (verbatim):
  ```isabelle
  datatype 'a sorter = Return "'a list" | Query 'a 'a "bool ⇒ 'a sorter"
  primrec count_queries :: "('a × 'a) set ⇒ 'a sorter ⇒ nat"
  definition count_wc_queries :: "('a × 'a) set set ⇒ 'a sorter ⇒ nat"
  primrec eval_sorter
  definition is_sorting :: "('a × 'a) set ⇒ 'a list ⇒ 'a list ⇒ bool"
  ```
  Central theorem (verbatim):
  ```isabelle
  theorem
    fixes sorter :: "'a sorter" and xs :: "'a list"
    assumes distinct: "distinct xs"
    assumes sorter: "⋀R. linorder_on (set xs) R ⟹ is_sorting R xs (eval_sorter R sorter)"
    defines "Rs ≡ {R. linorder_on (set xs) R}"
    shows   two_power_count_queries_ge: "fact (length xs) ≤ (2 ^ count_wc_queries Rs sorter :: nat)"
      and   count_queries_ge:           "log 2 (fact (length xs)) ≤ real (count_wc_queries Rs sorter)"
  ```
  plus `card_range_eval_sorter` (`card (eval_sorter · ` Rs) ≤ 2 ^ count_wc_queries`)
  and `count_queries_bigomega : (λn. count_wc_queries (Rs n) (sorter n)) ∈ Ω(λn. n * ln n)`,
  derived from `asymp_equiv_ln_fact : (λn. ln (fact n)) ∼[at_top] (λn. n * ln n)`.

  Note: there is **no `sort` locale**; the model is the datatype above.  The
  worst case `count_wc_queries Rs sorter` is a maximum over the `n!` linear
  orders, i.e. already the *input-attained* form: leaves that no order reaches
  simply never contribute.  `WorstCase.lean` here proves the same (over the
  canonical inputs `xOfPerm p`) **and** the tree-depth form, which the AFP does
  not state.

* **Coq/Rocq (MathComp)**, Arthur Azevedo de Amorim, 2015-03-25,
  *Analyzing sorting algorithms* — <https://poleiro.info/posts/2015-03-25-analyzing-sorting-algorithms.html>
  (source `theories/Sorting.v` linked there):
  ```coq
  Inductive sort_alg (n : nat) :=
    Compare (i j : 'I_n) (l r : sort_alg n) | Done of 'S_n.
  Lemma card_perms : #|perms a| <= 2 ^ comparisons a.
  Lemma log2_fact : (n * log2 n)./2 <= log2 n`!.
  Lemma sort_alg_ok_leq n (a : sort_alg n) : sort_alg_ok a -> (n * log2 n)./2 <= comparisons a.
  ```
  Stirling-free route via `trunc_log`, giving exactly the `(n/2)·log₂ n` shape.

* **HOL4 / ACL2 / PVS / Mizar**: nothing found; *unverified absence*.

## Lean 4 prior art

* **Mathlib**: `Mathlib/Data/List/Sort.lean` has sorting *correctness* only
  (`orderedInsert`, `insertionSort`, `mergeSort`, `perm_mergeSort`,
  `pairwise_mergeSort`, stability).  No decision-tree model, no comparison
  counter, no `log₂(n!)` statement.
* **CLRS-Lean** (TankTechnology), Chapter 8 — <https://github.com/TankTechnology/CLRS-Lean>:
  `SortTree n`, `CorrectSort`,
  `height_le_logb_factorial : CorrectSort T → Real.logb 2 (n! : ℝ) ≤ T.height`,
  `comparisonSort_worstCase_lowerBound`, `factorial_sq_ge_pow_self :
  n^n ≤ (n!)^2`, and (Ch. 8.3) `radixSortNatByCost_bigO : ∃ c, ∀ base d n,
  radixSortNatByCost base d n ≤ c * (d * (n + base + 1))`.  Self-described
  AI-agent-built, with published audits listing semantic issues; treated here
  as prior art, not as authority.
* **girving/debate `Comp/Sort.lean`** — <https://github.com/girving/debate>:
  oracle-cost model with `Sorts.le_cost` (average case) and `Sorts.le_cost'`
  (worst case), plus `cost_mergeSort_le : … ≤ 3 * n * n.ceil_log2`.
  Unreviewed personal development.
* **tomaz1502/RunTimeFormalization** (Lean Zulip, 27 May 2022): operation
  counts for insertion/merge sort, *not* a lower bound; no merged Mathlib PR.

## Radix / counting sort

* **Isabelle/HOL** `HOL-ex/Radix_Sort` (Nipkow) —
  <https://isabelle.in.tum.de/library/HOL/HOL-ex/Radix_Sort.html>: locale
  `Radix_Sort` assuming `sorted (map f (sort1 f xss))`,
  `mset (sort1 f xss) = mset xss`, `stable_sort_key sort1`; `radix_sort`,
  `mset_radix_sort`, `sorted_radix_sort`.  Correctness only.
* **KeY**: de Gouw, de Boer, Rot, *Proof Pearl: The KeY to Correct and Stable
  Sorting*, J. Autom. Reasoning 53(2):129–139 (2014), doi:10.1007/s10817-013-9300-y;
  extended chapter on counting and radix sort in LNCS 10001 (2016).
* **CLRS-Lean** §8.2–8.3: `countingSortBy`, `radixSortBy`, `radixSortBy_perm`,
  `radixSortBy_stable`, cost bound above.

## Textbook statements

* **CLRS Theorem 8.1** (§8.1): "Any comparison sort algorithm requires
  `Ω(n lg n)` comparisons in the worst case."  Proof: `n! ≤ l ≤ 2^h` for a
  decision tree with `l` leaves and height `h`; "taking logarithms … `h ≥ lg(n!)`
  = `Ω(n lg n)` (by equation (3.18))".  **Corollary 8.2**: heapsort and
  mergesort are asymptotically optimal comparison sorts.  Exercise 8.1-2 asks
  for asymptotically tight bounds on `lg(n!)` without Stirling.
  (3rd-edition wording; 4th-edition numbering *unverified*.)
* **CLRS Problem 8-1**, "Probabilistic lower bounds on comparison sorting" —
  the standard textbook home for the expectation/average-case version
  (deterministic *or* randomized sorts, uniform random input).
* **Knuth, TAOCP vol. 3, §5.3.1 "Minimum-Comparison Sorting"**: `S(n)`,
  `⌈lg n!⌉` as the information-theoretic bound.  Section numbering and the
  average-case `Ā(n)` statement *unverified* (secondary sources only).
* The elementary bound `(n!)² ≥ nⁿ` (pair `k` with `n+1−k`) gives
  `lg(n!) ≥ (n/2)lg n`; no textbook sentence stating `n! ≥ (n/2)^(n/2)`
  verbatim was located — treat as folklore.

## What this repository adds

1. A small, dependency-light Lean 4 + Mathlib development (no Mathlib PR
   required) that derives both the *input-attained* worst case (`worstCase t`
   over the `n!` canonical inputs, so the depth/reachability gap cannot bite)
   **and** the tree-depth form from a single elementary counting argument, and
   transfers the bound to arbitrary value types via comparison-pattern
   invariance (`General.lean`).
2. The average-case bound (`avg_cost_ge_log2_factorial`) derived from the same
   `(1/2)^cost` weight lemma, in Lean, with the analytic step made explicit.
3. A counted merge sort with an explicit `O(n log n)` comparison bound
   (`UpperBound.lean`), i.e. the matching upper half of `Θ(n log n)`.
4. Radix/counting sort in the same repository as the lower bound: correctness,
   stability, comparison-freeness as a *theorem*, and the `d·(n+b)` ledger — so
   the "why doesn't radix sort contradict `Ω(n log n)`?" question is answered
   by the code rather than by prose.
