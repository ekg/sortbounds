# PROGRESS

Single source of truth for status. Only the integrator edits this file; lanes
update the `## Log` of their own `README.md`.

Status values: `DONE` · `ACTIVE` · `QUEUED` · `BLOCKED` · `SHELVED` (with reason).

## Where we are

The comparison-model result is **settled and frozen**: `Ω(n log n)` for the worst
case over inputs, the average case, arbitrary value types, plus a matching
`O(n log n)` upper bound. Frozen means: no more work on restating it, no constant
chasing. It is the worked example for `SortBounds/Core`.

The question now is not "is the bound true" but **"what does the bound say about
other models"** — every open lane is about a model where the answer changes.

## Lanes

| Lane | Question | Target theorem | Status | Milestone |
| --- | --- | --- | --- | --- |
| `Core` | bits per probe | `card_le_pow_of_prefixFree`, `logb_le_of_le_pow`, **`mean_cost_ge_logb`** (Kraft + Gibbs, any `b`) | **DONE** | frame complete |
| `Comparison` | comparison sorts | `exists_input_cost_ge_quarter`, `avg_cost_ge_log2_factorial` | **DONE** | frozen |
| `Instances` | where the bound breaks | `radixSort_keys_congr`, `msortCount_le`, `factorial_le_two_pow_length_of_sortsAll`, `sortsAll_of_sorts_zeroOne` | **DONE** | frozen |
| `FordJohnson` | exact comparison counts, upper bound | `fjCountJ_table` (`F(4..11) = 5,7,10,13,16,19,22,26`), `fjCountJ_eq_sum`, **`fjCountJ_attains`** (the count is *attained*) | **M2/M3/M4 DONE** | list→`Tree` transfer (lane `FjTree`) |
| `SN` | exact `S(n)`, explicit trees | `S 0..7` (**`S 4=5, S 5=7, S 6=10, S 7=13`**), each in both readings | **M2 for n ≤ 7** | `S 12 = 30` open |
| `XY` | sorting `X+Y` | `pairSums`, `pairSums_card_le`, `naivePairsSorted_*` | **M1 DONE** | M2 gated |
| `BenOr` | algebraic decision trees | model, `exists_decidesReal_distinct`, **`numComponents_distinctSet` (`= n!`)** | **M1 DONE** | Milnor–Thom step (components ⇒ height) |
| `FjTree` | FJA's decision tree | **`S_eq_clog`**: `S n = ⌈log₂ n!⌉` for `4 ≤ n ≤ 11`, `S_eq_clog_large` for `20, 21` | **DONE** | — |
| `SortTree` | `Θ` inside one model | **`S_sandwich`**: `⌈log₂ n!⌉ ≤ S n ≤ n(⌈log₂ n⌉+1)` | **DONE** | — |
| `SAIS` | suffix arrays, cost model | `kasai_cost_le` (`≤ 2n`, build the LCP array), `checkOn_computed_cost` (`n − 1`, verify against the *computed* array) | `inf'_lcpAt_le_lcp` (text-order skip), `lcp_suffix_eq_inf'_of_increasing` (the real min property, along a sorted chain), `verify_linear_time` (`n-1` inspections to verify a suffix array) | **M1 DONE** | sorting in `O(n log n)` inspections not formalised |

## Decisions (and why)

1. **Freeze the lower bound.** It is done three times over elsewhere; more
   restatements add nothing. See `docs/PRIOR-ART.md`.
2. **One project, directories per lane.** Mathlib oleans are 7.6 GB; per-lane
   Lake packages would duplicate that. Details in `docs/STRUCTURE.md`.
3. **`Core` first, instances second.** The reusable object is the
   branching-factor counting lemma, not the Ω statement.
4. **Prior art checked before each lane starts.** Two earlier ideas died this
   way: the 0-1 principle + verified sorting networks (Coq: arXiv 2203.01579,
   1502.05209, 2012.04400; Lean: girving/aks formalises AKS), and verified SA-IS
   correctness (Isabelle AFP `SuffixArray`, 2024). Only the *cost model* for
   suffix arrays is unclaimed.
5. **Lanes are allowed to end at M1.** Reaching a weaker true theorem is a
   success; a `sorry` is not.

## Milestone vocabulary

* `M0` — definitions and the target statement compiles (possibly with the easy
  direction only). No `sorry`.
* `M1` — the main theorem proved for the small/central case.
* `M2` — the general theorem.
* `M3` — the result that would be new to the literature (gated; may not land).

## What each lane actually landed (verified, not claimed)

* **FordJohnson** — `insertCount` (binary insertion, `≤ ⌈log₂(k+1)⌉` comparisons),
  `fjSort` (merge-insertion) with `fjSort_perm`, `fjSort_sorted`,
  `fjSort_count_le : (fjSort l).1 ≤ fjCount l.length`. Round 2 added M2/M3:
  `fjCount_le : fjCount n ≤ n·(⌈log₂ n⌉+1)`, then the real thing —
  `fjSortJ` (losers inserted in JACOBSTHAL order into a growing sorted prefix,
  `Jacobsthal.lean`), `fjSortJ_count_le : (fjSortJ l).1 ≤ fjCountJ l.length`,
  the closed form `fjCountJ_eq_sum : fjCountJ n = Σ_{k<n} ⌈log₂((3(k+1)+3)/4)⌉`
  for `n ≤ 22`, and `fjCountJ_table : fjCountJ 4..11 = 5,7,10,13,16,19,22,26` —
  the information-theoretic value `⌈log₂ n!⌉` in each case. Smoke test:
  `fjSortJ [5,3,1,4,2]` costs 7.  Round 4 added **attainment**: `fjCountJ_attains`
  (an explicit input family makes *every* search in a batch cost its full
  `⌈log₂(jacLo + jacHi)⌉`), so `fjCountJ` is the exact worst case of the idealised
  algorithm, not merely an upper bound.  **Still not claimed:** `S n ≤ fjCountJ n`
  (needs the list→`Tree` transfer — lane `FjTree`).  The lane's comparison model is
  an *idealisation*: `sortPairs`/`splitBelow`/`countP` inspect values without being
  charged, which is faithful to the real algorithm (where that bookkeeping is
  threaded, not recomputed) and is now stated at `JacobsthalInsertion.lean`.
  **Caveat (documented in the lane):** two bookkeeping steps are uncharged (the
  winner/loser reordering and locating the window), so the count is for an
  idealised implementation; charging them needs an adversary argument.
  *Attainment* of the bound by one input is also still open.
* **SN** — `exists_correct_tree` (a compare-all-pairs tree, depth `n²`),
  `S`, `S_spec`, `S_le_iff`, `S_lower` (`⌈log₂ n!⌉ ≤ S n`), and
  `S 0 = 0, S 1 = 0, S 2 = 1, S 3 = 3`, and now **`S 4 = 5`, `S 5 = 7`**
  (`Four.lean`, `Five.lean`: upper bounds from explicit 5- and 7-comparison
  trees, lower bounds from `S_lower` since `⌈log₂ 4!⌉ = 5`, `⌈log₂ 5!⌉ = 7`).
  So `S(n) = ⌈log₂ n!⌉` is machine-checked for `n ≤ 7` (**`S 6 = 10`, `S 7 = 13`**
  added with kernel-checked 720- and 5040-leaf trees from the committed generator
  `search_optimal_tree.py`), **in both readings**:
  `four_needs_five_comparisons` / `five_needs_seven_comparisons` rule out any tree
  whose every input costs `≤ 4` resp. `≤ 6`, so "fewest comparisons that suffice"
  (least worst-case *cost*) is also 5 / 7, not just the least *depth*. `S_eq_clog` (n ≤ 11) and
  `S 12 = 30` are **not** proved; the contract marks them as targets.
* **XY** — `pairSums`, `pairSums_card_le`, `naivePairsSorted_*`, and the counted
  merge-sort run `naivePairsMsort_count`. Review caught a false claim in the
  prose (`Ω(n² log n)` for the sums problem); fixed — the M0 theorem is the
  generic `N`-item bound re-indexed, and Fredman's `O(n²)` scheme is exactly why
  it does not apply to sums.
* **BenOr** — `ADT`, `height`, `numCells`, `run`, `decides`, `degreeLe`,
  `ADT.card_cells_le`, the *statements* `BenOrBound`,
  `ElementDistinctHeightBound`, `elementDistinctComponents`, **and now the
  non-vacuity witnesses**: `exists_decidesReal_distinct` (a tree of degree
  `n(n-1)` deciding element distinctness via `-(∏ᵢ<ⱼ (xᵢ-xⱼ)²)`, so
  `decidesReal (distinctSet n)` is satisfiable) and `halfLineTree_decidesReal`
  for the real semantics. The vacuity risk flagged by review is closed.
* **SAIS** — M0 landed (`LCP.lean`, 657 lines): `suffix`, `lcp`, `cmpCounted`
  with `cmpCounted_snd = lcp + 1`, `cmpFrom` (comparison that starts after a
  supplied LCP bound) with `suffix_compare_eq_of_lcp` and `cmpFrom_lcp_advance`
  (soundness of the skip), the per-comparison inspection count, and the exact
  `aⁿ` contrast: `naiveInspectSum = n(n-1)(n+4)/6` vs
  `guidedInspectSum = n(n-1)/2`, i.e. `3·naive = (n+4)·guided`. Review caught
  three prose errors (labelled quadratic/linear when it is cubic/quadratic,
  "characters" where the model charges *positions*, an off-by-one in `j = n+1`),
  all fixed.

## SAIS, complete (M0–M2)

`≤ 2n` character comparisons to build the LCP array (Kasai) and `n − 1` inspections to
verify a candidate against *that computed array* — versus `Θ(n²)` naive.  **The two are
not added into a single `3n`**: `pairScan` charges 0 for a scan that runs off the end
while `inspectCount` charges 1, so they are counters in different conventions; the unified
figure would be `≤ 4n − 1` and is not formalised (review finding, recorded rather than
papered over).  What is
*not* formalised: producing the candidate suffix array itself — SA-IS/DC3 sort integer
ranks with radix/counting sort, i.e. they take the door `Instances.Radix` describes.
The evidence chain: `kasai_lcp_correct` (the array is right, given `Verified s sa`),
`compare_lt_iff_saRank_lt` (a verified candidate *is* the suffix array),
`checkSaCounted_cost` (the `n − 1` is an executable's counter).

## Blockers and dependencies

* `SN` M2 (optimal trees for `n = 6..11`) **depends on** `FordJohnson` M1: the
  merge-insertion algorithm is the cheapest way to *construct* the optimal trees.
  Until then `SN` works on `M0`/`M1` (which are independent).
* `SN` M3 (`S 12 = 30`, the first case where `⌈log₂ 12!⌉ = 29 < 30`) needs a
  genuine adversary/entropy argument, not just counting. Research-level.
* `XY` M2+ (Fredman's `O(n²)` comparison algorithm) is research-level.
* `BenOr` M1+ (component count of the distinctness set) needs real algebraic
  geometry; `M0` only is the committed deliverable.
* `SAIS` is queued behind `XY`, which will exercise the same weighted cost model.

## Queue (take the next item without asking)

### Landed (do not redo)

`Core` (bits per probe, worst + average, any `b`) · `Comparison` (Ω(n log n):
worst, average, any value type, randomised) · `SortTree` (`Θ` inside one model) ·
`FordJohnson` (count, closed form, attainment) · `FjTree` (`S n = ⌈log₂ n!⌉` for
`4..11`, `20`, `21`; `S_pin` for `n ≤ 22`; depth = count exactly) · `SN` (`S 4..7`
by explicit kernel-checked trees) · `Instances` (radix; networks + comparator
bound + 0-1 principle + network→tree; merge sort) · `SAIS` (LCP cost model;
Kasai `≤ 2n`; verify `n − 1` on computed data) · `BenOr` (model + statement +
non-vacuity witnesses).

### Open — ordered by what is actually reachable

1. ~~**Domain / word-RAM model**~~ **DONE** (`Projects/Domain`): `passes_lower`
   (`2 ≤ b → p < d → ¬∃ P, SortsAllKeys P`), `probes_tight` (`d` probes are necessary
   *and* sufficient), `wordram_probes` (`w`-bit words: `n` reads necessary and
   sufficient for `n` digits), and the contrast `radix_cost_le_comparison_cost`: the bound becomes
   `log_b U` instead of `log₂ n!`, and radix attains it exactly — the quantitative
   answer to "does structure buy speed, or is `n log n` inescapable?".
   `log_b U` probes are necessary and `⌈log_b U⌉` suffice, so for `U = n^{O(1)}` and
   `b = n` integer sorting needs `O(1)` passes versus `Ω(n log n)` comparisons.  The
   model's one loophole — encoding the key in *which* digit is read — is closed by the
   `hfiber` hypothesis on values only; review is auditing exactly that.
2. ~~**`BenOr` M1**~~ **DONE**: `numComponents_distinctSet : Nat.card (ConnectedComponents
   ↥(distinctSet n)) = n!`, with an explicit `componentsEquivPerm : ConnectedComponents
   ↥(distinctSet n) ≃ Equiv.Perm (Fin n)`.  **No algebraic geometry needed**: the
   distinctness set is a disjoint union of `n!` open convex *sectors* (one per ordering),
   so in the subspace each sector is clopen (complement = the other open sectors) and
   connected (continuous image of a convex set), hence exactly one component.
   `benOrBound_benOrDistinctness` now supplies the component count that Ben-Or's bound
   consumes.  What remains for the bound itself is the Milnor–Thom step (components ⇒
   height), which is still a `Prop` statement, not a proof.
3. **`XY` M2**: Fredman's `O(n²)` comparison scheme for `X+Y` (statement first, with
   citation; the algorithm is a research paper).
4. **`SAIS`**: the `P2` from review — `saRank` is `O(n)` per lookup, so `kasai` is
   quadratic in *list scans* though linear in *character inspections*; a cost model
   that charges indexed access would be more faithful.
5. **`S 12 = 30`**: open, and **not reachable by counting** (`12! < 2^29`, Kraft
   realizes any `L ≤ 2^d`).  Needs a pruned search (Wells 1971, Peczarski 2004).
6. **`SortTree`'s constant**: `n(⌈log₂ n⌉+1)` vs `⌈log₂ n!⌉` — the gap is a constant;
   only worth doing if someone needs the constant.

## Changelog

| Date | Change |
| --- | --- |
| 2026-11-11 | **`S n = ⌈log₂ n!⌉` proved for `4 ≤ n ≤ 11` and `n = 20, 21`** (`FjTree.S_eq_clog`): merge-insertion verified optimal. `fjTree_correct` found two real bugs in the tree that `fjTree_depth_le` could not see. |
| 2026-11-11 | Round 4: `S 6 = 10`, `S 7 = 13` (kernel-checked 720/5040-leaf trees), `fjCountJ_attains` (the FJA count is attained), `FjTree` depth accounting (`depth (fjTree n) ≤ fjCountJ n`), `S_le_of_forall_cost_le` (fewest-comparisons reading = least depth, generally). |
| 2026-11-11 | Core completed: average case for any branching factor (`mean_cost_ge_logb`), and `prune`/`exists_depth_le_of_cost_le` showing depth = worst-case cost at the optimum. FJA-tree queued behind SortTree. |
| 2026-11-11 | Round-2 reviews applied: FordJohnson prose no longer claims `S n = fjCountJ n` or attainment; Ford–Johnson added to PRIOR-ART; SN/SAIS/BenOr doc drifts fixed. |
| 2026-11-11 | FordJohnson M2/M3: verified Jacobsthal-order merge-insertion with the literature closed form and the optimal table `F(4..11)`. |
| 2026-11-11 | 0-1 principle in Lean: thresholding commutes with comparators (`map_netRun`), so a network sorting all `Fin n → Fin 2` inputs sorts everything; concrete networks verified by `decide`. |
| 2026-11-11 | SN M2 for small n: `S 4 = 5`, `S 5 = 7` (integrated; the lane's two files needed an import fix). |
| 2026-11-11 | Round-2 partial integration: BenOr witnesses (vacuity closed), SAIS cost model M0 (cubic-vs-quadratic `aⁿ` contrast), review prose fixes. |
| 2026-11-11 | `Instances.Network`: sorting networks cannot beat the bound in comparator count (`n! ≤ 2^k`), only in depth. Round-2 lanes launched with 4h deadlines (BenOr witness, FordJohnson count, SN `S 4`/`S 5`, SAIS cost model). |
| 2026-11-11 | Lanes ran: FordJohnson/SN/XY to M1, BenOr to M0. Review caught one false prose claim (XY) and one vacuity gap (BenOr); both recorded. |
| 2026-11-09 | Repo restructured (`Core`/`Comparison`/`Instances`/`Projects`); `Core.Branching` landed; four lanes opened. |
| 2026-11-09 | Initial development: comparison model, Ω(n log n) (worst/average/any value type), radix, counted merge sort. |
