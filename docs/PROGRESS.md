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
| `Core` | bits per probe | `card_le_pow_of_prefixFree`, `logb_le_of_le_pow` | **DONE** | M0 |
| `Comparison` | comparison sorts | `exists_input_cost_ge_quarter`, `avg_cost_ge_log2_factorial` | **DONE** | frozen |
| `Instances` | where the bound breaks | `radixSort_keys_congr`, `msortCount_le`, `factorial_le_two_pow_length_of_sortsAll`, `sortsAll_of_sorts_zeroOne` | **DONE** | frozen |
| `FordJohnson` | exact comparison counts, upper bound | `fjCount_le`, **`fjSortJ_count_le`**, **`fjCountJ_table`** (`F(4..11) = 5,7,10,13,16,19,22,26`), `fjCountJ_eq_sum` | **M2/M3 DONE** | attainment open |
| `SN` | exact `S(n)`, both bounds | `S 0..3`, **`S 4 = 5`, `S 5 = 7`** | **M2 for n ≤ 5** | n ≥ 6 open |
| `XY` | sorting `X+Y` | `pairSums`, `pairSums_card_le`, `naivePairsSorted_*` | **M1 DONE** | M2 gated |
| `BenOr` | algebraic decision trees | `ADT`, `decides`, `ADT.card_cells_le`, `BenOrBound` (statement), `exists_decidesReal_distinct` | **M0 DONE** (semantics now witnessed) | M1+ gated |
| `SAIS` | suffix arrays, cost model | `cmpFrom` soundness, `inspectCount_replicate`, `three_mul_naiveInspectSum` (cubic vs quadratic) | **M0 DONE** | M1 needs LCP-array construction |

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
  `fjSortJ [5,3,1,4,2]` costs 7. **Not claimed:** `fjCountJ n = S n` (needs a
  list→`Tree` transfer; `Comparison/Bridge` has the mechanism) and *attainment*
  (some input actually costing `fjCountJ n`). Review caught prose that claimed
  both; fixed in `Jacobsthal.lean`/`JacobsthalInsertion.lean`/the lane README.
  **Caveat (documented in the lane):** two bookkeeping steps are uncharged (the
  winner/loser reordering and locating the window), so the count is for an
  idealised implementation; charging them needs an adversary argument.
  *Attainment* of the bound by one input is also still open.
* **SN** — `exists_correct_tree` (a compare-all-pairs tree, depth `n²`),
  `S`, `S_spec`, `S_le_iff`, `S_lower` (`⌈log₂ n!⌉ ≤ S n`), and
  `S 0 = 0, S 1 = 0, S 2 = 1, S 3 = 3`, and now **`S 4 = 5`, `S 5 = 7`**
  (`Four.lean`, `Five.lean`: upper bounds from explicit 5- and 7-comparison
  trees, lower bounds from `S_lower` since `⌈log₂ 4!⌉ = 5`, `⌈log₂ 5!⌉ = 7`).
  So `S(n) = ⌈log₂ n!⌉` is machine-checked for `n ≤ 5`, **in both readings**:
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

1. `BenOr` witness: `∃ t, t.degreeLe (n*(n-1)) ∧ t.decidesReal (distinctSet n)` — removes the
   vacuity risk on the unproved Ben-Or statements. *Running.*
2. `FordJohnson` M2/M3: `fjCount n ≤ n·(⌈log₂ n⌉+1)` for the existing recurrence, then the real
   Jacobsthal-order count with the table `F(4..11) = 5,7,10,13,16,19,22,26`. *Running.*
3. `SN` M2: `S 4 = 5`, `S 5 = 7` by explicit optimal trees. *Running.*
4. `SAIS` M0: `cmpFrom` soundness under a known LCP, plus the quadratic-vs-linear character
   contrast on `aⁿ`. *Running.*
5. ~~`Core` leads with Mathlib~~ **DONE**: `card_le_pow_of_prefixFree` is now a
   corollary of Mathlib's Kraft inequality
   (`InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`),
   not a re-proof: `Core/Branching.lean` dropped from ~110 lines of bespoke
   padding combinatorics to 76 lines of instantiation. Recorded in PRIOR-ART.
6. ~~`Instances.Network`~~ **DONE**: `factorial_le_two_pow_length_of_sortsAll`
   (`n! ≤ 2 ^ #comparators` for any sorting network) and
   `logb_factorial_le_length_of_sortsAll`. A network is a comparison algorithm with depth =
   comparator count, so networks win on depth (AKS: `O(log n)`), never on work.
6b. ~~0-1 principle~~ **DONE**: `sortsAll_of_sorts_zeroOne` (hypothesis over `Fin n → Fin 2`,
   hence **decidable**), `factorial_le_two_pow_length_of_sorts_zeroOne`, and
   `sorts_zeroOne_three_wire` verified by `decide` over 8 inputs. Concrete networks are now
   checkable without enumerating `n!` permutations.
7. `Comparison/Bridge` M1: `insertTree (σ) : Tree (n+1)` — binary search for the rank of
   `x n` among the prefix order `σ`, leaves `insertPerm σ j` (`Fin.succAbove`/`decomposeFin'`
   territory), then `sortTree n` by iterating `liftTree`, giving `S n ≤ n·(⌈log₂ n⌉+1)` and
   hence `Θ(n log n)` **inside one model**. M0 (substitution, depth, correctness transfer) landed.
8. `XY` M2, `BenOr` M1+: research gates, only with a concrete plan.

Working agreement: see `AGENTS.md` (autonomy, 4h lane deadlines, background fan-out,
truth discipline).

## Changelog

| Date | Change |
| --- | --- |
| 2026-11-11 | Round-2 reviews applied: FordJohnson prose no longer claims `S n = fjCountJ n` or attainment; Ford–Johnson added to PRIOR-ART; SN/SAIS/BenOr doc drifts fixed. |
| 2026-11-11 | FordJohnson M2/M3: verified Jacobsthal-order merge-insertion with the literature closed form and the optimal table `F(4..11)`. |
| 2026-11-11 | 0-1 principle in Lean: thresholding commutes with comparators (`map_netRun`), so a network sorting all `Fin n → Fin 2` inputs sorts everything; concrete networks verified by `decide`. |
| 2026-11-11 | SN M2 for small n: `S 4 = 5`, `S 5 = 7` (integrated; the lane's two files needed an import fix). |
| 2026-11-11 | Round-2 partial integration: BenOr witnesses (vacuity closed), SAIS cost model M0 (cubic-vs-quadratic `aⁿ` contrast), review prose fixes. |
| 2026-11-11 | `Instances.Network`: sorting networks cannot beat the bound in comparator count (`n! ≤ 2^k`), only in depth. Round-2 lanes launched with 4h deadlines (BenOr witness, FordJohnson count, SN `S 4`/`S 5`, SAIS cost model). |
| 2026-11-11 | Lanes ran: FordJohnson/SN/XY to M1, BenOr to M0. Review caught one false prose claim (XY) and one vacuity gap (BenOr); both recorded. |
| 2026-11-09 | Repo restructured (`Core`/`Comparison`/`Instances`/`Projects`); `Core.Branching` landed; four lanes opened. |
| 2026-11-09 | Initial development: comparison model, Ω(n log n) (worst/average/any value type), radix, counted merge sort. |
