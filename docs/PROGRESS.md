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
| `Algorithms` | executable measures, SA/BWT/`r` | `deltaCompute_eq`, `suffixArray_perm`/`_sorted`, `measure_spec` | **DONE** | SA-IS (fast SA), LZ/grammar measures |
| `Repetitiveness` | string attractors; certification | `delta_le_gamma`, `checkAttractor_eq_true_iff`, `greedyAttractor_isAttractor`, `delta_le_greedyAttractor_card` | **DONE** (formalizes known facts; no literature-novel claim) | characterisation `γ = δ` refuted (KNP III.3) | `distinctFactors_card_le_mul_attractor` (KNP Lem. II.4), `substringComplexity_le_minAttractorSize` (`δ ≤ γ`), `…_le_slp` (`δ ≤ g`) | **M0/M1 DONE** | characterization `γ = δ` **refuted** (KNP Thm III.3: `δ ≤ 2`, `γ ≥ ½log n`) |
| `BestCase` | best case | **`pred_le_cost`** (`n − 1` on every input), `exists_correct_cost_id_eq'` (attained) | **DONE** | — |
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
* `BenOr` M2 (components ⇒ height, the Milnor–Thom step) is the only open input in
  that lane; the component count itself is **done** (`numComponents_distinctSet`,
  and it needed no algebraic geometry — open convex sectors).
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

### Closed: `BestCase` — the third corner of `Θ`

`pred_le_cost : n − 1 ≤ cost t x` for **every** injective `x` (not just the sorted one),
plus `exists_correct_cost_id_eq' : ∃ t, Correct t ∧ cost t (fun i : Fin n => i) = n − 1` —
so over inputs with distinct values the best case is *exactly* `n − 1`.  `pred_le_cost_of_orderEmb`
gives the same bound for any value type.  With `Ω(n log n)` for the optimal worst case and `≥ log₂ n!` for the
average over random orderings, the `Θ` picture is complete in one model.
Machinery: `comparedPairs`/`comparisonGraph` along a path, `run_eq_of_agree` (same answers
on the pairs *made* ⟹ same leaf), `run_eq_of_add_const` (pushing a block of values above
the rest changes no made comparison), `preconnected_comparisonGraph`, and the edge count
`n − 1 ≤ #pairs ≤ cost`.

### Open — ordered by what is actually reachable

1. ~~**Domain / word-RAM model**~~ **DONE** (`Projects/Domain`): `passes_lower`
   (`2 ≤ b → p < d → ¬∃ P, SortsAllKeys P`), `probes_tight` (`d` probes are necessary
   *and* sufficient), `wordram_probes` (`w`-bit words: `n` reads necessary and
   sufficient for `n` digits), and the contrast `radix_cost_le_comparison_cost`: the bound becomes
   `log_b U` instead of `log₂ n!`, and radix attains it exactly — the quantitative
   answer to "does structure buy speed, or is `n log n` inescapable?".
   **Scope, stated precisely** (review finding): for a *per-key digest plan*
   (`KeyProc`: `p` digit reads per key, each position chosen from the values already
   read, digest a function of those values), `2 ≤ b` and `p < d` ⇒ no plan separates the
   `b^d` keys; `radixProc` attains `d = log_b U`.  So in the probe currency `U = b^d`,
   `b = n` costs `O(1)` reads per key against `Ω(n log n)` comparisons
   (`exists_input_cost_ge_quarter`).  Radix's *list* cost is the separate definition
   `radixCost d n b = d·(n+b)`, not an operation count extracted from `radixSort`.
   The loophole — encoding the key in *which* digit is read — is closed by the type of
   `next` (it can only consult observed values), and `card_le_pow_probes`'s fibre
   hypothesis is *proved* from digest injectivity (`Lower.lean:108`).  **Not covered:**
   a general *list* algorithm (sorting by integer `O(1)`-time reads over an array) —
   that is the follow-up, with `exists_obs_eq_of_lt` as the adversary skeleton.
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

## Attractor programme (opened 2026-11-13)

The measure worth optimising is `γ` (smallest attractor), not `r`: an attractor of size `c`
yields an RLSLP of size `O(c log(n/c))`, so a better attractor is a smaller grammar.
`γ` is NP-hard, so the interface is a certified bracket, never an answer.

| lane | what | state |
| --- | --- | --- |
| `tools/attractor` | any-time search: greedy → irredundant prune → swaps → iterative deepening, with `δ` and a packing bound as certified lower bounds | running |
| `tools/approx` + `docs/research/attractor-approx.md` | **guaranteed** bounds: `δ ≤ γ ≤ z ≤ 4(δ log(n/δ)+δ)` gives an `O(log n)` approximation *constructively* (LZ77 → attractor), plus the structural theory (interval structure for fixed `k`, LP gap, `σ = 2` hardness) | running |

**First results (anytime lane, verified by re-running the tool):** the bracket *closes* on
every highly repetitive instance tried — `mississippi` `[4,4]`, `abracadabra` `[5,5]`,
Thue–Morse `2⁸`/`2¹⁰` `[4,4]`, Fibonacci `F₁₄`/`F₁₈` `[2,2]` (packing witnesses re-checked
from the text each time) — and stays open on incompressible text (`n = 2048`:
`[165,179]`).  Two distinct mechanisms close it: on Thue–Morse it is `⌈δ⌉ = 4 = γ`
(`δ ≈ 3.32`, `γ` an integer); on random text `δ` alone is far too weak (`δ ≈ 140.31` at
`n = 2048`) and the *packing* bound carries the floor (`γ ≥ 165`).  So the second lower
bound is not redundant — it is what makes the bracket usable where `δ` is loose.

*(Correction: an earlier commit message of mine claimed the packing bound exceeded `δ` on
Thue–Morse. It does not — there `δ > packing` and it is `⌈δ⌉` that closes the bracket. The
packing bound wins on *incompressible* text, which is the opposite regime. The lane's
README had it right; I misread the table.)*

The open theoretical question, stated sharply: `γ/δ = Θ(log(n/δ))` is achievable
(KNP23 Thm III.3) — *not* the `Θ(log n log log n)` figure, which is `r/δ` (KK Thm 4.3) —
so any algorithm whose lower bound is only `δ` cannot beat a `log n` factor — is `O(log n)`
inherent for `γ`, or does the interval structure admit a constant-factor (or exact on
restricted families) algorithm?  A failed constant-factor attempt is as informative as a
success here, which is why the note is required to state falsifiable conjectures.

## Three questions (opened 2026-11-13) — `workflows/three-questions.js`

Whether a *guaranteed* small-attractor algorithm exists reduces to three questions, each now
a swarmed lane with its own independent review:

### A theorem: `γ/γ₂` is unbounded (2026-11-13)

| `γ(B_k) ≥ 2^k/k` and `γ₂(B_k) ≤ 4` | for binary de Bruijn words `B_k`; hence `γ/γ₂ ≥ 2^k/(4k) → ∞` |
| --- | --- |
| proof | `d_i = 2^i` (`i ≤ k`, pad to a `k`-gram) ⇒ `δ = 2^k/k` (`2^i/i` nondecreasing) ⇒ `δ ≤ γ`; and 4 positions cover the four 2-grams |
| machine-checked | `SortBounds.Projects.DeBruijn.gamma_ge_of_isDeBruijn`, `deltaQ_isDeBruijn`, `card_distinctFactors_of_coversAllWords`, plus `decide` witnesses at `k = 2, 3`; `deltaQ_le_minAttractorSize` supplies `δ ≤ γ` for the minimum |
| exact confirmation | `γ₂(B_k) = 2` for every `k ≤ 7` (so the ratio is `≥ 2^{k-1}/k`); `δ(B_k) = 2^k/k` to `k = 13` |
| strengthened | **every fixed `k` fails**: `γ_k(B_m) ≤ 2^k` so `γ/γ_k ≥ 2^m/(m·2^k) → ∞`; machine-checked as `gamma_ratio_ge_isDeBruijn` over a real `γ_k` (`IsAttractorK`, `minAttractorKSize`, with `isAttractorK_self_iff` pinning `γ_n = γ`) |
| kills | "compute `γ₂` (polynomial at `σ = 2`) and you are within a constant of `γ`" — the best structural route in `sigma2-algorithm.md`; the stronger corollary kills **all** bounded-length relaxations, and explains that lane's measured `k* ≈ n/2` |

`docs/research/gamma-vs-gamma2.md`.

### A theorem: the attractor LP is not integral (2026-11-13)

| `γ(LP₁₃) = 3`, `LP* = 11/5`, `γ/LP* = 15/11` | `s = 0110101101110`, kernel-checked |
| --- | --- |
| `SortBounds/Projects/AttractorLP/Gap.lean` | `coverageSet`, `factorUniverse`, `PrimalFeasible`, `DualFeasible`, `weak_duality` (elementary, no LP theory) |
| `SortBounds/Projects/AttractorLP/Witness.lean` | `lp13_gamma`, `lp13_primal`, `lp13_dual`, `lp13_gap` |
| why it matters | the LP route to an approximate `γ` is *not* an integrality argument: the relaxation genuinely falls below the integer optimum, so any `O(1)`-ratio algorithm must round, and the rounding question is now the only question |
| what is *not* claimed | that `15/11` is the supremum (that is the computation to `n ≤ 16`), nor that the gap is bounded |

### The LP gap is not `15/11`: `7/5` at `n = 31` (2026-11-13)

Searched to `n = 40` (beam over extensions of the `n = 13` witnesses, plus structured families),
every record re-verified independently with exact rationals:

| n | γ | LP* | gap | δ |
| --- | --- | --- | --- | --- |
| 21, 27 | 3 | 13/6 | 18/13 = 1.3846 | 2 |
| 30 | 5 | 18/5 | 25/18 = 1.3889 | 3 |
| 31 | 5 | 25/7 | **7/5 = 1.4** | 3 |

So `15/11` is the exhaustive maximum only for `n ≤ 16`; it is refuted as a maximum over all
lengths.  `γ/LP* ≤ γ/δ` always (since `LP* ≥ δ`), so the LP gap can only grow by growing the
`δ`-gap — and every measurement has `γ − ⌈δ⌉ ≤ 3`, which would force the LP gap `→ 1` at scale.
Exhaustive `n = 17` was **not** completed.  `docs/research/lp-gap-growth.md`.

### `LP* ≥ δ`, machine-checked (2026-11-13)

`AttractorLP/DeltaBound.lean`: `deltaQ_le_primalValue` — every primal-feasible fractional cover
of the attractor LP has value at least `δ` (weighted counting: `d_j ≤ j · Σ x`, then `sup'`).
Corollary `gamma_div_primal_le`: `γ/Σx ≤ γ/δ`.  So the LP gap **cannot exceed** the `δ`-gap; with
`γ − ⌈δ⌉ ≤ 3` in every measurement, the LP gap is forced toward `1` at scale.  `make trust`:
141 theorems.

### Answers (2026-11-13)

| lane | verdict |
| --- | --- |
| **A** | **OPEN, and now constrained.** No source proves `σ = 2` hardness and none gives an algorithm; three explicit binary reductions are **refuted** (an inversion `τ=1 → γ=5` vs `τ=2 → γ=3` at the same `n`, `|T|`), and a **proved necessary condition** survives: any threshold candidate must have `γ(T_G)` depend only on the *isomorphism class* of `G`. Neighbour note: SGP is NP-complete for fixed alphabets `σ ≥ 17` (Casel et al. 2021) and *open at `σ = 2`* — with one **UNVERIFIED** 2026 preprint (arXiv:2610.32298v2, Thm 1.4) claiming binary SGP hardness; `γ ≤ g` does **not** transfer that to `γ`. |
| **B** | **The LP gap is small, not `log n`**: max `γ/LP* = 15/11` at `n = 13`, exhaustive to `n ≤ 16`, 89–92 % of instances exactly integral, Fibonacci integral at every length to 987. No log-growth family found. But a small gap is **not** an algorithm: a constructive rounding rule is missing. |
| **C** | **`γ = ⌈δ⌉` is family-specific, not general.** Proved for Thue–Morse `n ≥ 6` (and fails at `n = 4,5`, and at TM prefixes 25–59); `γ = δ` proved for unary/Sturmian/Fibonacci only because `δ = d₁ = σ`. Measured over 117 texts in 13 families: `γ = ⌈δ⌉` on 69 rows, `>` on 32, 16 undecided — with `γ` printed **only** where the certified bracket is closed. `γ` is not a function of the `d`-profile (41/123 classes split). |

The three questions converge on one conclusion: **no cheap structural route to `γ` survives**; the
two live research directions are a real `σ = 2` reduction (with the isomorphism-class filter as a
screening test) and an `O(1)`-gap LP rounding rule.

| lane | question | why it decides something |
| --- | --- | --- |
| **A** (2 researchers) | Is minimum-attractor NP-hard on a **binary** alphabet? | every published reduction uses a *growing* alphabet; `σ = 2` is where corpora live. If binary is not hard, exact-on-binary is not fantasy; if it is, say which gadgets make it so |
| **B** (implementer) | What is the **LP integrality gap** of the attractor cover? | if `O(1)`, a constant-factor approximation is within reach; if `Θ(log n)`, LP-based methods are stuck at the log factor. Nobody has measured it — requires an exact rational simplex, plus the *fixed-`k`* gap where consecutive-ones structure should force gap 1 |
| **C** (theorist + experimenter) | When is `γ = ⌈δ⌉`? | the anytime search found *closed* brackets on every repetitive family tried. If that pattern is structural, `γ` is computable in `O(n)` exactly where it matters; if not, the gap's growth rate is the quantity to know |

**Lane A, hard mode** (`workflows/sigma2-hard.js`, running): since `σ = 2` is *open* — no source
proves hardness, none gives an algorithm — treat it as a research problem rather than a
footnote. Three angles in parallel: (a) **build and exhaustively test** a reduction from a known
NP-hard problem to a binary string, with the equivalence claim checked on every small source
instance (a hand-built gadget is not credible otherwise); (b) the opposite bet — hunt for
structure that makes binary instances tractable, by computing exact `γ` for binary strings
together with `δ`, the `d_k` profile, `γ_1`, `γ_2`, run structure, period, packing bound, and
testing whether `γ` is a function of them or admits a DP; (c) **mine the neighbour reductions**
(minimum SLP, minimum LZ77 phrases — `γ ≤ g`, `γ ≤ z`) for binary-alphabet gadget technique,
quoting the sentence that fixes each alphabet. Then a synthesis claim-register and an
adversarial review whose mandate is: *does anything actually answer the question, or is it a
gadget sketch dressed as a theorem?*

**Correction to my own reading of the `k = 2` data:** I said "the whole difficulty is
concentrated in factors of length 2". The LP gap at `k = 2` is indeed already `4/3`, but
`γ − γ₂` reaches **3** by `n = 17` (`docs/research/sigma2-algorithm.md`: `bbbaabaabbababaaa`,
`γ = 5`, `γ₂ = 2`, sampled), so `γ` itself does separate from the 2-attractor — the
localisation is only about the *LP*, not about `γ`.

**Lane B growth data** (exact rational LP, all binary strings, exhaustive):

| n | 1–6 | 7 | 8–11 | 12 |
| --- | --- | --- | --- | --- |
| max gap | 1 | 6/5 = 1.20 | 9/7 ≈ 1.286 | **4/3 ≈ 1.333** |
| # with gap > 1 | 0 | 4 | 16…200 | 408 |

Read: (i) **not** the `Θ(log n)` of general set cover — `4/3` at `n = 12` against `log₂12 ≈ 3.58`;
(ii) **not** a small-`k` artefact either — the *single-`k`* column already has `k = 2` at `4/3`
(and `k = 1` at 1), while `k = 3` reaches `3/2`; (iii) the median is exactly 1 and only ~10 % of
strings at `n = 12` have any gap.  So the covering family looks **benign**, and the conjecture to
test is `γ/LP* ≤ 4/3` for every binary string — checkable, and the lane is sampling `n = 14..16`
to look for a witness above it.

Standing rules carried into all three: no fabricated number, `timeout` on every run, progress
assertion in every loop, every "γ" backed by a *closed* bracket rather than an upper bound,
and an independent reviewer per lane.

## Research threads (opened 2026-11-12)

Compressed text indexing, split into two independent threads with their own briefs in
`docs/research/` (see the README there):

* **S — space** (`docs/research/space.md`): is `r` the right measure; hierarchy
  `δ ≤ γ ≤ r` and its separations; is `O(r)` space optimal (any lower bound?); is an
  `O(γ)`/`O(δ)`-space index with fast queries possible; where `σ` enters.
* **T — time** (`docs/research/time-{1..5}-*.md`): the state of the art in `O(r)` space,
  the space-for-time knobs and the Pareto frontier, what is *provably* impossible, the
  `O(γ)`/`O(δ)`-space end, and where the time actually goes in practice.

Standing rule for these threads (earned the hard way this session): **no contract is
written from recollection.** Every Lean target must be grounded in a quoted statement in
one of these briefs, with its verdict (PROVED / CONDITIONAL / OPEN / FOLKLORE) recorded.

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
