# Lane: SAIS — suffix arrays, and a cost model that LCP actually improves

**Status: M0 LANDED; M1a–M1c LANDED with one corrected target (see the note under
`M1 target` and the Log); `lcp_guided_cost` still open.** Correctness is solved elsewhere (Isabelle AFP `SuffixArray`,
2024; JAR 2025), so the only unclaimed and interesting target is the **cost
model**.

**Question.** Sorting the `n` suffixes of a string is *not* the comparison
problem we proved a bound for: (a) each comparison is over strings, so its cost is
the number of characters inspected, not 1; (b) keeping an LCP lower bound makes
comparisons start past the shared prefix; (c) the linear-time algorithms
(SA-IS, DC3) sort *integer ranks* with radix/counting, i.e. they leave the
comparison model — the same door radix sort uses.

**Target (M0/M1, when unblocked).**

```lean
namespace SortBounds.Projects.SAIS

/-- Suffix `i` of `s`. -/
def suffix (s : List α) (i : Fin s.length) : List α
/-- Cost model: a comparison of two suffixes costs `1 + characters examined past
the supplied LCP lower bound`. -/
def cmpCost (lcp : ℕ) (a b : List α) : ℕ
/-- M1: LCP-guided sorting of suffixes costs `O(n log n)` character inspections
(instead of `Θ(n²)` for naive comparison). -/
theorem lcp_guided_cost (s : List α) : …

end SortBounds.Projects.SAIS
```

**Unblocked:** `XY` M1 landed (`docs/PROGRESS.md`); the weighted cost model is
in place. M1 here needs the LCP-array construction (where the `k` values come
from), which is the open piece.

## Prior art

Isabelle AFP `SuffixArray` (SA-IS correctness, 2024); Cheung thesis (SA-IS + BWT);
Kasai et al. 2001 (LCP in linear time); Manber–Myers 1993; Nong–Zhang–Chan 2009.

## M1 target (opened after `FjTree` and `SortTree` landed)

The LCP question in its precise form: *if you know the LCP, what does a comparison
cost?* With the machinery in `LCP.lean` (`lcp`, `cmpFrom`, `inspectCount`), the
answer is: `inspectCount s k i j = 1 + (true lcp - k)`, so a comparison costs **one**
inspection exactly when the supplied bound is the true LCP. The LCP *array* supplies
exactly that for neighbouring suffixes, and — the classical min property — for any
pair it supplies the minimum over the interval:

```lean
/-- `lcpAt s i` is the LCP of neighbouring suffixes `i` and `i+1`. -/
def lcpAt (s : List α) (i : ℕ) : ℕ

/-- **The LCP array's min property.**  For `i ≤ j`, the LCP of suffixes `i` and `j`
is the minimum of `lcpAt` over `[i, j)`. -/
theorem lcp_eq_inf_lcpAt {s : List α} {i j : ℕ} (hij : i ≤ j) :
    lcp (suffix s i) (suffix s j) = (Finset.Ico i j).inf' ⟨i, ?_⟩ (lcpAt s)

/-- Hence a comparison guided by the LCP array inspects exactly one position. -/
theorem inspectCount_of_inf_lcpAt {s} {i j : ℕ} (hij : i ≤ j) :
    inspectCount s ((Finset.Ico i j).inf' ⟨i, ?_⟩ (lcpAt s)) i j = 1

/-- **A suffix array can be verified in linear inspections.**  If `sa` is a
permutation of `0..n-1` and each neighbouring pair in `sa` is compared with the LCP
array's bound, the total inspection count is `sa.length - 1`, versus `Θ(n²)` for
naive comparison (already proved for `aⁿ`: `naiveInspectSum` is cubic). -/
theorem sorted_check_linear (sa : List ℕ) : …
```

> **Correction (M1a, M1b as written above are false).**  The minimum of `lcpAt` over the
> *text* interval `[i, j)` is only a **lower bound** for `lcp (suffix s i) (suffix s j)`:
> on `"aba"` the minimum over `[0, 2)` is `0` while the LCP is `1` (`Array.lean`,
> `inf'_lcpAt_aba`, `exists_inf'_lcpAt_ne_lcp`).  The min property is about
> *lexicographically* neighbouring suffixes, i.e. about a suffix array.  Proved instead, in
> `Array.lean` / `Chain.lean` / `Verify.lean`:
>
> * text order, soundness: `inf'_lcpAt_le_lcp`, `cmpFrom_inf'_lcpAt`,
>   `inspectCount_inf'_lcpAt` (`= 1 + (lcp - inf)`) and
>   `inspectCount_inf'_lcpAt_eq_one_iff` (one inspection **iff** the bound is tight);
> * text order, verbatim M1a/M1b **with the missing hypothesis** that the interval's suffixes
>   increase: `lcp_eq_inf'_lcpAt_of_increasing`, `inspectCount_inf'_lcpAt_of_increasing`;
> * suffix-array order, the real min property: `lcp_eq_inf'_of_chain`,
>   `lcp_suffix_eq_inf'_of_increasing` (M1a), `inspectCount_inf'_of_increasing` (M1b:
>   `= 1`), `cmpFrom_inf'_of_increasing`.
>
> **The contrast is the content**: in *text* order you get only `inf' ≤ lcp`
> (`inf'_lcpAt_le_lcp`) — enough to license the skip in `cmpFrom`, and the comparison then
> costs `1 + (lcp - inf)`, *not* `1` — whereas along the *suffix array* (a lexicographically
> increasing chain) you get `inf' = lcp` (`lcp_eq_inf'_of_chain`), which is what makes each
> comparison of the check cost exactly one inspection.  Reading the inequality as an equality
> is precisely the error being corrected here.
>
> Also, `i ≤ j` must be `i < j`: `Ico i i` is empty and has no `inf'`, and the `i = j` case
> reads `lcp (suffix s i) (suffix s i) = (suffix s i).length` (`Array.lean`,
> `lcp_suffix_self`).

Order: M1a `lcpAt` + the min property (the real lemma); M1b
`inspectCount_of_inf_lcpAt`; M1c the linear-verification corollary if time allows.
Out of scope: SA-IS itself (Isabelle has its correctness); Kasai's O(n)
construction of the array (state it, do not prove it).

## M2 target: Kasai's linear-time LCP array (opened 2026-11-11)

`verify_linear_time` says a suffix array can be *verified* in `n-1` inspections
**given its LCP array**.  The missing half is producing that array.  Kasai's
algorithm does it in `O(n)` character inspections, by exploiting
`lcp (rank i) ≥ lcp (rank (i-1)) - 1`: shift one position right, and the common
prefix can only lose one character.

```lean
/-- The inverse of a suffix array, as a function. -/
def saRank (sa : List ℕ) (i : ℕ) : ℕ

/-- **Kasai's algorithm**, with a character-inspection counter.  Input: the string
and its suffix array.  Output: `lcp[k] = lcp (suffix (sa k)) (suffix (sa (k+1)))`
(up to `n-2`) together with the number of inspected character pairs. -/
def kasai (s : List α) (sa : List ℕ) : List ℕ × ℕ

/-- The array is correct: entry `k` really is that LCP. -/
theorem kasai_lcp_correct (s : List α) (sa : List ℕ) (hsa : IsSaCandidate s sa) :
    ∀ k < sa.length - 1, (kasai s sa).1.getD k 0 = lcp (suffix s (sa.getD k 0)) (suffix s (sa.getD (k+1) 0))

/-- **And it is linear**: at most `2 * s.length` inspected pairs, not `Θ(n²)`. -/
theorem kasai_cost_le (s : List α) (sa : List ℕ) : (kasai s sa).2 ≤ 2 * s.length
```

Order: M2a `saRank` + `kasai` as a computable function (a `while` loop with an
explicit fuel/counter is fine — the *cost* is the theorem, not the runtime);
M2b correctness of the entries; M2c the `2n` bound, whose proof is the amortised
argument `h` drops by at most one per text position.  Landing this plus
`verify_linear_time` gives a complete linear-time *account* of suffix-array
verification: Kasai produces the LCP array in `2n` inspections, the checker verifies
the array in `n-1`.  Out of scope: bearing the suffix array itself (SA-IS), and
making `kasai` fast in Lean's runtime.

## Log

* **M0 landed** (`LCP.lean`). Cost model + the local accounting principle:
  `suffix`, `lcp`, `cmpCounted` (comparison with an inspection counter),
  `cmpCost k a b` / `inspectCount s k i j` (`= 1 + lcp (a.drop k) (b.drop k)`),
  `cmpFrom`, and
  * `suffix_compare_eq_of_lcp` — a genuinely common `k`-prefix can be skipped without
    changing the answer;
  * `cmpFrom_lcp_advance` — advancing `k` to the true `lcp` stays correct;
  * `inspectCount_lcp` — *any* two suffixes, compared with their true `lcp`, cost
    exactly `1` inspection;
  * `cmpFrom_inspectCount_le` / `inspectCount_eq_add` — the `k` skipped characters
    cost nothing (exactly `k` when `k` is a prefix of the suffix);
  * `inspectCount_succ_le` — one more skipped character saves at most one inspection;
  * `take_min_length`, `suffix_lcp_def`, `lcp_le_left/right`, `take_eq_take_iff`;
  * the `aⁿ` contrast: `lcp_suffix_replicate` (`n - max i j`),
    `inspectCount_replicate` (`n - max i j + 1` naive), `inspectCount_replicate_lcp`
    (`1` guided), `replicate_pair_cost`, and the totals over all pairs
    `naiveInspectSum a n` (cubic: `6 · naive = n (n-1) (n+4)`) vs `guidedInspectSum a n`
    (quadratic: `2 · guided = n (n-1)`), with
    `three_mul_naiveInspectSum : 3 · naive = (n + 4) · guided`.
* Signature note for the integrator/reviewer: `suffix` is total,
  `suffix (s : List α) (i : ℕ) : List α := s.drop i`, not `(i : Fin s.length)` as
  sketched in the target above — `Fin`-indexed suffixes are the case `i < s.length`,
  and totality keeps `drop`-lemmas usable. `cmpCost` is `cmpCost (k : ℕ) (a b : List α)`
  as sketched, and `inspectCount s k i j` is its suffix-level instance.
* Not attempted (M1): `lcp_guided_cost`, i.e. the `O(n log n)` total for sorting; it
  needs a suffix-sorting algorithm plus the LCP-array construction.
* **M1a landed** (`Array.lean`, `Chain.lean`) — with the correction recorded above.  The real
  lemma is the three-list lemma `lcp_eq_min_lcp_of_compare_lt`
  (`a < b < c` lexicographically ⟹ `lcp a c = min (lcp a b) (lcp b c)`), which gives the min
  property along a sorted chain `lcp_eq_inf'_of_chain`
  (`lcp (f i) (f j) = (Ico i j).inf' fun k => lcp (f k) (f (k + 1))` for `i < j` and `f`
  strictly increasing on `[i, j)`), via `compare_lt_of_chain` and `min_inf'_Ico_succ`.
  Text order: `inf'_lcpAt_le_lcp` (sound lower bound, by the sliding-window chain
  `take_drop_chain`), `cmpFrom_inf'_lcpAt`, `inspectCount_inf'_lcpAt`,
  `inspectCount_inf'_lcpAt_eq_one_iff`, the repaired M1a/M1b
  (`lcp_eq_inf'_lcpAt_of_increasing`, `inspectCount_inf'_lcpAt_of_increasing`), and the
  refutation `inf'_lcpAt_aba` / `inf'_lcpAt_ne_lcp` / `exists_inf'_lcpAt_ne_lcp` (with
  `lcp_self`, `lcp_suffix_self` for the `i = j` case).  Non-vacuity:
  `aab_text_min_property` (text order, `"aab"`, interval `[0, 2)`) and
  `banana_min_property` (rank order, `"banana"`, suffix array `[5,3,1,0,4,2]`, ranks `[1, 4)`).
* **M1b landed**: `inspectCount_inf'_of_increasing` — for ranks `i < j` of a strictly increasing
  enumeration `π`, the interval minimum of the neighbouring LCPs *is* the true LCP, so the
  guided comparison inspects exactly one position (`= 1`), and `cmpFrom_inf'_of_increasing`
  says it is also the correct comparison.
* **M1c landed** (`Verify.lean`): `saLcp`, `verifyStep`, `Verified`, `IsSaCandidate`, with
  `verifyStep_eq` / `inspectCount_verifyStep` (each step is correct and inspects one position),
  `sum_inspectCount_verify` (**`sa.length - 1` inspections in total**),
  `checkSa` (the check as a `List.all` program) and `checkSa_eq_true_iff`,
  `verified_chain` / `compare_lt_of_verify` (a passed check orders every pair of ranks),
  `lcp_eq_inf'_saLcp` (the min property with the array written out),
  `cmpFrom_of_verified` / `inspectCount_of_verified` (afterwards **any** pair costs one
  inspection and gives the true answer), `verify_linear_time`, and the sharper statement that a
  verified candidate **is** the suffix array: `saRank` (`= idxOf`), `mem_of_candidate`,
  `saRank_lt`, `getD_saRank`, and `compare_lt_iff_saRank_lt`
  (`compare (suffix i) (suffix j) = lt ↔ saRank sa i < saRank sa j`, for a verified
  `IsSaCandidate`).  Then the contrast **on the same `n - 1` pairs**: for `aⁿ` the suffix
  array is `replicateSa n = [n-1, …, 0]` (`replicate_verified`, `replicateSa_candidate`,
  `compare_replicate`), the guided check costs `n - 1`
  (`sum_inspectCount_verify_replicate`) against `(n-1)(n+2)/2` naive
  (`naive_verify_replicate`), i.e. `2 · naive = (n + 2) · guided`
  (`verify_contrast_replicate`), verified on `a⁴` by `contrast_replicate_four` (`3` vs `9`).
  Instances: `banana_verified`, `banana_inspect_one`.
* Assumed, not proved: the LCP array is **free** (Kasai's linear-time construction is out of
  scope, as is SA-IS correctness).  `lcp_guided_cost` — the total for a whole sorting
  algorithm — is still not attempted.
* Contract corrected by the integrator in `docs/PROGRESS.md`: the min property is about
  lexicographically adjacent suffixes, not text-adjacent ones (see the note under `M1 target`);
  the corrected statements are the ones listed in the Log entries above.
