# Lane: SAIS — suffix arrays, and a cost model that LCP actually improves

**Status: M0 LANDED; M1 (`lcp_guided_cost`) not started.** Correctness is solved elsewhere (Isabelle AFP `SuffixArray`,
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
