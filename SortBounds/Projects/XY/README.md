# Lane: XY — sorting `X+Y` (Fredman / Berlekamp)

**Question.** Given `X, Y ⊂ ℝ` of size `n`, sort the `n²` pairwise sums. Output
size alone forces `Ω(n²)`. Berlekamp asked (Fredman 1976): can the *structure* be
exploited? Harper–Payne–Savage–Strauss gave `O(n² log n)`; Fredman showed `O(n²)`
comparisons suffice but no algorithm realizes it. **Open** (TOPP #41), and
`3SUM`-hardness (TOPP #11) is the neighbouring conjecture.

**Why it matters.** This is the canonical counterweight to our `n log n`: the
moment the input has additive structure, the comparison bound is about
*comparisons of sums*, and the `n!` counting argument no longer governs.

## Contract (exact target signatures, M0)

```lean
namespace SortBounds.Projects.XY

/-- The multiset of pairwise sums. -/
def pairSums (X Y : Finset ℕ) : Multiset ℕ

/-- Distinct pairwise sums: at most `X.card * Y.card` (collapsing equal sums). -/
theorem pairSums_card_le (X Y : Finset ℕ) :
    (pairSums X Y).toFinset.card ≤ X.card * Y.card

/-- M1: the naive algorithm, proved correct and counted (`n²` items, so
`Θ(n² log n)` comparisons). -/
def naivePairsSorted (X Y : Finset ℕ) : List ℕ
theorem naivePairsSorted_perm (X Y) : (naivePairsSorted X Y).Perm (pairSums X Y).toList
theorem naivePairsSorted_sorted (X Y) : (naivePairsSorted X Y).Pairwise (· ≤ ·)
theorem naivePairsSorted_count (X Y) :
    ((naivePairsSorted X Y).length) * Nat.clog 2 ((pairSums X Y).toList.length + 1)
      ≥ (pairSums X Y).toList.length

end SortBounds.Projects.XY
```

Note (added after review): the M0 counting corollary must be stated as *"the
generic `N`-item bound at `N = X.card * Y.card`"*, never as an `Ω(n² log n)`
bound on the sums problem — Fredman's `O(n²)` scheme is precisely the reason the
generic bound does not apply there.

**M2 is a research gate**, do not start it: `def fredmanCompares (n) : ℕ` and the
statement of Fredman's `O(n²)` comparison scheme — write it as a documented
`Prop`-valued definition plus a citation, never as `sorry`.

## Milestones

* **M0** `pairSums` + the counting corollary (instantiate `Core.Branching` with
  `b = 2`, or reuse `Comparison.Aggregate`'s machinery) + the output-size
  observation that sorting `n²` items needs `≥ log₂((n²)!)` comparisons.
* **M1** the naive algorithm (`List.mergeSort` on `(pairSums X Y).toList`),
  correct and with a stated comparison count. Instantiate
  `Instances.MergeSort` if it fits.
* **M2** *gated*: Fredman's `O(n²)` scheme — statement only, with citation.

## Rules

Own only `SortBounds/Projects/XY/`. `lake env lean`. No `sorry`. Keep M0 small
enough that it certainly lands.

## Prior art

Fredman 1976 (TCS); Harper–Payne–Savage–Strauss 1975; TOPP #41 (open); 3SUM,
TOPP #11 (open). No formalization found.

## Log

* 2026-11-11 — **M0 landed.** `PairSums.lean`: `pairSums`, `pairSums_mem`,
  `pairSums_card` (`= X.card * Y.card` entries), the contract's `pairSums_card_le`
  (distinct sums `≤ X.card * Y.card`), the `b = 2` bits-per-probe corollary
  `transcripts_card_le_pow_two`, and the output-size observation
  `factorial_mul_card_le_two_pow_depth` / `log2_factorial_mul_card_le_depth`
  (the generic `N = n·m` bound: a tree that sorts *every* `N`-element input with
  distinct values has depth `≥ log₂((n·m)!)`; **not** a bound on the sums
  problem — corrected after review, Fredman 1976 is the reason).
* 2026-11-11 — **M1 landed.** `Naive.lean`: `naivePairsSorted` with
  `naivePairsSorted_perm`, `naivePairsSorted_sorted`, `naivePairsSorted_count`,
  plus the same algorithm run through `Instances.MergeSort.msortCount`
  (`naivePairsMsort`, `_perm`, `_sorted`, `_count`), which supplies the genuine
  `count ≤ N * (⌈log₂ N⌉ + 1)` bound with `N = X.card * Y.card`.
* All six contract signatures are proved verbatim; no `sorry`; `#print axioms`
  is checked in `scripts/axioms.lean` by the integrator.
* Reviewed: `transcripts_card_le_pow_two` is a literal alias of
  `Core.Branching.card_le_pow_of_prefixFree` at `b = 2` and
  `naivePairsSorted_count` is pure `clog` arithmetic; both are honest re-exports,
  the substantive count is `naivePairsMsort_count`.
* The contract's `naivePairsSorted_count` is the trivial `N ≤ N · ⌈log₂(N+1)⌉`
  (kept as specified); the informative count is `naivePairsMsort_count`.  The two
  `M1` definitions are `noncomputable` because enumerating a `Finset` goes through
  `Multiset.toList`, which chooses a representative.
* **M2 not started** (gated by this README: statement-only, research level).
