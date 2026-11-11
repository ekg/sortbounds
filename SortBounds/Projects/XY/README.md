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

/-- Number of *distinct* orderings of `n²` sums is at most `2^c` for a
`c`-comparison decision procedure: the `b = 2` instance of `Core.Branching`. -/
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

* (empty)
