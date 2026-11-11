/-
SortBounds/Projects/XY/Naive.lean

The obvious algorithm for sorting `X + Y` (milestone `M1`): enumerate the
`X.card * Y.card` pairwise sums and merge sort them.  It ignores the additive
structure completely, so it is exactly the `O(N log N)` comparison sort of
`N = n·m` arbitrary items — the Harper–Payne–Savage–Strauss bound, not Fredman's
unrealised `O(n²)` scheme.

* `naivePairsSorted X Y` — sort the list of all pairwise sums;
* `naivePairsSorted_perm` / `naivePairsSorted_sorted` — it is a sorted
  permutation of `(pairSums X Y).toList`, i.e. it is a correct algorithm;
* `naivePairsSorted_count` — the contract's counting statement for `N` items,
  `N ≤ N · ⌈log₂(N+1)⌉`;
* `naivePairsMsort_*` — the same algorithm instantiated at
  `Instances.MergeSort.msortCount`, whose counter gives the genuine `Θ(N log N)`
  bound `naivePairsMsort_count : count ≤ N * (⌈log₂ N⌉ + 1)`.
-/
import SortBounds.Projects.XY.PairSums
import SortBounds.Instances.MergeSort

namespace SortBounds.Projects.XY

/-- The naive algorithm: list every pairwise sum, then merge sort the list.
(`noncomputable` only because `Finset ℕ` is a `Multiset`, so enumerating it requires
choosing a representative; the algorithm itself is the ordinary merge sort.) -/
noncomputable def naivePairsSorted (X Y : Finset ℕ) : List ℕ :=
  (pairSums X Y).toList.mergeSort (· ≤ ·)

theorem naivePairsSorted_perm (X Y : Finset ℕ) :
    (naivePairsSorted X Y).Perm (pairSums X Y).toList :=
  List.mergeSort_perm _ _

theorem naivePairsSorted_sorted (X Y : Finset ℕ) :
    (naivePairsSorted X Y).Pairwise (· ≤ ·) := by
  simpa [naivePairsSorted] using
    (List.pairwise_mergeSort' (r := (· ≤ ·)) (pairSums X Y).toList)

/-- The contract's counting statement for the naive algorithm.  For `N ≥ 1` items
`N ≤ N · ⌈log₂ (N+1)⌉` is the trivial inequality "every item is touched at least
once"; the *genuine* comparison accounting for this algorithm is
`naivePairsMsort_count` below, which counts what merge sort actually spends. -/
theorem naivePairsSorted_count (X Y : Finset ℕ) :
    ((naivePairsSorted X Y).length) * Nat.clog 2 ((pairSums X Y).toList.length + 1)
      ≥ (pairSums X Y).toList.length := by
  have hlen : (naivePairsSorted X Y).length = (pairSums X Y).toList.length :=
    (naivePairsSorted_perm X Y).length_eq
  rw [hlen]
  rcases Nat.eq_zero_or_pos (pairSums X Y).toList.length with h | h
  · simp [h]
  · exact Nat.le_mul_of_pos_right _
      (Nat.clog_pos (b := 2) (n := (pairSums X Y).toList.length + 1) (by norm_num) (by omega))

/-! ### The same algorithm, with its comparison counter -/

/-- The naive algorithm run through the counted merge sort of
`Instances.MergeSort`: the pair is (comparisons performed, sorted sums). -/
noncomputable def naivePairsMsort (X Y : Finset ℕ) : ℕ × List ℕ :=
  msortCount (· ≤ ·) (pairSums X Y).toList

theorem naivePairsMsort_perm (X Y : Finset ℕ) :
    (naivePairsMsort X Y).2.Perm (pairSums X Y).toList :=
  msortCount_perm _ _

theorem naivePairsMsort_sorted (X Y : Finset ℕ) :
    (naivePairsMsort X Y).2.Pairwise (· ≤ ·) :=
  msortCount_sorted _

/-- **The naive algorithm costs at most `N * (⌈log₂ N⌉ + 1)` comparisons**, where
`N = X.card * Y.card` is the number of pairwise sums: `Θ(N log N)`, i.e.
`Θ(n² log n)` when `X` and `Y` both have `n` elements. -/
theorem naivePairsMsort_count (X Y : Finset ℕ) :
    (naivePairsMsort X Y).1
      ≤ X.card * Y.card * (Nat.clog 2 (X.card * Y.card) + 1) := by
  have hlen : (pairSums X Y).toList.length = X.card * Y.card := by
    rw [Multiset.length_toList, pairSums_card]
  rw [naivePairsMsort, ← hlen]
  exact msortCount_counts_le _ _

end SortBounds.Projects.XY
