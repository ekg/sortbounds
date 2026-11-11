# Lane: FordJohnson — verified merge-insertion with a comparison-count bound

**Question.** `Ω(n log n)` says what no algorithm can beat. How close does a real
algorithm get? Ford–Johnson (merge-insertion, 1959) achieves `n⌈log₂ n⌉ − O(n)`
comparisons, and its count reaches `⌈log₂ n!⌉` for `n ≤ 11` and `n = 20, 21`
(the literature's optimality results; see `docs/PRIOR-ART.md`). No formalization of
it exists as far as we could find (searched 2026-11-11) — the closest Lean work is
Mathlib's `List.mergeSort` correctness, which has no count.

**What this lane proves, exactly.** An *upper bound* on the comparison count
(`≤ fjCountJ n`), the Jacobsthal-order algorithm that achieves it, and the closed
form and table. It does **not** prove `fjCountJ n = S n`: that needs a transfer
from the list algorithm to a `Tree n` of the same depth (`Comparison/Bridge.lean`
has the mechanism, not the instance), and it does not prove *attainment*
(`∃ l, (fjSortJ l).1 = fjCountJ l.length`).

**Why it matters.** It is the upper-bound half of the open problem "what is
`S(n)`", and the count is what makes it interesting: correctness alone is easy,
the count is delicate (Jacobsthal insertion order).

## Contract (exact target signatures)

```lean
namespace SortBounds.Projects.FordJohnson

/-- Binary insertion of `x` into a sorted list, counted. -/
def insertCount [LinearOrder α] (x : α) (l : List α) : ℕ × List α
theorem insertCount_perm [LinearOrder α] (x) (l) :
    (insertCount x l).2.Perm (x :: l)
theorem insertCount_sorted [LinearOrder α] (x) (l) (h : l.Pairwise (· ≤ ·)) :
    (insertCount x l).2.Pairwise (· ≤ ·)
theorem insertCount_count [LinearOrder α] (x) (l) :
    (insertCount x l).1 ≤ Nat.clog 2 (l.length + 1)

/-- The merge-insertion algorithm, counted. -/
def fjSort [LinearOrder α] (l : List α) : ℕ × List α
theorem fjSort_perm [LinearOrder α] (l) : (fjSort l).2.Perm l
theorem fjSort_sorted [LinearOrder α] (l) : (fjSort l).2.Pairwise (· ≤ ·)

/-- `F(n)`: an upper bound on the comparison count of merge-insertion on `n` elements. -/
def fjCount (n : ℕ) : ℕ
theorem fjSort_count_le [LinearOrder α] (l) : (fjSort l).1 ≤ fjCount l.length

end SortBounds.Projects.FordJohnson
```

## Milestones

* **M0** `insertCount` + its three theorems. (`Nat.clog 2 (k+1)` comparisons for
  binary insertion into a list of length `k`.)
* **M1** `fjSort` correct (`perm`, `sorted`) for a *stated* `fjCount`
  recurrence, with `fjSort_count_le`. Chain insertion in the Jacobsthal order
  (`1, 3, 5, 11, 21, …`), pairing elements, and merging.
* **M2** closed form for the *Jacobsthal* count `fjCountJ` (done:
  `fjCountJ_eq_sum` for `n ≤ 22`).  NB `fjCount` is the crude whole-chain
  schedule and does **not** meet the table (`fjCount 4 = 8 > 5`); the deliverable
  is `fjCountJ`/`fjSortJ`, and the contract keeps `fjCount` only as the simple
  `O(n log n)` stepping stone (`fjCount_le`).
* **M3** the table: `fjCountJ n = Nat.clog 2 n!` for `n ≤ 11` and `n = 20, 21`
  (done).  Feeding lane `SN` with an actual `Tree` requires the list→`Tree`
  transfer, which is *not* done: `S n = fjCountJ n` remains unproved, and so does
  attainment.

## Rules

Do not touch files outside `SortBounds/Projects/FordJohnson/`. Validate with
`lake env lean SortBounds/Projects/FordJohnson/<File>.lean`. No `sorry`; if M2
fights you, stop at M1 and say exactly where the count got stuck.

## Prior art

Ford & Johnson 1959; Knuth TAOCP vol. 3 §5.3.1 (algorithm M, and the exact
`S(n)` table up to `n = 22`); Stober & Weiß 2022 for `S(16..18)`. Nothing
machine-checked found.

## Log

* 2026-11-11 — **M0 landed** (`Insertion.lean`): `insertCount` with
  `insertCount_perm`, `insertCount_sorted`, `insertCount_count`
  (`≤ ⌈log₂(list.length+1)⌉`).
* 2026-11-11 — **M1 landed** (`MergeInsertion.lean`): `pairUp` (+perm/length
  lemmas), `insertAll`/`insertAllCost` (`insertAll_count`), `loserCost`,
  `fjCount` (structural recursion with `termination_by`), and
  `fjSort_perm`/`fjSort_sorted`/`fjSort_count_le`.
  The lane worker hit the 30-minute cap with `fjSort_count_le`'s final
  arithmetic goal unsolved; the integrator finished it (unfold `loserCost`,
  `rw [hm] at hrec ⊢` to align the recursive call on the winners, then split on
  the unpaired element and `omega`).
* 2026-11-12 — **M2 landed, first half** (`Count.lean`): the `O(n log n)` claim is now
  machine-checked for the M1 recurrence — `insertAllCost_le`
  (`insertAllCost k n ≤ n ⌈log₂ (k+n)⌉`), `loserCost_le`/`loserCost_le_succ`, and
  **`fjCount_le : fjCount n ≤ n (⌈log₂ n⌉ + 1)`**.
* 2026-11-12 — **M2 landed, second half** (`Jacobsthal.lean`): the Jacobsthal numbers
  (`jac`, `jacPred`, `jac k + jac (k+1) = 2^(k+2)`), the insertion cost `jacInsertCost`
  (batch `k` = `jacPred k+1 … min M (jac k)` items, each searched in `jacLo + jacHi` slots),
  the literature recurrence **`fjCountJ_le_recurrence`**
  (`fjCountJ n = n/2 + fjCountJ (n/2) + jacInsertCost ⌈n/2⌉`) and the closed form
  **`fjCountJ_eq_sum`** (`F(n) = Σ_{k≤n} ⌈log₂ ⌈3k/4⌉⌉`, kernel-checked for `n ≤ 22`).
* 2026-11-12 — **M3 landed** (`JacobsthalInsertion.lean`): the Jacobsthal-order algorithm
  `fjSortJ` (`sortedPairs`/`insertItems` bookkeeping, bounded insertion `insertWindow` into
  the prefix below the partner, batch walk `insertJacobsthal`) with
  **`fjSortJ_perm`**, **`fjSortJ_sorted`** and
  **`fjSortJ_count_le : (fjSortJ l).1 ≤ fjCountJ l.length`**, plus the table
  **`fjCountJ_table`** (`F 4 … F 11 = 5, 7, 10, 13, 16, 19, 22, 26`) and
  `fjCountJ_eq_clog_factorial` (`fjCountJ n = ⌈log₂ n!⌉` for `4 ≤ n ≤ 11`) and
  `fjCountJ_eq_clog_factorial_large` (`n = 20, 21`).  Caveats in the file's docstring: the
  count is an upper bound on comparisons (attainment by an adversarial input is not proved),
  and `sortPairs` reorders the loser array for free (the loser array rides along with the
  winners' recursive sort in the real algorithm).
* 2026-11-11 — **M4 landed** (`Attain.lean`): the bounds of this lane are **attained**, so
  `fjCountJ` is the *worst-case* comparison count of `fjSortJ`, not merely an upper bound.
  Proved (all kernel-checked, `#print axioms` = `propext, Classical.choice, Quot.sound`):
  * **`insertCount_attains (k : ℕ) : ∃ x : ℕ, ∃ l : List ℕ, l.length = k ∧ (insertCount x l).1 = Nat.clog 2 (k + 1)`**
    via `insertCount_eq_clog_of_forall_le` (`x` below the whole window always takes the left
    branch, which is a deepest leaf) and `clog_half_eq`;
  * **`loserCost_attains (m : ℕ) : ∃ ws ls : List ℕ, ws.length = m ∧ ls.length = m ∧ (insertAll ls ws).1 = loserCost m`**
    (witnesses `replicate m 0`: inserting `0` into an all-`0` chain is always a deepest-path
    search).  Stated without the `1 ≤ m` hypothesis of the original sketch — it is not needed;
  * **`jacInsertCost_attains (M K : ℕ) : ∃ items, items.length = M ∧ (insertJacobsthal items M 0 (attnChain (K+M) M)).1 = jacInsertCost M`**
    — the insertion phase alone, on the canonical items `attnItems` / chain `attnChain`;
  * **`fjCountJ_attains (n : ℕ) (hn : 2 ≤ n) : ∃ l : List ℕ, l.length = n ∧ (fjSortJ l).1 = fjCountJ n`**
    — the prize.  The witness is `attnList n 0`, and `attnList_spec` gives more:
    `(attnList n K).Nodup ∧ length = n ∧ ∀ x ∈ attnList n K, K ≤ x ∧ x < K + n ∧
    (fjSortJ (attnList n K)).1 = fjCountJ n`, i.e. **the input is a permutation of
    `K … K+n-1` on which the algorithm spends exactly `F(n)`**.
  Method: the items to insert are the values `K … K+M-1` in *decreasing insertion order*
  (`attainVal M K j = K + M - 1 - t(j)`, `jacBatchOf` = the batch of rank `j`), so every item
  is below everything inserted before it and below every winner; the search window of a batch-`k`
  item then has exactly `jacLo + jacHi - 1 - j'` elements with `j' < 2^k`, so every search of
  the batch costs exactly `⌈log₂ (jacLo + jacHi)⌉`.  The general exact-count lemmas are
  `insertBatch_eq` (a batch costs exactly `|batch| ⌈log₂ T⌉`) and `insertJacobsthal_eq` (the
  walk costs exactly `jacInsertCostAux`); the bookkeeping around `pairUp`/`sortPairs` is
  `pairUp_flatMap_pairs`, `sortPairs_map_eq`, `perm_range_of_nodup_in_range`.
  Attainment was checked by brute force first (`n ≤ 9` exhaustive over permutations: max over
  inputs `= fjCountJ n` exactly for `2 ≤ n ≤ 9`; the same construction attains for `n ≤ 40`),
  so the target is true and no counterexample exists.
  **Stale prose to fix by the integrator**: the "does not prove *attainment*" clauses above
  (README intro and the M3 log entry) are superseded by this entry; the remaining caveat
  `fjCountJ n = S n` (a list→`Tree` transfer, `Comparison/Bridge.lean`) is *not* addressed here
  and still stands.
