# Lane: FordJohnson — verified merge-insertion with an exact comparison count

**Question.** `Ω(n log n)` says what no algorithm can beat. How close does a real
algorithm get? Ford–Johnson (merge-insertion, 1959) achieves `n⌈log₂ n⌉ − O(n)`
and is *exactly* optimal for `n ≤ 11` (and `n = 20, 21`). No formalization of it
exists as far as we could find (searched 2026-11-09) — the closest Lean work is
Mathlib's `List.mergeSort` correctness, which has no count.

**Why it matters.** It is the upper-bound half of the open problem "what is
`S(n)`", and the count is what makes it interesting: correctness alone is easy,
the *exact* count is delicate (Jacobsthal insertion order).

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

/-- `F(n)`: the worst-case comparison count of merge-insertion on `n` elements. -/
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
* **M2** closed form for `fjCount` (Knuth TAOCP 5.3.1 gives
  `F(n) = Σ_{k≥1} ⌈(3/4)·2^k − 1/2⌉`-style sums; state the version you prove).
* **M3** the table: `fjCount n = Nat.clog 2 n!` for `n ≤ 11`, `n = 20, 21`
  (the cases where merge-insertion is optimal). Feeds lane `SN`.

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
* M2 (`fjCount` closed form) and M3 (optimality for `n ≤ 11`, `20`, `21`): open.
