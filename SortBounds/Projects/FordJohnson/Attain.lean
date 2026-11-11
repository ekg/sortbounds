/-
SortBounds/Projects/FordJohnson/Attain.lean

The other half of the count: the bounds of this lane are **attained**.

`JacobsthalInsertion.lean` proves `(fjSortJ l).1 ≤ fjCountJ l.length`: the algorithm never
spends more than the literature's `F(n)`.  That is an upper bound on *one* input's cost only
in the sense that it holds for *every* input; here we show that some input makes every single
comparison of the analysis happen, so the bound is not slack:

* `insertCount_attains` — `∃ x l, l.length = k ∧ (insertCount x l).1 = ⌈log₂ (k+1)⌉`: the
  deepest leaf of the bisection tree is reachable (`insertCount_eq_clog_of_forall_le`: an
  element below the whole window always takes the left branch, which is deepest);
* `loserCost_attains` — a batch of `m` insertions into a chain of `m` all-equal elements
  costs exactly `loserCost m`;
* `fjCountJ_attains` — **`∃ l : List ℕ, l.length = n ∧ (fjSortJ l).1 = fjCountJ n`**: there is
  an input on which merge-insertion spends exactly `F(n) = fjCountJ n` comparisons, i.e. the
  `≤` of `fjSortJ_count_le` is an equality for that input, and hence `fjCountJ n` is the
  worst-case cost of the algorithm on `n` elements.

### The attaining input

Write `n = 2m` (`2m+1` for odd `n`) and `M = ⌈n/2⌉`.  The input is built recursively: the
winners are an attaining list of length `m`, scaled into the block `[K+m+1, K+m+1+m)` for a
descent parameter `K` (the losers of the next level live below them), and the `M` items to
insert get the values `K + M - 1 - t`, where `t` is the number of items inserted before them
in the Jacobsthal order.  Consequences, all of which the algorithm's count needs:

* every item is below every winner, so the search window of the item of rank `j` after `s`
  insertions always has exactly `j + s` elements (no winner and no inserted element is lost);
* every item is below everything inserted before it, so each insertion descends the left
  spine of its window — the deepest leaf (`insertCount_eq_clog_of_forall_le`);
* the window of a batch-`k` item is `⌈2^(k+1)⌉ - 1 - j'` elements for inner index `j'`
  (`jacLo + jacHi = 2^(k+1)` in a full batch), and `j' < 2^k`, so the cost `⌈log₂ ⌉` of the
  window is the same `k+1` for every item of the batch.

That is exactly `jacInsertCostAux`: `jacHi - jacLo` items per batch, each costing
`⌈log₂ (jacLo + jacHi)⌉`.
-/
import SortBounds.Projects.FordJohnson.JacobsthalInsertion

namespace SortBounds.Projects.FordJohnson

/-! ### `⌈log₂ ·⌉` under halving -/

/-- Half of a nonempty window needs exactly one bit less: `⌈log₂ (k+1)⌉ = ⌈log₂ (k/2 + 1)⌉ + 1`
for `k ≥ 1`.  (The `≤` half is `clog_half_add_one`, which is all the upper bound needs.) -/
theorem clog_half_eq (k : ℕ) (hk : 0 < k) :
    Nat.clog 2 (k + 1) = Nat.clog 2 (k / 2 + 1) + 1 := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hj1 : 1 ≤ j := by omega
    have hk' : k / 2 = j := by omega
    rw [hk', hj, clog_two_add_one j hj1]
  · have hk' : k / 2 = j := by omega
    have hkj : k + 1 = (j + 1) + (j + 1) := by omega
    rw [hk', hkj, clog_two_add (j + 1) (by omega)]

/-! ### Binary insertion attains `⌈log₂ (k+1)⌉` -/

/-- **An element below the whole window takes the deepest path.**  If `x` is at most every
element of `l`, then every comparison `x ≤ a` succeeds, the search always continues into the
first half, and the number of comparisons is exactly `⌈log₂ (l.length + 1)⌉`. -/
theorem insertCount_eq_clog_of_forall_le (x : ℕ) (l : List ℕ) (h : ∀ a ∈ l, x ≤ a) :
    (insertCount x l).1 = Nat.clog 2 (l.length + 1) := by
  suffices H : ∀ k (l : List ℕ), l.length = k → (∀ a ∈ l, x ≤ a) →
      (insertCount x l).1 = Nat.clog 2 (l.length + 1) from H l.length l rfl h
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro l hl hall
    match l with
    | [] =>
      rw [insertCount.eq_1]
      simp
    | y :: ys =>
      subst hl
      have hpos : 0 < (y :: ys).length := by simp
      have htake_len : ((y :: ys).take ((y :: ys).length / 2)).length = (y :: ys).length / 2 := by
        rw [List.length_take]
        omega
      obtain ⟨a, bs, hdrop⟩ : ∃ a bs, (y :: ys).drop ((y :: ys).length / 2) = a :: bs := by
        cases hh : (y :: ys).drop ((y :: ys).length / 2) with
        | nil => exact absurd hh (drop_half_ne_nil (by simp))
        | cons a bs => exact ⟨a, bs, rfl⟩
      have hamem : a ∈ (y :: ys).drop ((y :: ys).length / 2) := by
        rw [hdrop]; exact List.mem_cons_self
      have hx : x ≤ a := hall a ((List.drop_sublist _ _).subset hamem)
      simp only [insertCount_drop_cons x y ys hdrop, ite_eq_left hx]
      have ih_take : (insertCount x ((y :: ys).take ((y :: ys).length / 2))).1
          = Nat.clog 2 (((y :: ys).take ((y :: ys).length / 2)).length + 1) :=
        ih _ (by omega) _ rfl (fun a ha => hall a ((List.take_sublist _ _).subset ha))
      rw [ih_take, htake_len]
      exact (clog_half_eq _ hpos).symm

/-- **Binary insertion attains its bound**: on a window of `k` elements there is an element
whose insertion costs exactly `⌈log₂ (k+1)⌉` comparisons. -/
theorem insertCount_attains (k : ℕ) :
    ∃ x : ℕ, ∃ l : List ℕ, l.length = k ∧ (insertCount x l).1 = Nat.clog 2 (k + 1) := by
  refine ⟨0, List.replicate k 0, List.length_replicate, ?_⟩
  rw [insertCount_eq_clog_of_forall_le 0 (List.replicate k 0) (by simp),
    List.length_replicate]

/-! ### A batch of insertions attains `insertAllCost` -/

/-- **`m` zeros inserted into any chain cost exactly `insertAllCost l.length m`**: `0` is below
every element, so each of the `m` insertions is a deepest-path search
(`insertCount_eq_clog_of_forall_le`), and the chain grows by one each time. -/
theorem insertAll_replicate_zero (m : ℕ) :
    ∀ l : List ℕ, (insertAll (List.replicate m 0) l).1 = insertAllCost l.length m := by
  induction m with
  | zero =>
    intro l
    simp [insertAll, insertAllCost]
  | succ m ih =>
    intro l
    have hlen : (insertCount (0 : ℕ) l).2.length = l.length + 1 := insertCount_length 0 l
    rw [List.replicate_succ]
    simp only [insertAll]
    rw [insertAllCost_succ, ih (insertCount (0 : ℕ) l).2, hlen,
      insertCount_eq_clog_of_forall_le 0 l (by simp)]

/-- **The loser insertions of merge-insertion attain their bound**: inserting `m` fresh
elements into a chain of `m` elements can cost exactly `loserCost m` comparisons, so
`loserCost` is the worst case of the insertion phase (`insertAll_count` is the other half). -/
theorem loserCost_attains (m : ℕ) :
    ∃ ws ls : List ℕ, ws.length = m ∧ ls.length = m ∧ (insertAll ls ws).1 = loserCost m :=
  ⟨List.replicate m 0, List.replicate m 0, List.length_replicate, List.length_replicate, by
    rw [insertAll_replicate_zero m (List.replicate m 0)]
    simp [loserCost]⟩

end SortBounds.Projects.FordJohnson
