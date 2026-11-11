/-
SortBounds/Projects/FordJohnson/JacobsthalInsertion.lean

Milestone **M2/M3** of the `FordJohnson` lane: merge-insertion with the literature's count.

`MergeInsertion.lean` inserts every loser into the whole chain of winners.  Ford and Johnson
insert the losers into a *growing sorted prefix* instead: the loser of the `t`-th smallest
winner is only ever searched for among the chain elements below its own partner, and the
losers are visited in **Jacobsthal order** (`1`, then `3, 2`, then `5, 4`, then `11, …, 6`).
Inside one batch `t + s` — the rank plus the number of items already inserted — is constant,
so every binary search in the batch faces the same number `⌈log₂ (t+s+1)⌉` of slots: the
searches are perfectly balanced, whence

  `F(n) = n/2 + F(n/2) + (sum over the Jacobsthal batches of (items in batch) · ⌈log₂ window⌉)`

(`Jacobsthal.lean`).  The unpaired element of an odd-length input rides along in the same
order as one more item with no upper bound: the chain elements below "rank `m+1`" are the
whole chain, which is exactly `t + s = m + s`.

What this file proves, for the algorithm `fjSortJ`:

* `fjSortJ_perm`      — it returns a permutation of its input;
* `fjSortJ_sorted`    — the output is sorted;
* `fjSortJ_count_le`  — `(fjSortJ l).1 ≤ fjCountJ l.length`, the literature's `F`.

Together with `fjCountJ_table` (`F 4 … F 11 = 5, 7, 10, 13, 16, 19, 22, 26`) and
`fjCountJ_eq_clog_factorial` this makes merge-insertion's optimality for `n ≤ 11`
machine-checked.

### What is counted, and what is not

Only `pairUp` and `insertWindow` compare values, so `(fjSortJ l).1` is a genuine comparison
count: `⌊n/2⌋` for the pairing, `F(⌊n/2⌋)` recursively, and one bounded binary search per
item.  Two bookkeeping steps inspect values without being charged a comparison, and neither
needs one in a real implementation:

* `sortPairs` orders the winner/loser pairs by winner.  In merge-insertion the loser array
  travels with the winners through the recursive sort, so this permutation is free — we
  recompute it from the values instead of threading the permutation through the recursion.
  Ties are broken arbitrarily and cannot affect the count:
  `countP_fst_lt_le_index` only counts winners strictly below the partner's value.
* `List.countP` / `List.length` locate the window; the search *inside* the window is
  `insertCount`, and that is charged.
-/
import SortBounds.Projects.FordJohnson.Jacobsthal

namespace SortBounds.Projects.FordJohnson

variable {α : Type*}

/-! ### Splitting the chain at a bound -/

/-- Split `l` at the first element that is not strictly below `b`.  This is the window a
bounded insertion may search: everything below the bound comes first. -/
def splitBelow [LinearOrder α] (b : α) : List α → List α × List α
  | [] => ([], [])
  | a :: as =>
    if a < b then (a :: (splitBelow b as).1, (splitBelow b as).2) else ([], a :: as)

theorem splitBelow_append [LinearOrder α] (b : α) (l : List α) :
    (splitBelow b l).1 ++ (splitBelow b l).2 = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases h : a < b
    · rw [splitBelow, if_pos h, List.cons_append]
      exact congrArg (a :: ·) ih
    · rw [splitBelow, if_neg h]
      rfl

theorem splitBelow_fst_lt [LinearOrder α] (b : α) :
    ∀ (l : List α) {a : α}, a ∈ (splitBelow b l).1 → a < b := by
  intro l
  induction l with
  | nil => intro a ha; exact absurd ha (by simp [splitBelow])
  | cons c cs ih =>
    intro a ha
    by_cases h : c < b
    · rw [splitBelow, if_pos h] at ha
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact h
      · exact ih hmem
    · rw [splitBelow, if_neg h] at ha
      exact absurd ha (by simp)

theorem splitBelow_snd_le [LinearOrder α] (b : α) :
    ∀ (l : List α), l.Pairwise (· ≤ ·) → ∀ a ∈ (splitBelow b l).2, b ≤ a := by
  intro l
  induction l with
  | nil => intro _ a ha; exact absurd ha (by simp [splitBelow])
  | cons c cs ih =>
    intro hs a ha
    have hcs : cs.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hs).2
    have hcross : ∀ x ∈ cs, c ≤ x := (List.pairwise_cons.mp hs).1
    by_cases h : c < b
    · rw [splitBelow, if_pos h] at ha
      exact ih hcs a ha
    · rw [splitBelow, if_neg h] at ha
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact not_lt.mp h
      · exact le_trans (not_lt.mp h) (hcross a hmem)

theorem splitBelow_fst_length_le_countP [LinearOrder α] (b : α) :
    ∀ (l : List α), (splitBelow b l).1.length ≤ l.countP (· < b) := by
  intro l
  induction l with
  | nil => simp [splitBelow]
  | cons c cs ih =>
    by_cases h : c < b
    · rw [splitBelow, if_pos h, List.length_cons, List.countP_cons]
      have hc : (if (decide (c < b) : Bool) = true then 1 else 0) = 1 := by simp [h]
      rw [hc]
      omega
    · rw [splitBelow, if_neg h, List.length_nil]
      exact Nat.zero_le _

/-! ### Bounded binary insertion -/

/-- The number of slots a bounded insertion may place its element in. -/
def windowSize [LinearOrder α] : Option α → List α → ℕ
  | none, l => l.length
  | some b, l => l.countP (· < b)

/-- Insert `x` into the sorted list `l` by binary search, using the upper bound `x ≤ b` that a
pair comparison provides: only the part of `l` strictly below `b` can hold `x`'s position. -/
def insertWindow [LinearOrder α] (bnd : Option α) (x : α) (l : List α) : ℕ × List α :=
  match bnd with
  | none => insertCount x l
  | some b =>
    let s := splitBelow b l
    let r := insertCount x s.1
    (r.1, r.2 ++ s.2)

theorem insertWindow_perm [LinearOrder α] (bnd : Option α) (x : α) (l : List α) :
    (insertWindow bnd x l).2.Perm (x :: l) := by
  cases bnd with
  | none => exact insertCount_perm x l
  | some b =>
    show ((insertCount x (splitBelow b l).1).2 ++ (splitBelow b l).2).Perm (x :: l)
    refine (List.Perm.append_right _ (insertCount_perm x (splitBelow b l).1)).trans ?_
    rw [List.cons_append, splitBelow_append b l]

theorem insertWindow_length [LinearOrder α] (bnd : Option α) (x : α) (l : List α) :
    (insertWindow bnd x l).2.length = l.length + 1 :=
  (insertWindow_perm bnd x l).length_eq.trans (by simp)

theorem insertWindow_sorted [LinearOrder α] (bnd : Option α) (x : α) (l : List α)
    (hl : l.Pairwise (· ≤ ·)) (hb : ∀ b, bnd = some b → x ≤ b) :
    (insertWindow bnd x l).2.Pairwise (· ≤ ·) := by
  cases bnd with
  | none => exact insertCount_sorted x l hl
  | some b =>
    show ((insertCount x (splitBelow b l).1).2 ++ (splitBelow b l).2).Pairwise (· ≤ ·)
    have hxb : x ≤ b := hb b rfl
    have hl' : ((splitBelow b l).1 ++ (splitBelow b l).2).Pairwise (· ≤ ·) := by
      rw [splitBelow_append]; exact hl
    rw [List.pairwise_append] at hl'
    obtain ⟨h1, h2, h3⟩ := hl'
    rw [List.pairwise_append]
    refine ⟨insertCount_sorted x _ h1, h2, ?_⟩
    intro u hu v hv
    rcases List.mem_cons.mp ((insertCount_perm x _).mem_iff.mp hu) with rfl | hu'
    · exact le_trans hxb (splitBelow_snd_le b l hl v hv)
    · exact h3 u hu' v hv

theorem insertWindow_count [LinearOrder α] (bnd : Option α) (x : α) (l : List α) :
    (insertWindow bnd x l).1 ≤ Nat.clog 2 (windowSize bnd l + 1) := by
  cases bnd with
  | none => exact insertCount_count x l
  | some b =>
    show (insertCount x (splitBelow b l).1).1 ≤ Nat.clog 2 (l.countP (· < b) + 1)
    refine (insertCount_count x (splitBelow b l).1).trans ?_
    exact Nat.clog_mono_right 2 (by
      have := splitBelow_fst_length_le_countP b l
      omega)

/-! ### Counting the elements below a value -/

theorem countP_eq_zero_of_forall [LinearOrder α] {b : α} :
    ∀ (l : List α), (∀ x ∈ l, b ≤ x) → l.countP (· < b) = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    have ha : (decide (a < b) : Bool) = false := by
      have hlt : ¬ a < b := not_lt.mpr (h a (by simp))
      simp [hlt]
    rw [List.countP_cons, ha]
    simp only [Bool.false_eq_true, if_false, Nat.add_zero]
    exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

/-! ### Ordering the pairs by winner -/

/-- Insert a winner/loser pair into a list of pairs ordered by winner. -/
def insertPair [LinearOrder α] (q : α × α) : List (α × α) → List (α × α)
  | [] => [q]
  | p :: ps => if q.1 ≤ p.1 then q :: p :: ps else p :: insertPair q ps

/-- Order the winner/loser pairs by their winners.  In merge-insertion the loser array moves
with the winners through the recursive sort, so this permutation is bookkeeping and costs no
comparison (see the module docstring). -/
def sortPairs [LinearOrder α] : List (α × α) → List (α × α)
  | [] => []
  | q :: qs => insertPair q (sortPairs qs)

theorem insertPair_perm [LinearOrder α] (q : α × α) :
    ∀ (ps : List (α × α)), (insertPair q ps).Perm (q :: ps) := by
  intro ps
  induction ps with
  | nil => simp [insertPair]
  | cons p ps ih =>
    by_cases h : q.1 ≤ p.1
    · rw [insertPair, if_pos h]
    · rw [insertPair, if_neg h]
      exact (List.Perm.cons p ih).trans (List.Perm.swap' q p (List.Perm.refl ps))

theorem sortPairs_perm [LinearOrder α] (ps : List (α × α)) : (sortPairs ps).Perm ps := by
  induction ps with
  | nil => exact List.Perm.refl _
  | cons q qs ih => exact (insertPair_perm q (sortPairs qs)).trans (ih.cons q)

theorem insertPair_pairwise [LinearOrder α] (q : α × α) :
    ∀ (ps : List (α × α)), ps.Pairwise (fun p r => p.1 ≤ r.1) →
      (insertPair q ps).Pairwise (fun p r => p.1 ≤ r.1) := by
  intro ps
  induction ps with
  | nil => intro _; simp [insertPair]
  | cons p ps ih =>
    intro hs
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    by_cases h : q.1 ≤ p.1
    · rw [insertPair, if_pos h, List.pairwise_cons]
      refine ⟨fun x hx => ?_, hs⟩
      rcases List.mem_cons.mp hx with hxp | hx'
      · rw [hxp]; exact h
      · exact le_trans h (hhead x hx')
    · rw [insertPair, if_neg h, List.pairwise_cons]
      refine ⟨fun x hx => ?_, ih htail⟩
      have hmemy : x = q ∨ x ∈ ps := List.mem_cons.mp ((insertPair_perm q ps).mem_iff.mp hx)
      rcases hmemy with hxq | hx'
      · rw [hxq]; exact le_of_lt (not_le.mp h)
      · exact hhead x hx'

theorem sortPairs_pairwise [LinearOrder α] (ps : List (α × α)) :
    (sortPairs ps).Pairwise (fun p q => p.1 ≤ q.1) := by
  induction ps with
  | nil => exact List.Pairwise.nil
  | cons q qs ih => exact insertPair_pairwise q _ ih

/-- **The growing sorted prefix.**  In a list of pairs ordered by winner, the number of
winners strictly below the winner of the pair at index `j` is at most `j`: everything below it
has already been inserted when that loser comes up. -/
theorem countP_fst_lt_le_index [LinearOrder α] :
    ∀ (ps : List (α × α)) (j : ℕ) (hj : j < ps.length),
      ps.Pairwise (fun p q => p.1 ≤ q.1) → (ps.map Prod.fst).countP (· < ps[j].1) ≤ j := by
  intro ps
  induction ps with
  | nil => intro j hj; simp at hj
  | cons q qs ih =>
    intro j hj hs
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    rcases j with _ | j
    · rw [List.map_cons, List.countP_cons, List.getElem_cons_zero]
      have hz : (qs.map Prod.fst).countP (· < q.1) = 0 :=
        countP_eq_zero_of_forall _ (fun x hx => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
          exact hhead p hp)
      rw [hz]
      have hq : (decide (q.1 < q.1) : Bool) = false := by simp
      rw [hq]
      simp
    · rw [List.map_cons, List.countP_cons, List.getElem_cons_succ]
      have hj' : j < qs.length := by simpa using hj
      have hrec := ih j hj' htail
      split <;> omega

/-! ### Inserting one Jacobsthal batch -/

/-- Insert a batch of items into the chain, in the given order (decreasing rank, as
merge-insertion does it). -/
def insertBatch [LinearOrder α] : List (Option α × α) → List α → ℕ × List α
  | [], l => (0, l)
  | q :: qs, l =>
    let r := insertWindow q.1 q.2 l
    let r' := insertBatch qs r.2
    (r.1 + r'.1, r'.2)

theorem insertBatch_perm [LinearOrder α] (batch : List (Option α × α)) (l : List α) :
    (insertBatch batch l).2.Perm (l ++ batch.map Prod.snd) := by
  induction batch generalizing l with
  | nil => simp [insertBatch]
  | cons q qs ih =>
    simp only [insertBatch, List.map_cons, List.cons_append]
    refine (ih (insertWindow q.1 q.2 l).2).trans ?_
    refine ((insertWindow_perm q.1 q.2 l).append_right (qs.map Prod.snd)).trans ?_
    exact (List.perm_middle (l₁ := l) (l₂ := qs.map Prod.snd)).symm

theorem insertBatch_length [LinearOrder α] (batch : List (Option α × α)) (l : List α) :
    (insertBatch batch l).2.length = l.length + batch.length := by
  rw [(insertBatch_perm batch l).length_eq, List.length_append, List.length_map]

theorem insertBatch_sorted [LinearOrder α] (batch : List (Option α × α)) (l : List α)
    (hl : l.Pairwise (· ≤ ·)) (hb : ∀ q ∈ batch, ∀ b, q.1 = some b → q.2 ≤ b) :
    (insertBatch batch l).2.Pairwise (· ≤ ·) := by
  induction batch generalizing l with
  | nil => simpa [insertBatch] using hl
  | cons q qs ih =>
    simp only [insertBatch]
    refine ih _ (insertWindow_sorted q.1 q.2 l hl ?_) ?_
    · intro b hbnd; exact hb q (by simp) b hbnd
    · intro p hp b hbnd; exact hb p (List.mem_cons_of_mem _ hp) b hbnd

/-- **The comparisons one Jacobsthal batch costs.**  `T` bounds, for every item of the batch,
the insertion window plus one: the winners below the item's partner plus the elements already
inserted.  Each insertion is a bounded binary search into a window of fewer than `T` slots, so
it costs at most `⌈log₂ T⌉`, and the whole batch at most `|batch| ⌈log₂ T⌉`. -/
theorem insertBatch_count [LinearOrder α] (ws : List α) (s T : ℕ) (batch : List (Option α × α))
    (l ins : List α) (hperm : l.Perm (ws ++ ins)) (hlen : ins.length = s)
    (hsome : ∀ (j : ℕ) (q : Option α × α) (b : α), batch[j]? = some q → q.1 = some b →
      ws.countP (· < b) + s + j + 1 ≤ T)
    (hnone : ∀ (j : ℕ) (q : Option α × α), batch[j]? = some q → q.1 = none →
      ws.length + s + j + 1 ≤ T) :
    (insertBatch batch l).1 ≤ batch.length * Nat.clog 2 T := by
  induction batch generalizing l ins s with
  | nil => simp [insertBatch]
  | cons q qs ih =>
    have hhead : (insertWindow q.1 q.2 l).1 ≤ Nat.clog 2 T := by
      refine (insertWindow_count q.1 q.2 l).trans (Nat.clog_mono_right 2 ?_)
      cases hq : q.1 with
      | none =>
        have h0 := hnone 0 q (by simp) hq
        have hlen' : l.length = ws.length + s := by rw [hperm.length_eq]; simp [hlen]
        simp only [windowSize]
        rw [hlen']
        omega
      | some b =>
        have h0 := hsome 0 q b (by simp) hq
        have hc : l.countP (· < b) = ws.countP (· < b) + ins.countP (· < b) := by
          rw [hperm.countP_eq (fun x => decide (x < b)), List.countP_append]
        have hle := List.countP_le_length (p := fun x => decide (x < b)) (l := ins)
        simp only [windowSize]
        rw [hc]
        omega
    have hperm' : (insertWindow q.1 q.2 l).2.Perm (ws ++ (ins ++ [q.2])) := by
      refine ((insertWindow_perm q.1 q.2 l).trans ?_)
      refine ((List.perm_append_singleton q.2 l).symm.trans ?_)
      rw [← List.append_assoc]
      exact hperm.append_right [q.2]
    have htail := ih (s + 1) (insertWindow q.1 q.2 l).2 (ins ++ [q.2]) hperm' (by simp [hlen])
      (fun j p b hp hb => by
        have h1 := hsome (j + 1) p b (by simpa using hp) hb
        omega)
      (fun j p hp hn => by
        have h1 := hnone (j + 1) p (by simpa using hp) hn
        omega)
    simp only [insertBatch, List.length_cons]
    have hlen2 : qs.length * Nat.clog 2 T + Nat.clog 2 T = (qs.length + 1) * Nat.clog 2 T := by
      ring
    omega

/-- The slice a batch is made of: its `j`-th element (in insertion order) is the item of rank
`hi - j` of the rank-ordered list. -/
theorem getElem?_batch_slice {β : Type*} (l : List β) {lo hi : ℕ} (hlo : lo ≤ hi)
    (hhi : hi ≤ l.length) (j : ℕ) (hj : j < hi - lo) :
    (((l.drop lo).take (hi - lo)).reverse)[j]? = l[hi - 1 - j]? := by
  rw [List.getElem?_reverse (by rw [List.length_reverse, List.length_take]; omega)]
  rw [List.length_take, List.length_drop,
    show min (hi - lo) (l.length - lo) = hi - lo by omega]
  rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop]
  congr 1
  omega

/-! ### The Jacobsthal walk -/

/-- First rank of batch `k`: the number of items already in the chain when batch `k` starts. -/
def jacLo (M k : ℕ) : ℕ := min M (jacPred k)

/-- One past the last rank of batch `k`. -/
def jacHi (M k : ℕ) : ℕ := min M (jac k)

theorem jacLo_le_jacHi (M k : ℕ) : jacLo M k ≤ jacHi M k :=
  min_le_min_left M (jacPred_le_jac k)

theorem jacHi_le (M k : ℕ) : jacHi M k ≤ M := min_le_left M (jac k)

theorem jacLo_succ (M k : ℕ) : jacLo M (k + 1) = jacHi M k := rfl

/-- The items of batch `k` in insertion order: ranks `jacLo M k + 1 … jacHi M k`, the highest
rank first, so that inside the batch "rank plus items already inserted" stays constant. -/
def jacBatch (items : List (Option α × α)) (k : ℕ) : List (Option α × α) :=
  ((items.drop (jacLo items.length k)).take
    (jacHi items.length k - jacLo items.length k)).reverse

theorem jacBatch_length (items : List (Option α × α)) (k : ℕ) :
    (jacBatch items k).length = jacHi items.length k - jacLo items.length k := by
  rw [jacBatch, List.length_reverse, List.length_take, List.length_drop]
  have h1 := jacHi_le items.length k
  have h2 := jacLo_le_jacHi items.length k
  omega

theorem jacBatch_length_le (items : List (Option α × α)) (k : ℕ) :
    (jacBatch items k).length ≤ items.length := by
  rw [jacBatch_length]
  have := jacHi_le items.length k
  omega

/-- The `j`-th item of batch `k` in insertion order is the item of rank `jacHi M k - j`. -/
theorem jacBatch_getElem? (items : List (Option α × α)) (k : ℕ) {j : ℕ}
    (hj : j < jacHi items.length k - jacLo items.length k) :
    (jacBatch items k)[j]? = items[jacHi items.length k - 1 - j]? := by
  rw [jacBatch]
  have hlen : (((items.drop (jacLo items.length k)).take
      (jacHi items.length k - jacLo items.length k))).length
      = jacHi items.length k - jacLo items.length k := by
    rw [List.length_take, List.length_drop]
    have h1 := jacHi_le items.length k
    have h2 := jacLo_le_jacHi items.length k
    omega
  rw [List.getElem?_reverse (by rw [hlen]; omega), hlen, List.getElem?_take,
    if_pos (by omega), List.getElem?_drop]
  congr 1
  omega

theorem jacBatch_subset (items : List (Option α × α)) (k : ℕ) :
    ∀ q ∈ jacBatch items k, q ∈ items := by
  intro q hq
  have hs : List.Sublist (jacBatch items k) items := by
    rw [jacBatch]
    exact List.Sublist.reverse ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  exact hs.subset hq

/-- The batches tile the item list: batch `k` (in decreasing rank) together with everything
from `jacHi` on is exactly the part of the list from `jacLo` on. -/
theorem jacBatch_tile (items : List (Option α × α)) (k : ℕ) :
    List.Perm ((jacBatch items k).map Prod.snd ++
        (items.drop (jacHi items.length k)).map Prod.snd)
      ((items.drop (jacLo items.length k)).map Prod.snd) := by
  have hleh : jacLo items.length k ≤ jacHi items.length k := jacLo_le_jacHi _ _
  have hdrop : (items.drop (jacLo items.length k)).drop
      (jacHi items.length k - jacLo items.length k) = items.drop (jacHi items.length k) := by
    rw [List.drop_drop, show jacLo items.length k + (jacHi items.length k - jacLo items.length k)
      = jacHi items.length k by omega]
  have htile : (items.drop (jacLo items.length k)).take
        (jacHi items.length k - jacLo items.length k) ++ items.drop (jacHi items.length k)
      = items.drop (jacLo items.length k) := by
    rw [← hdrop, List.take_append_drop]
  have hmap : (jacBatch items k).map Prod.snd
      = ((((items.drop (jacLo items.length k)).take
          (jacHi items.length k - jacLo items.length k))).map Prod.snd).reverse := by
    rw [jacBatch, List.map_reverse]
  rw [hmap]
  refine (List.Perm.append_right _ (List.reverse_perm _)).trans ?_
  rw [← List.map_append, htile]

/-- Walk the batches `k, k+1, …`, inserting each into the chain. -/
def insertJacobsthal [LinearOrder α] (items : List (Option α × α)) :
    ℕ → ℕ → List α → ℕ × List α
  | 0, _, l => (0, l)
  | fuel + 1, k, l =>
    let r := insertBatch (jacBatch items k) l
    let r' := insertJacobsthal items fuel (k + 1) r.2
    (r.1 + r'.1, r'.2)

theorem insertJacobsthal_perm [LinearOrder α] (items : List (Option α × α)) :
    ∀ (fuel k : ℕ) (l : List α), items.length ≤ fuel + k →
      (insertJacobsthal items fuel k l).2.Perm
        (l ++ (items.drop (jacLo items.length k)).map Prod.snd) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k l hk
    have hM : jacLo items.length k = items.length := by
      have h1 : items.length ≤ k := by omega
      have h2 : k ≤ jacPred k := by
        cases k with
        | zero => exact Nat.le_refl 0
        | succ j => rw [jacPred_succ]; exact le_trans (by omega) (le_jac j)
      simp only [jacLo]
      omega
    rw [hM, List.drop_length, List.map_nil, List.append_nil]
    exact List.Perm.refl _
  | succ fuel ih =>
    intro k l hk
    have hth := ih (k + 1) (insertBatch (jacBatch items k) l).2 (by omega)
    rw [jacLo_succ] at hth
    refine (hth.trans ?_).trans (List.Perm.refl _)
    refine (List.Perm.append_right _ (insertBatch_perm (jacBatch items k) l)).trans ?_
    rw [List.append_assoc]
    exact List.Perm.append_left _ (jacBatch_tile items k)

theorem insertJacobsthal_sorted [LinearOrder α] (items : List (Option α × α)) :
    ∀ (fuel k : ℕ) (l : List α), l.Pairwise (· ≤ ·) →
      (∀ q ∈ items, ∀ b, q.1 = some b → q.2 ≤ b) →
      (insertJacobsthal items fuel k l).2.Pairwise (· ≤ ·) := by
  intro fuel
  induction fuel with
  | zero => intro k l hl _; exact hl
  | succ fuel ih =>
    intro k l hl hitems
    exact ih (k + 1) _ (insertBatch_sorted _ l hl
      (fun q hq b hb => hitems q (jacBatch_subset items k q hq) b hb)) hitems

/-- **The comparisons of the Jacobsthal walk.**  Batch `k` inserts `jacHi - jacLo` items and
each of them is searched for in a window of `jacHi + jacLo` slots — the `jacLo` winners below
its partner plus the items already in the chain — which is exactly the sum `jacInsertCostAux`
of `Jacobsthal.lean`. -/
theorem insertJacobsthal_count [LinearOrder α] (items : List (Option α × α)) (ws : List α) :
    ∀ (fuel k : ℕ) (l ins : List α),
      l.Perm (ws ++ ins) → ins.length = jacLo items.length k →
      (∀ (j : ℕ) (q : Option α × α) (b : α), items[j]? = some q → q.1 = some b →
        ws.countP (· < b) ≤ j) →
      (∀ (j : ℕ) (q : Option α × α), items[j]? = some q → q.1 = none → ws.length ≤ j) →
      (insertJacobsthal items fuel k l).1 ≤ jacInsertCostAux items.length fuel k := by
  intro fuel
  induction fuel with
  | zero => intro k l ins _ _ _ _; exact Nat.zero_le _
  | succ fuel ih =>
    intro k l ins hperm hlen hsome hnone
    have hleh : jacLo items.length k ≤ jacHi items.length k := jacLo_le_jacHi _ _
    have hhiM : jacHi items.length k ≤ items.length := jacHi_le _ _
    -- the batch costs `|batch| ⌈log₂ window⌉`
    have hbatch : (insertBatch (jacBatch items k) l).1 ≤
        (jacHi items.length k - jacLo items.length k)
          * Nat.clog 2 (jacLo items.length k + jacHi items.length k) := by
      have hcount := insertBatch_count ws (jacLo items.length k)
        (jacLo items.length k + jacHi items.length k) (jacBatch items k) l ins hperm hlen ?_ ?_
      · rwa [jacBatch_length] at hcount
      · intro j q b hjq hb
        by_cases hjn : j < jacHi items.length k - jacLo items.length k
        · rw [jacBatch_getElem? items k hjn] at hjq
          have h := hsome (jacHi items.length k - 1 - j) q b hjq hb
          omega
        · have hz : (jacBatch items k)[j]? = none := by
            rw [List.getElem?_eq_none_iff, jacBatch_length]
            omega
          rw [hz] at hjq
          exact absurd hjq (by simp)
      · intro j q hjq hn
        by_cases hjn : j < jacHi items.length k - jacLo items.length k
        · rw [jacBatch_getElem? items k hjn] at hjq
          have h := hnone (jacHi items.length k - 1 - j) q hjq hn
          omega
        · have hz : (jacBatch items k)[j]? = none := by
            rw [List.getElem?_eq_none_iff, jacBatch_length]
            omega
          rw [hz] at hjq
          exact absurd hjq (by simp)
    -- the tail of the walk
    have hperm' : (insertBatch (jacBatch items k) l).2.Perm
        (ws ++ (ins ++ (jacBatch items k).map Prod.snd)) := by
      refine (insertBatch_perm (jacBatch items k) l).trans ?_
      rw [← List.append_assoc]
      exact hperm.append_right _
    have hlen' : (ins ++ (jacBatch items k).map Prod.snd).length
        = jacLo items.length (k + 1) := by
      rw [List.length_append, hlen, jacBatch_length, jacLo_succ]
      omega
    have htail := ih (k + 1) (insertBatch (jacBatch items k) l).2
      (ins ++ (jacBatch items k).map Prod.snd) hperm' hlen' hsome hnone
    have hclog : min items.length (jacPred k) = jacLo items.length k := rfl
    have hclog2 : min items.length (jac k) = jacHi items.length k := rfl
    simp only [insertJacobsthal, jacInsertCostAux, hclog, hclog2]
    omega
