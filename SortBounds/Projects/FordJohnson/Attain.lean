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

/-! ### The insertion window of a chain -/

/-- A sorted chain: the part strictly below `b` is a prefix, so its length is the number of
elements below `b`.  (Only `≤` from `splitBelow_fst_length_le_countP` is needed for the upper
bound; the equality is what makes the window exact.) -/
theorem splitBelow_fst_length_eq_countP (b : ℕ) :
    ∀ l : List ℕ, l.Pairwise (· ≤ ·) → (splitBelow b l).1.length = l.countP (· < b) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro hs
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    by_cases h : c < b
    · rw [splitBelow, ite_eq_left h, List.length_cons, List.countP_cons,
        ite_eq_left (by simp [h]), ih htail]
    · rw [splitBelow, ite_eq_right h, List.length_nil, List.countP_cons,
        ite_eq_right (by simp [h]), Nat.add_zero]
      exact (countP_eq_zero_of_forall cs (fun x hx => by have := hhead x hx; omega)).symm

/-- Every element below the bound is counted: `countP` of a list all of whose elements are
below `b` is its length. -/
theorem countP_eq_length_of_forall_lt (b : ℕ) :
    ∀ l : List ℕ, (∀ x ∈ l, x < b) → l.countP (· < b) = l.length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro h
    rw [List.countP_cons, ite_eq_left (by simp [h c (by simp)]),
      ih (fun x hx => h x (List.mem_cons_of_mem c hx)), List.length_cons]

/-- The count of a bounded insertion whose element is below the whole chain. -/
theorem insertWindow_eq_clog_none (x : ℕ) (l : List ℕ) (h : ∀ a ∈ l, x ≤ a) :
    (insertWindow none x l).1 = Nat.clog 2 (l.length + 1) :=
  insertCount_eq_clog_of_forall_le x l h

/-- The count of a bounded insertion whose element is below every element of its window. -/
theorem insertWindow_eq_clog_some (b x : ℕ) (l : List ℕ) (hl : l.Pairwise (· ≤ ·))
    (h : ∀ a ∈ (splitBelow b l).1, x ≤ a) :
    (insertWindow (some b) x l).1 = Nat.clog 2 (l.countP (· < b) + 1) := by
  show (insertCount x (splitBelow b l).1).1 = Nat.clog 2 (l.countP (· < b) + 1)
  rw [insertCount_eq_clog_of_forall_le x (splitBelow b l).1 h,
    splitBelow_fst_length_eq_countP b l hl]

/-! ### One Jacobsthal batch, exactly -/

/-- **A batch of `jacHi - jacLo` insertions costs exactly `|batch| ⌈log₂ T⌉`.**  This is
`insertBatch_count` with its sole inequality turned into an equality: every item of the batch
is below the whole window it is searched for in (so the window has exactly `ws.countP (· < b)`
`+ s` elements, not fewer) and each search descends to the deepest leaf
(`insertCount_eq_clog_of_forall_le`).  The two `hsome`/`hnone` hypotheses are the equality
versions of the window bounds. -/
theorem insertBatch_eq (ws : List ℕ) (s T : ℕ) (batch : List (Option ℕ × ℕ)) (l ins : List ℕ)
    (hperm : l.Perm (ws ++ ins)) (hins : ins.length = s) (hsorted : l.Pairwise (· ≤ ·))
    (hins_ws : ∀ y ∈ ins, ∀ w ∈ ws, y < w)
    (hq_ws : ∀ q ∈ batch, ∀ w ∈ ws, q.2 < w)
    (hq_ins : ∀ q ∈ batch, ∀ y ∈ ins, q.2 ≤ y)
    (hq_le : ∀ q ∈ batch, ∀ b : ℕ, q.1 = some b → q.2 ≤ b)
    (hbound : ∀ (j : ℕ) (q : Option ℕ × ℕ) (b : ℕ), batch[j]? = some q → q.1 = some b → b ∈ ws)
    (hmono : batch.Pairwise (fun p q => q.2 ≤ p.2))
    (hsome : ∀ (j : ℕ) (q : Option ℕ × ℕ) (b : ℕ), batch[j]? = some q → q.1 = some b →
      ws.countP (· < b) + s + j + 1 = T)
    (hnone : ∀ (j : ℕ) (q : Option ℕ × ℕ), batch[j]? = some q → q.1 = none →
      ws.length + s + j + 1 = T) :
    (insertBatch batch l).1 = batch.length * Nat.clog 2 T := by
  induction batch generalizing l ins s with
  | nil => simp [insertBatch]
  | cons q qs ih =>
    obtain ⟨hq_mono, hqs_mono⟩ := List.pairwise_cons.mp hmono
    have hqmem : q ∈ q :: qs := List.mem_cons_self ..
    -- every element of the chain is at least the item about to be inserted
    have hw : ∀ a ∈ l, q.2 ≤ a := by
      intro a ha
      rcases List.mem_append.mp (hperm.mem_iff.mp ha) with h | h
      · exact le_of_lt (hq_ws q hqmem a h)
      · exact hq_ins q hqmem a h
    have hhead : (insertWindow q.1 q.2 l).1 = Nat.clog 2 T := by
      cases hq1 : q.1 with
      | none =>
        rw [insertWindow_eq_clog_none q.2 l hw, hperm.length_eq, List.length_append, hins,
          show ws.length + s + 1 = T from hnone 0 q (by simp) hq1]
      | some b =>
        have hwin : ∀ a ∈ (splitBelow b l).1, q.2 ≤ a := fun a ha =>
          hw a (by rw [← splitBelow_append b l]; exact List.mem_append_left _ ha)
        rw [insertWindow_eq_clog_some b q.2 l hsorted hwin]
        have hb : b ∈ ws := hbound 0 q b (by simp) hq1
        have hcp : l.countP (· < b) = ws.countP (· < b) + s := by
          rw [hperm.countP_eq (fun x => decide (x < b)), List.countP_append,
            countP_eq_length_of_forall_lt b ins (fun y hy => hins_ws y hy b hb), hins]
        rw [hcp, hsome 0 q b (by simp) hq1]
    -- the rest of the batch, on the extended chain
    have hperm' : (insertWindow q.1 q.2 l).2.Perm (ws ++ (ins ++ [q.2])) := by
      refine (insertWindow_perm q.1 q.2 l).trans ?_
      refine ((List.perm_append_singleton q.2 l).symm.trans ?_)
      rw [← List.append_assoc]
      exact hperm.append_right [q.2]
    have htail := ih (s + 1) _ (ins ++ [q.2]) hperm' (by simp [hins])
      (insertWindow_sorted q.1 q.2 l hsorted (fun b hb => hq_le q hqmem b hb))
      (fun y hy w hw' => by
        rcases List.mem_append.mp hy with h | h
        · exact hins_ws y h w hw'
        · rw [List.mem_singleton] at h
          subst h
          exact hq_ws q hqmem w hw')
      (fun q' hq' w hw' => hq_ws q' (List.mem_cons_of_mem q hq') w hw')
      (fun q' hq' y hy => by
        rcases List.mem_append.mp hy with h | h
        · exact hq_ins q' (List.mem_cons_of_mem q hq') y h
        · rw [List.mem_singleton] at h
          subst h
          exact hq_mono q' hq')
      (fun q' hq' b hb => hq_le q' (List.mem_cons_of_mem q hq') b hb)
      (fun j q' b hjq hb => hbound (j + 1) q' b (by simpa using hjq) hb)
      hqs_mono
      (fun j q' b hjq hb => by
        have h := hsome (j + 1) q' b (by simpa using hjq) hb
        omega)
      (fun j q' hjq hn => by
        have h := hnone (j + 1) q' (by simpa using hjq) hn
        omega)
    simp only [insertBatch, List.length_cons]
    rw [hhead, htail]
    ring

/-! ### The Jacobsthal walk, exactly -/

/-- **The insertion phase costs exactly `jacInsertCost`.**  `insertJacobsthal_count` bounds the
walk by `jacInsertCostAux`; here every item is below the whole window it is searched for in
(`hitem_ws`, `hmono`, `hcross`: item values decrease along the Jacobsthal order) and the bounds
are the chain elements themselves (`hcnt`, `hlast`), so each of the `|batch|` searches of batch
`k` faces exactly `jacLo + jacHi - 1` elements and the batch costs `|batch| ⌈log₂ (jacLo +
jacHi)⌉` (`insertBatch_eq`). -/
theorem insertJacobsthal_eq (items : List (Option ℕ × ℕ)) (ws : List ℕ)
    (hcnt : ∀ (j : ℕ) (q : Option ℕ × ℕ) (b : ℕ), items[j]? = some q → q.1 = some b →
      ws.countP (· < b) = j)
    (hlast : ∀ (j : ℕ) (q : Option ℕ × ℕ), items[j]? = some q → q.1 = none → j = ws.length)
    (hbound : ∀ (j : ℕ) (q : Option ℕ × ℕ) (b : ℕ), items[j]? = some q → q.1 = some b → b ∈ ws)
    (hitem_ws : ∀ q ∈ items, ∀ w ∈ ws, q.2 < w)
    (hitem_le : ∀ q ∈ items, ∀ b : ℕ, q.1 = some b → q.2 ≤ b)
    (hmono : ∀ k : ℕ, (jacBatch items k).Pairwise (fun p q => q.2 ≤ p.2))
    (hcross : ∀ (k k' : ℕ) (q p : Option ℕ × ℕ), k < k' → q ∈ jacBatch items k' →
      p ∈ jacBatch items k → q.2 ≤ p.2) :
    ∀ (fuel k : ℕ) (l ins : List ℕ), l.Perm (ws ++ ins) → ins.length = jacLo items.length k →
      l.Pairwise (· ≤ ·) → (∀ y ∈ ins, ∀ w ∈ ws, y < w) →
      (∀ y ∈ ins, ∀ (k' : ℕ), k ≤ k' → ∀ q ∈ jacBatch items k', q.2 ≤ y) →
      (insertJacobsthal items fuel k l).1 = jacInsertCostAux items.length fuel k := by
  intro fuel
  induction fuel with
  | zero => intro k l ins _ _ _ _ _; rfl
  | succ fuel ih =>
    intro k l ins hperm hlen hsorted hins_ws hins_q
    have hbl : (jacBatch items k).length
        = jacHi items.length k - jacLo items.length k := jacBatch_length items k
    have hmiss : ∀ j : ℕ, ¬ j < jacHi items.length k - jacLo items.length k →
        (jacBatch items k)[j]? = none := by
      intro j hjn
      rw [List.getElem?_eq_none_iff, hbl]
      omega
    have hsome : ∀ (j : ℕ) (q : Option ℕ × ℕ) (b : ℕ), (jacBatch items k)[j]? = some q →
        q.1 = some b → ws.countP (· < b) + jacLo items.length k + j + 1
          = jacLo items.length k + jacHi items.length k := by
      intro j q b hjq hb
      by_cases hjn : j < jacHi items.length k - jacLo items.length k
      · rw [jacBatch_getElem? items k hjn] at hjq
        have h := hcnt (jacHi items.length k - 1 - j) q b hjq hb
        omega
      · rw [hmiss j hjn] at hjq
        exact absurd hjq (by simp)
    have hnone' : ∀ (j : ℕ) (q : Option ℕ × ℕ), (jacBatch items k)[j]? = some q → q.1 = none →
        ws.length + jacLo items.length k + j + 1 = jacLo items.length k + jacHi items.length k := by
      intro j q hjq hn
      by_cases hjn : j < jacHi items.length k - jacLo items.length k
      · rw [jacBatch_getElem? items k hjn] at hjq
        have h := hlast (jacHi items.length k - 1 - j) q hjq hn
        omega
      · rw [hmiss j hjn] at hjq
        exact absurd hjq (by simp)
    have hbound' : ∀ (j : ℕ) (q : Option ℕ × ℕ) (b : ℕ), (jacBatch items k)[j]? = some q →
        q.1 = some b → b ∈ ws := by
      intro j q b hjq hb
      by_cases hjn : j < jacHi items.length k - jacLo items.length k
      · rw [jacBatch_getElem? items k hjn] at hjq
        exact hbound _ q b hjq hb
      · rw [hmiss j hjn] at hjq
        exact absurd hjq (by simp)
    have hbatch := insertBatch_eq ws (jacLo items.length k)
      (jacLo items.length k + jacHi items.length k) (jacBatch items k) l ins
      hperm hlen hsorted hins_ws
      (fun q hq w hw => hitem_ws q (jacBatch_subset items k q hq) w hw)
      (fun q hq y hy => hins_q y hy k le_rfl q hq)
      (fun q hq b hb => hitem_le q (jacBatch_subset items k q hq) b hb)
      hbound' (hmono k) hsome hnone'
    have hbatch' : (insertBatch (jacBatch items k) l).1
        = (jacHi items.length k - jacLo items.length k)
          * Nat.clog 2 (jacLo items.length k + jacHi items.length k) := by
      rw [hbatch, hbl]
    -- the rest of the walk, on the extended chain
    have hperm' : (insertBatch (jacBatch items k) l).2.Perm
        (ws ++ (ins ++ (jacBatch items k).map Prod.snd)) := by
      refine (insertBatch_perm (jacBatch items k) l).trans ?_
      rw [← List.append_assoc]
      exact hperm.append_right _
    have hlen' : (ins ++ (jacBatch items k).map Prod.snd).length
        = jacLo items.length (k + 1) := by
      rw [List.length_append, List.length_map, hlen, hbl, jacLo_succ]
      have := jacLo_le_jacHi items.length k
      omega
    have htail := ih (k + 1) _ (ins ++ (jacBatch items k).map Prod.snd) hperm' hlen'
      (insertBatch_sorted (jacBatch items k) l hsorted
        (fun q hq b hb => hitem_le q (jacBatch_subset items k q hq) b hb))
      (fun y hy w hw => by
        rcases List.mem_append.mp hy with h | h
        · exact hins_ws y h w hw
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
          exact hitem_ws q (jacBatch_subset items k q hq) w hw)
      (fun y hy k' hk' q hq => by
        rcases List.mem_append.mp hy with h | h
        · exact hins_q y h k' (le_trans (Nat.le_succ k) hk') q hq
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
          exact hcross k k' q p (by omega) hq hp)
    have hstep : (insertJacobsthal items (fuel + 1) k l).1
        = (insertBatch (jacBatch items k) l).1
          + (insertJacobsthal items fuel (k + 1) (insertBatch (jacBatch items k) l).2).1 := rfl
    rw [hstep, hbatch', htail]
    simp only [jacInsertCostAux, jacLo, jacHi]

/-! ### The insertion order as a function of the rank -/

/-- `jacPred k = jac (k-1)`: the first rank of batch `k` is the last rank of batch `k-1`. -/
theorem jacPred_eq_of_pos {k : ℕ} (hk : 0 < k) : jacPred k = jac (k - 1) := by
  cases k with
  | zero => omega
  | succ j => rw [jacPred_succ]

/-- Every rank lies in some batch, because `jac` dominates the identity. -/
theorem jacBatchOf_exists (j : ℕ) : ∃ k, j < jac k := ⟨j, by have := le_jac j; omega⟩

/-- **The batch holding rank `j`**: the least `k` with `j < jac k`, so that batch `k` holds the
ranks `jacPred k … jac k - 1`. -/
def jacBatchOf (j : ℕ) : ℕ := Nat.find (jacBatchOf_exists j)

theorem jacBatchOf_spec (j : ℕ) : j < jac (jacBatchOf j) := Nat.find_spec (jacBatchOf_exists j)

theorem jacBatchOf_le {j k : ℕ} (h : j < jac k) : jacBatchOf j ≤ k :=
  Nat.find_min' (jacBatchOf_exists j) h

/-- No rank is below the start of its own batch. -/
theorem jacPred_jacBatchOf_le (j : ℕ) : jacPred (jacBatchOf j) ≤ j := by
  rcases Nat.eq_zero_or_pos (jacBatchOf j) with h0 | h0
  · simp [h0, jacPred]
  · by_contra hcon
    have hp : j < jac (jacBatchOf j - 1) := by
      rw [← jacPred_eq_of_pos h0]
      omega
    have := jacBatchOf_le hp
    omega

/-- A rank is in the batch `k` exactly when `jacPred k ≤ j < jac k`. -/
theorem jacBatchOf_eq {j k : ℕ} (h1 : j < jac k) (h2 : jacPred k ≤ j) : jacBatchOf j = k := by
  refine le_antisymm (jacBatchOf_le h1) ?_
  rcases Nat.eq_zero_or_pos k with hk | hk
  · simp [hk]
  · by_contra hcon
    have hspec := jacBatchOf_spec j
    have h2' : jac (k - 1) ≤ j := by
      rw [← jacPred_eq_of_pos hk]
      exact h2
    have hmono : jac (jacBatchOf j) ≤ jac (k - 1) := jac_strictMono.monotone (by omega)
    omega

/-- `jacLo` is monotone in the batch index. -/
theorem jacLo_mono (M : ℕ) {k k' : ℕ} (h : k ≤ k') : jacLo M k ≤ jacLo M k' := by
  refine min_le_min_left M ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  · have hmono : jac (k - 1) ≤ jac (k' - 1) := jac_strictMono.monotone (by omega)
    rwa [jacPred_eq_of_pos hk, jacPred_eq_of_pos (by omega)]

/-- The batches tile the order: the largest window of batch `k` is still below the smallest
window of any later batch. -/
theorem jacHi_le_jacLo (M : ℕ) {k k' : ℕ} (h : k < k') : jacHi M k ≤ jacLo M k' :=
  le_trans (le_of_eq (jacLo_succ M k).symm) (jacLo_mono M (by omega))

/-! ### The values of the attaining input

With `M` items to insert into a chain whose winners form the block `[K+M, K+M+m)`, the item of
rank `j` gets the value `K + M - 1 - t(j)`, where `t(j) = jacLo + jacHi - 1 - j` counts the
items inserted before it in the Jacobsthal order: the values of the items decrease along that
order, so every item lies below everything already inserted and below every winner. -/

/-- `t(j)`: the number of items inserted before the item of rank `j`. -/
def attainT (M j : ℕ) : ℕ := jacLo M (jacBatchOf j) + jacHi M (jacBatchOf j) - 1 - j

/-- The value of the item of rank `j`, the `(t(j)+1)`-st smallest of the `M` values
`K … K + M - 1`. -/
def attainVal (M K j : ℕ) : ℕ := K + (M - 1 - attainT M j)

theorem jacLo_jacBatchOf_le (M j : ℕ) : jacLo M (jacBatchOf j) ≤ j :=
  (min_le_right _ _).trans (jacPred_jacBatchOf_le j)

theorem lt_jacHi_jacBatchOf (M j : ℕ) (hj : j < M) : j < jacHi M (jacBatchOf j) :=
  lt_min hj (jacBatchOf_spec j)

/-- `t(j)` is a position among the `M` items, so it is at most `M - 1`. -/
theorem attainT_le (M j : ℕ) (hj : j < M) : attainT M j ≤ M - 1 := by
  have h1 : jacLo M (jacBatchOf j) ≤ j := jacLo_jacBatchOf_le M j
  have h2 : j < jacHi M (jacBatchOf j) := lt_jacHi_jacBatchOf M j hj
  have h3 : jacHi M (jacBatchOf j) ≤ M := jacHi_le _ _
  simp only [attainT]
  omega

/-- Within one batch the values increase with the rank (the batch is inserted in decreasing
rank order). -/
theorem attainT_lt_of_batch_eq (M j j' : ℕ) (h : j < j')
    (hb : jacBatchOf j = jacBatchOf j') : attainT M j' < attainT M j := by
  simp only [attainT, hb]
  omega

/-- Across batches the values decrease: everything inserted in a later batch lies below
everything inserted in an earlier one. -/
theorem attainT_lt_of_batch_lt (M j j' : ℕ) (hj : j < M) (hj' : j' < M)
    (hb : jacBatchOf j < jacBatchOf j') : attainT M j < attainT M j' := by
  have h1 : jacLo M (jacBatchOf j) ≤ j := jacLo_jacBatchOf_le M j
  have h2 : j < jacHi M (jacBatchOf j) := lt_jacHi_jacBatchOf M j hj
  have h3 : jacLo M (jacBatchOf j') ≤ j' := jacLo_jacBatchOf_le M j'
  have h4 : j' < jacHi M (jacBatchOf j') := lt_jacHi_jacBatchOf M j' hj'
  have h5 : jacHi M (jacBatchOf j) ≤ jacLo M (jacBatchOf j') := jacHi_le_jacLo M hb
  simp only [attainT]
  omega

/-- The position `t` determines the rank: the batches partition the insertion order. -/
theorem attainT_inj (M j j' : ℕ) (hj : j < M) (hj' : j' < M)
    (h : attainT M j = attainT M j') : j = j' := by
  rcases lt_trichotomy (jacBatchOf j) (jacBatchOf j') with hb | hb | hb
  · have := attainT_lt_of_batch_lt M j j' hj hj' hb; omega
  · rcases lt_trichotomy j j' with hlt | hlt | hlt
    · have := attainT_lt_of_batch_eq M j j' hlt hb; omega
    · exact hlt
    · have := attainT_lt_of_batch_eq M j' j hlt hb.symm; omega
  · have := attainT_lt_of_batch_lt M j' j hj' hj hb; omega

/-- The values of the items are strictly between `K` and `K + M`. -/
theorem attainVal_lt (M K j : ℕ) (hj : j < M) : attainVal M K j < K + M := by
  have := attainT_le M j hj
  simp only [attainVal]
  omega

theorem attainVal_le_self (M K j : ℕ) : attainVal M K j ≤ K + M + j :=
  le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

/-- Within one batch, the values increase with the rank. -/
theorem attainVal_lt_of_batch_eq (M K j j' : ℕ) (hj : j < M) (hj' : j' < M) (h : j < j')
    (hb : jacBatchOf j = jacBatchOf j') : attainVal M K j < attainVal M K j' := by
  have h1 := attainT_lt_of_batch_eq M j j' h hb
  have h2 := attainT_le M j' hj'
  simp only [attainVal]
  omega

/-- Across batches the values decrease. -/
theorem attainVal_lt_of_batch_lt (M K j j' : ℕ) (hj : j < M) (hj' : j' < M)
    (hb : jacBatchOf j < jacBatchOf j') : attainVal M K j' < attainVal M K j := by
  have h1 := attainT_lt_of_batch_lt M j j' hj hj' hb
  have h2 := attainT_le M j hj
  simp only [attainVal]
  omega

/-- The item values are distinct. -/
theorem attainVal_inj (M K j j' : ℕ) (hj : j < M) (hj' : j' < M)
    (h : attainVal M K j = attainVal M K j') : j = j' := by
  have h1 := attainT_le M j hj
  have h2 := attainT_le M j' hj'
  simp only [attainVal] at h
  exact attainT_inj M j j' hj hj' (by omega)

end SortBounds.Projects.FordJohnson
