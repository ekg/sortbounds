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
  | succ j => rw [jacPred_succ]; simp

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

/-- The window of a batch never exceeds the whole chain of winners. -/
theorem jacHi_le_jac (M k : ℕ) : jacHi M k ≤ jac k := min_le_right _ _

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
theorem attainT_lt_of_batch_eq (M j j' : ℕ) (hj' : j' < M) (h : j < j')
    (hb : jacBatchOf j = jacBatchOf j') : attainT M j' < attainT M j := by
  have h2 : j' < jacHi M (jacBatchOf j') := lt_jacHi_jacBatchOf M j' hj'
  have h3 : jacLo M (jacBatchOf j) ≤ j := jacLo_jacBatchOf_le M j
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
  have e1 : jacLo M (jacBatchOf j) + jacHi M (jacBatchOf j) - 1 - j
      ≤ jacHi M (jacBatchOf j) - 1 := by
    rw [Nat.sub_le_iff_le_add]
    omega
  have e2 : jacLo M (jacBatchOf j')
      ≤ jacLo M (jacBatchOf j') + jacHi M (jacBatchOf j') - 1 - j' := by
    have heq : jacLo M (jacBatchOf j') + jacHi M (jacBatchOf j') - 1 - j'
        = jacLo M (jacBatchOf j') + (jacHi M (jacBatchOf j') - 1 - j') := by omega
    rw [heq]
    exact Nat.le_add_right _ _
  have e3 : jacHi M (jacBatchOf j) - 1 < jacLo M (jacBatchOf j') := by omega
  simp only [attainT]
  omega

/-- The position `t` determines the rank: the batches partition the insertion order. -/
theorem attainT_inj (M j j' : ℕ) (hj : j < M) (hj' : j' < M)
    (h : attainT M j = attainT M j') : j = j' := by
  rcases lt_trichotomy (jacBatchOf j) (jacBatchOf j') with hb | hb | hb
  · have := attainT_lt_of_batch_lt M j j' hj hj' hb; omega
  · rcases lt_trichotomy j j' with hlt | hlt | hlt
    · have := attainT_lt_of_batch_eq M j j' hj' hlt hb; omega
    · exact hlt
    · have := attainT_lt_of_batch_eq M j' j hj hlt hb.symm; omega
  · have := attainT_lt_of_batch_lt M j' j hj' hj hb; omega

/-- The values of the items are strictly between `K` and `K + M`. -/
theorem attainVal_lt (M K j : ℕ) (hj : j < M) : attainVal M K j < K + M := by
  have h := Nat.sub_le (M - 1) (attainT M j)
  simp only [attainVal]
  omega

theorem attainVal_le_add (M K j : ℕ) : attainVal M K j ≤ K + M := by
  have h := Nat.sub_le (M - 1) (attainT M j)
  simp only [attainVal]
  omega

theorem attainVal_le_self (M K j : ℕ) : attainVal M K j ≤ K + M + j :=
  le_trans (attainVal_le_add M K j) (Nat.le_add_right _ _)

/-- Within one batch, the values increase with the rank. -/
theorem attainVal_lt_of_batch_eq (M K j j' : ℕ) (hj : j < M) (hj' : j' < M) (h : j < j')
    (hb : jacBatchOf j = jacBatchOf j') : attainVal M K j < attainVal M K j' := by
  have h1 := attainT_lt_of_batch_eq M j j' hj' h hb
  have h2 := attainT_le M j hj
  have h3 : M - 1 - attainT M j < M - 1 - attainT M j' :=
    Nat.sub_lt_sub_left (by omega) h1
  simp only [attainVal]
  omega

/-- Across batches the values decrease. -/
theorem attainVal_lt_of_batch_lt (M K j j' : ℕ) (hj : j < M) (hj' : j' < M)
    (hb : jacBatchOf j < jacBatchOf j') : attainVal M K j' < attainVal M K j := by
  have h1 := attainT_lt_of_batch_lt M j j' hj hj' hb
  have h2 := attainT_le M j' hj'
  have h2' := attainT_le M j hj
  have h3 : M - 1 - attainT M j' < M - 1 - attainT M j :=
    Nat.sub_lt_sub_left (by omega) h1
  simp only [attainVal]
  omega

/-- The item values are distinct. -/
theorem attainVal_inj (M K j j' : ℕ) (hj : j < M) (hj' : j' < M)
    (h : attainVal M K j = attainVal M K j') : j = j' := by
  have h1 := attainT_le M j hj
  have h2 := attainT_le M j' hj'
  simp only [attainVal] at h
  exact attainT_inj M j j' hj hj' (by omega)

/-! ### The items and the chain of the attaining input -/

/-- The chain of winners: the block `[A, A+m)` in increasing order. -/
def attnChain (A m : ℕ) : List ℕ := (List.range m).map (fun i => A + i)

/-- The `M` items to insert, in rank order.  The item of rank `j < m` is the loser of the
rank-`j` winner `K+M+j`, searched for among the `j` winners below its own partner; an item of
rank `m` (possible only for an odd number of elements) is the unpaired element, with no
bound. -/
def attnItems (K m M : ℕ) : List (Option ℕ × ℕ) :=
  (List.range M).map (fun j => (if j < m then some (K + M + j) else none, attainVal M K j))

theorem attnItems_length (K m M : ℕ) : (attnItems K m M).length = M := by
  simp [attnItems]

theorem attnChain_length (A m : ℕ) : (attnChain A m).length = m := by
  simp [attnChain]

theorem attnChain_mem (A m j : ℕ) (hj : j < m) : A + j ∈ attnChain A m :=
  List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem attnChain_sorted (A m : ℕ) : (attnChain A m).Pairwise (· ≤ ·) := by
  simp only [attnChain]
  suffices H : ∀ m : ℕ, (List.range m).map (fun i => A + i) |>.Pairwise (· ≤ ·) from H m
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hy
    have h1 := List.mem_range.mp hi
    have h2 : i' = n := List.mem_singleton.mp hi'
    omega

theorem attnItems_getElem? (K m M j : ℕ) (hj : j < M) :
    (attnItems K m M)[j]? = some (if j < m then some (K + M + j) else none, attainVal M K j) := by
  simp [attnItems, hj]

/-- The chain `[A, A+m)` has exactly `j` elements below `A + j`. -/
theorem attnChain_countP (A m j : ℕ) (hj : j < m) :
    (attnChain A m).countP (· < A + j) = j := by
  suffices H : ∀ m j, j < m →
      (List.map (fun i => A + i) (List.range m)).countP (· < A + j) = j from H m j hj
  intro m
  induction m with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rw [List.range_succ, List.map_append, List.countP_append]
    have hz : List.countP (fun x => decide (x < A + j)) (List.map (fun i => A + i) [n]) = 0 := by
      have hc : ¬ (A + n < A + j) := by omega
      simp [hc]
    rw [hz, Nat.add_zero]
    rcases Nat.lt_or_ge j n with h | h
    · exact ih j h
    · have hje : j = n := by omega
      rw [hje]
      rw [countP_eq_length_of_forall_lt (A + n) (List.map (fun i => A + i) (List.range n))
        (fun x hx => by
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
          have := List.mem_range.mp hi
          omega), List.length_map, List.length_range]

/-- A rank inside a batch determines the batch. -/
theorem jacBatchOf_eq_of_mem {M j k : ℕ} (h1 : jacLo M k ≤ j) (h2 : j < jacHi M k) :
    jacBatchOf j = k := by
  have hk : j < jac k := lt_of_lt_of_le h2 (jacHi_le_jac M k)
  have hM : j < M := lt_of_lt_of_le h2 (jacHi_le M k)
  refine jacBatchOf_eq hk ?_
  by_contra hcon
  have hjacPred : j < jacPred k := by omega
  by_cases hle : jacPred k ≤ M
  · have hmin : jacLo M k = jacPred k := by
      simp only [jacLo, min_def]
      split <;> omega
    omega
  · have hmin : jacLo M k = M := by
      simp only [jacLo, min_def]
      split <;> omega
    omega

theorem jacBatch_attnItems_length (K m M k : ℕ) :
    (jacBatch (attnItems K m M) k).length = jacHi M k - jacLo M k := by
  rw [jacBatch_length, attnItems_length]

/-- The `i`-th item of batch `k`, in insertion order: its value is the value of the item of
rank `jacHi - 1 - i`. -/
theorem jacBatch_attnItems_getElem? (K m M k i : ℕ) (hi : i < jacHi M k - jacLo M k) :
    (jacBatch (attnItems K m M) k)[i]?
      = some (if jacHi M k - 1 - i < m then some (K + M + (jacHi M k - 1 - i)) else none,
          attainVal M K (jacHi M k - 1 - i)) := by
  have hget : (jacBatch (attnItems K m M) k)[i]?
      = (attnItems K m M)[jacHi (attnItems K m M).length k - 1 - i]? :=
    jacBatch_getElem? (attnItems K m M) k (by rwa [attnItems_length])
  rw [attnItems_length K m M] at hget
  have hlt : jacHi M k - 1 - i < M := by
    have := jacHi_le M k
    omega
  rw [attnItems_getElem? K m M _ hlt] at hget
  exact hget

theorem jacBatch_attnItems_getElem (K m M k i : ℕ)
    (hi : i < (jacBatch (attnItems K m M) k).length) :
    (jacBatch (attnItems K m M) k)[i]
      = (if jacHi M k - 1 - i < m then some (K + M + (jacHi M k - 1 - i)) else none,
          attainVal M K (jacHi M k - 1 - i)) := by
  have hi' : i < jacHi M k - jacLo M k := by
    rw [jacBatch_attnItems_length] at hi; exact hi
  have hget := jacBatch_attnItems_getElem? K m M k i hi'
  rw [List.getElem?_eq_getElem hi] at hget
  exact Option.some.inj hget

/-- The index, among the items, of the `i`-th item of batch `k` lies in batch `k`. -/
theorem jacBatchOf_attnItems (M k i : ℕ) (hi : i < jacHi M k - jacLo M k) :
    jacBatchOf (jacHi M k - 1 - i) = k := by
  have h1 : jacLo M k ≤ jacHi M k - 1 - i := by omega
  have h2 : jacHi M k - 1 - i < jacHi M k := by omega
  exact jacBatchOf_eq_of_mem (k := k) h1 h2

/-- Inside one batch an item inserted later has a smaller value: the batch is inserted in
decreasing rank order. -/
theorem attnItems_mono (K m M k : ℕ) :
    (jacBatch (attnItems K m M) k).Pairwise (fun p q => q.2 ≤ p.2) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hlt
  have hi' : i < jacHi M k - jacLo M k := by
    rw [jacBatch_attnItems_length K m M k] at hi; exact hi
  have hj' : j < jacHi M k - jacLo M k := by
    rw [jacBatch_attnItems_length K m M k] at hj; exact hj
  rw [jacBatch_attnItems_getElem K m M k j hj, jacBatch_attnItems_getElem K m M k i hi]
  have hbi : jacBatchOf (jacHi M k - 1 - i) = k := jacBatchOf_attnItems M k i hi'
  have hbj : jacBatchOf (jacHi M k - 1 - j) = k := jacBatchOf_attnItems M k j hj'
  have hM : jacHi M k - 1 - j < M := by have := jacHi_le M k; omega
  have hM' : jacHi M k - 1 - i < M := by have := jacHi_le M k; omega
  exact le_of_lt (attainVal_lt_of_batch_eq M K _ _ hM hM' (by omega) (by rw [hbj, hbi]))

/-- An item of a later batch has a smaller value than an item of an earlier batch: the batches
are inserted in increasing order. -/
theorem attnItems_cross (K m M k k' : ℕ) (hkk : k < k') :
    ∀ (q p : Option ℕ × ℕ), q ∈ jacBatch (attnItems K m M) k' →
      p ∈ jacBatch (attnItems K m M) k → q.2 ≤ p.2 := by
  intro q p hq hp
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
  have hil : i < (jacBatch (attnItems K m M) k').length := by
    by_contra hcon
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at hi
    exact absurd hi (by simp)
  have hjl : j < (jacBatch (attnItems K m M) k).length := by
    by_contra hcon
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at hj
    exact absurd hj (by simp)
  have hi' : i < jacHi M k' - jacLo M k' := by
    rw [jacBatch_attnItems_length K m M k'] at hil; exact hil
  have hj' : j < jacHi M k - jacLo M k := by
    rw [jacBatch_attnItems_length K m M k] at hjl; exact hjl
  have hq2 : q = (if jacHi M k' - 1 - i < m then some (K + M + (jacHi M k' - 1 - i)) else none,
      attainVal M K (jacHi M k' - 1 - i)) := by
    rw [List.getElem?_eq_getElem hil] at hi
    rw [jacBatch_attnItems_getElem K m M k' i hil] at hi
    exact (Option.some.inj hi).symm
  have hp2 : p = (if jacHi M k - 1 - j < m then some (K + M + (jacHi M k - 1 - j)) else none,
      attainVal M K (jacHi M k - 1 - j)) := by
    rw [List.getElem?_eq_getElem hjl] at hj
    rw [jacBatch_attnItems_getElem K m M k j hjl] at hj
    exact (Option.some.inj hj).symm
  have hbi : jacBatchOf (jacHi M k - 1 - j) = k := jacBatchOf_attnItems M k j hj'
  have hbi' : jacBatchOf (jacHi M k' - 1 - i) = k' := jacBatchOf_attnItems M k' i hi'
  have hM : jacHi M k - 1 - j < M := by have := jacHi_le M k; omega
  have hM' : jacHi M k' - 1 - i < M := by have := jacHi_le M k'; omega
  rw [hq2, hp2]
  exact le_of_lt (attainVal_lt_of_batch_lt M K _ _ hM hM' (by rw [hbi, hbi']; exact hkk))

/-! ### The insertion phase attains `jacInsertCost` -/

/-- **The Jacobsthal walk on the canonical items costs exactly `jacInsertCost`**: the `M` items
`attnItems K m M` inserted into the chain `[K+M, K+M+m)` (all of them below every winner, and
decreasing along the insertion order) make every search of the walk a deepest-path search in a
window of exactly `jacLo + jacHi - 1` elements. -/
theorem insertJacobsthal_attnItems (K m M : ℕ) (hmM : m ≤ M) (hMm : M ≤ m + 1) :
    (insertJacobsthal (attnItems K m M) M 0 (attnChain (K + M) m)).1 = jacInsertCost M := by
  have hget : ∀ j : ℕ, j < m → (attnItems K m M)[j]?
      = some (some (K + M + j), attainVal M K j) := by
    intro j hj
    rw [attnItems_getElem? K m M j (by omega), ite_eq_left hj]
  have hmemy : ∀ j : ℕ, j < M → ¬ j < m → j = m := by
    intro j hj hjm
    omega
  have hnoneq : ∀ j : ℕ, ¬ j < M → (attnItems K m M)[j]? = none := by
    intro j hj
    rw [List.getElem?_eq_none_iff, attnItems_length]
    omega
  have hcnt : ∀ (j : ℕ) (q : Option ℕ × ℕ) (b : ℕ), (attnItems K m M)[j]? = some q →
      q.1 = some b → (attnChain (K + M) m).countP (· < b) = j := by
    intro j q b hjq hb
    by_cases hjM : j < M
    · by_cases hj : j < m
      · rw [hget j hj] at hjq
        have hq : q = (some (K + M + j), attainVal M K j) := (Option.some.inj hjq).symm
        have hb' : b = K + M + j := by rw [hq] at hb; exact (Option.some.inj hb).symm
        rw [hb']
        exact attnChain_countP (K + M) m j hj
      · rw [attnItems_getElem? K m M j hjM, ite_eq_right hj] at hjq
        have hq : q.1 = none := (congrArg Prod.fst (Option.some.inj hjq)).symm
        rw [hq] at hb
        exact absurd hb (by simp)
    · rw [hnoneq j hjM] at hjq
      exact absurd hjq (by simp)
  have hnone : ∀ (j : ℕ) (q : Option ℕ × ℕ), (attnItems K m M)[j]? = some q → q.1 = none →
      j = (attnChain (K + M) m).length := by
    intro j q hjq hn
    by_cases hjM : j < M
    · by_cases hj : j < m
      · rw [hget j hj] at hjq
        have hq : q = (some (K + M + j), attainVal M K j) := (Option.some.inj hjq).symm
        rw [hq] at hn
        exact absurd hn (by simp)
      · rw [attnChain_length]
        exact hmemy j hjM hj
    · rw [hnoneq j hjM] at hjq
      exact absurd hjq (by simp)
  have hbound : ∀ (j : ℕ) (q : Option ℕ × ℕ) (b : ℕ), (attnItems K m M)[j]? = some q →
      q.1 = some b → b ∈ attnChain (K + M) m := by
    intro j q b hjq hb
    by_cases hjM : j < M
    · by_cases hj : j < m
      · rw [hget j hj] at hjq
        have hq : q = (some (K + M + j), attainVal M K j) := (Option.some.inj hjq).symm
        have hb' : b = K + M + j := by rw [hq] at hb; exact (Option.some.inj hb).symm
        rw [hb']
        exact attnChain_mem (K + M) m j hj
      · rw [attnItems_getElem? K m M j hjM, ite_eq_right hj] at hjq
        have hq : q.1 = none := (congrArg Prod.fst (Option.some.inj hjq)).symm
        rw [hq] at hb
        exact absurd hb (by simp)
    · rw [hnoneq j hjM] at hjq
      exact absurd hjq (by simp)
  have hitem_ws : ∀ q ∈ attnItems K m M, ∀ w ∈ attnChain (K + M) m, q.2 < w := by
    intro q hq w hw
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    have hj' : j < M := List.mem_range.mp hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have h := attainVal_lt M K j hj'
    simp only
    omega
  have hitem_le : ∀ q ∈ attnItems K m M, ∀ b : ℕ, q.1 = some b → q.2 ≤ b := by
    intro q hq b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    have hj' : j < M := List.mem_range.mp hj
    by_cases hjm : j < m
    · rw [ite_eq_left hjm] at hb
      rw [(Option.some.inj hb).symm]
      exact attainVal_le_self M K j
    · rw [ite_eq_right hjm] at hb
      exact absurd hb (by simp)
  have hwk := insertJacobsthal_eq (attnItems K m M) (attnChain (K + M) m) hcnt hnone hbound
    hitem_ws hitem_le (attnItems_mono K m M)
    (fun k k' q p hkk => attnItems_cross K m M k k' hkk q p)
    M 0 (attnChain (K + M) m) [] (by simp) (by simp [jacLo, jacPred])
    (attnChain_sorted _ _) (by simp) (by simp)
  rw [attnItems_length] at hwk
  rw [hwk]
  rfl

/-- **The insertion phase of merge-insertion attains its bound**: there are `M` items and a
chain of winners on which `insertJacobsthal` spends exactly `jacInsertCost M` comparisons.  So
`jacInsertCost` is the worst case of the insertion phase, not only an upper bound. -/
theorem jacInsertCost_attains (M K : ℕ) :
    ∃ items : List (Option ℕ × ℕ), items.length = M ∧
      (insertJacobsthal items M 0 (attnChain (K + M) M)).1 = jacInsertCost M :=
  ⟨attnItems K M M, attnItems_length K M M, insertJacobsthal_attnItems K M M le_rfl (by omega)⟩

/-! ### The list of pairs, read back by `pairUp` -/

/-- `pairUp` on an interleaved list of `(loser, winner)` pairs recovers the winners in order and
the losers alongside them. -/
theorem pairUp_flatMap_pairs (W : List ℕ) (f : ℕ → ℕ) (h : ∀ w ∈ W, f w < w) :
    pairUp (W.flatMap (fun w => [f w, w])) = (W, W.map f, none) := by
  induction W with
  | nil => rfl
  | cons w Ws ih =>
    have hw : f w < w := h w (by simp)
    have hne : ¬ w ≤ f w := by omega
    have htail := ih (fun x hx => h x (by simp [hx]))
    have hshape : ((w :: Ws).flatMap (fun w => [f w, w]))
        = f w :: w :: Ws.flatMap (fun w => [f w, w]) := by
      simp [List.flatMap_cons]
    rw [hshape, pairUp_cons_of_not_le (f w) w _ hne, htail]
    simp

/-- The same with an unpaired element at the end. -/
theorem pairUp_flatMap_pairs_cons (W : List ℕ) (f : ℕ → ℕ) (h : ∀ w ∈ W, f w < w) (u : ℕ) :
    pairUp (W.flatMap (fun w => [f w, w]) ++ [u]) = (W, W.map f, some u) := by
  induction W with
  | nil => rfl
  | cons w Ws ih =>
    have hw : f w < w := h w (by simp)
    have hne : ¬ w ≤ f w := by omega
    have htail := ih (fun x hx => h x (by simp [hx]))
    have hshape : ((w :: Ws).flatMap (fun w => [f w, w]) ++ [u])
        = f w :: w :: (Ws.flatMap (fun w => [f w, w]) ++ [u]) := by
      simp [List.flatMap_cons]
    rw [hshape, pairUp_cons_of_not_le (f w) w _ hne, htail]
    simp

theorem flatMap_pairs_length (W : List ℕ) (f : ℕ → ℕ) :
    (W.flatMap (fun w => [f w, w])).length = 2 * W.length := by
  induction W with
  | nil => rfl
  | cons w Ws ih =>
    have hshape : ((w :: Ws).flatMap (fun w => [f w, w]))
        = f w :: w :: Ws.flatMap (fun w => [f w, w]) := by
      simp [List.flatMap_cons]
    rw [hshape, List.length_cons, List.length_cons, ih, List.length_cons]
    omega

theorem mem_flatMap_pairs (W : List ℕ) (f : ℕ → ℕ) (x : ℕ) :
    x ∈ W.flatMap (fun w => [f w, w]) ↔ ∃ w ∈ W, x = f w ∨ x = w := by
  simp [List.mem_flatMap]

/-- The interleaved list has no repeats when the losers are all below the winners and distinct
among themselves. -/
theorem nodup_flatMap_pairs (W : List ℕ) (f : ℕ → ℕ) (A : ℕ) (hnd : W.Nodup)
    (hbelow : ∀ w ∈ W, f w < A) (habove : ∀ w ∈ W, A ≤ w)
    (hinj : ∀ w ∈ W, ∀ w' ∈ W, f w = f w' → w = w') :
    (W.flatMap (fun w => [f w, w])).Nodup := by
  induction W with
  | nil => exact List.nodup_nil
  | cons w Ws ih =>
    obtain ⟨hwnd, hWs⟩ := List.nodup_cons.mp hnd
    have hfw : f w < A := hbelow w (by simp)
    have hwA : A ≤ w := habove w (by simp)
    have hne : f w ≠ w := by omega
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨by simp [hne], ?_, ?_⟩
    · exact ih hWs (fun x hx => hbelow x (by simp [hx])) (fun x hx => habove x (by simp [hx]))
        (fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy]))
    · intro x hx y hy
      rw [mem_flatMap_pairs] at hy
      obtain ⟨v, hv, hvy⟩ := hy
      rcases List.mem_cons.mp hx with hfx | hfx
      · intro he
        rw [hfx] at he
        rcases hvy with hyv | hyv
        · rw [hyv] at he
          have hwv : w = v := hinj w (by simp) v (by simp [hv]) he
          exact hwnd (hwv ▸ hv)
        · rw [hyv] at he
          have h1 : f v < A := hbelow v (by simp [hv])
          have h2 : A ≤ v := habove v (by simp [hv])
          omega
      · intro he
        have hxw : x = w := List.mem_singleton.mp hfx
        rw [hxw] at he
        rcases hvy with hyv | hyv
        · rw [hyv] at he
          have h1 : f v < A := hbelow v (by simp [hv])
          have h2 : A ≤ w := hwA
          omega
        · rw [hyv] at he
          exact hwnd (he ▸ hv)

/-- The interleaved list consists exactly of the winners and the losers. -/
theorem flatMap_pairs_mem_range (W : List ℕ) (f : ℕ → ℕ) (A : ℕ)
    (hbelow : ∀ w ∈ W, f w < A) (habove : ∀ w ∈ W, A ≤ w) {x : ℕ}
    (hx : x ∈ W.flatMap (fun w => [f w, w])) : x < A ∨ A ≤ x := by
  rw [mem_flatMap_pairs] at hx
  obtain ⟨w, hw, hxw | hxw⟩ := hx
  · exact Or.inl (hxw ▸ hbelow w hw)
  · exact Or.inr (hxw ▸ habove w hw)

/-! ### The winner list is a block of values -/

theorem nodup_range_map_add (A m : ℕ) : ((List.range m).map (fun j => A + j)).Nodup := by
  refine List.Nodup.map ?_ List.nodup_range
  intro a b hab
  simp only at hab
  omega

theorem pairwise_lt_range_map_add (A m : ℕ) :
    ((List.range m).map (fun j => A + j)).Pairwise (· < ·) := by
  refine List.Pairwise.map _ ?_ (List.pairwise_lt_range (n := m))
  intro a b hab
  have h : A + a < A + b := Nat.add_lt_add_left hab A
  simpa using h

/-- A `≤`-sorted list without repeats is `<`-sorted. -/
theorem pairwise_lt_of_pairwise_le_of_nodup (l : List ℕ) (h1 : l.Pairwise (· ≤ ·))
    (h2 : l.Nodup) : l.Pairwise (· < ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    rw [List.pairwise_cons] at h1 ⊢
    obtain ⟨h1a, h1t⟩ := h1
    obtain ⟨h2a, h2t⟩ := List.nodup_cons.mp h2
    exact ⟨fun x hx => lt_of_le_of_ne (h1a x hx) (fun he => h2a (he ▸ hx)), ih h1t h2t⟩

/-- **A list of `m` distinct values in `[A, A+m)` is a permutation of that block.** -/
theorem perm_range_of_nodup_in_range (l : List ℕ) (A m : ℕ) (hlen : l.length = m)
    (hnd : l.Nodup) (h : ∀ x ∈ l, A ≤ x ∧ x < A + m) :
    l.Perm ((List.range m).map (fun j => A + j)) := by
  have hnd' : ((List.range m).map (fun j => A + j)).Nodup := nodup_range_map_add A m
  have hsub : l.toFinset ⊆ ((List.range m).map (fun j => A + j)).toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    obtain ⟨h1, h2⟩ := h x hx
    exact List.mem_map.mpr ⟨x - A, List.mem_range.mpr (by omega), by omega⟩
  have hcard : ((List.range m).map (fun j => A + j)).toFinset.card ≤ l.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd', List.toFinset_card_of_nodup hnd, hlen]
    simp
  have hfin : l.toFinset = ((List.range m).map (fun j => A + j)).toFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : ∀ x, x ∈ l ↔ x ∈ (List.range m).map (fun j => A + j) := by
    intro x
    rw [← List.mem_toFinset, hfin, List.mem_toFinset]
  refine List.perm_iff_count.mpr (fun x => ?_)
  by_cases hx : x ∈ l
  · rw [List.count_eq_one_of_mem hnd hx, List.count_eq_one_of_mem hnd' ((hmem x).mp hx)]
  · rw [List.count_eq_zero_of_not_mem hx,
      List.count_eq_zero_of_not_mem (fun hc => hx ((hmem x).mpr hc))]

/-! ### Sorting the pairs of the winners -/

/-- **Sorting the pairs of a permuted block reproduces the block.**  The pairs of the winner
list, ordered by winner, are the pairs of the block in increasing order: the keys are distinct,
so the sorted order is unique. -/
theorem sortPairs_map_eq (W : List ℕ) (f : ℕ → ℕ) (A m : ℕ)
    (hW : W.Perm ((List.range m).map (fun j => A + j))) :
    sortPairs (W.map (fun w => (w, f w))) = (List.range m).map (fun j => (A + j, f (A + j))) := by
  have hperm : (W.map (fun w => (w, f w))).Perm
      ((List.range m).map (fun j => (A + j, f (A + j)))) := by
    rw [show (List.range m).map (fun j => (A + j, f (A + j)))
        = ((List.range m).map (fun j => A + j)).map (fun a => (a, f a)) from by
      rw [List.map_map]; rfl]
    exact hW.map _
  have hR : ((List.range m).map (fun j => (A + j, f (A + j)))).Pairwise
      (fun p q => p.1 < q.1) := by
    rw [show (List.range m).map (fun j => (A + j, f (A + j)))
        = ((List.range m).map (fun j => A + j)).map (fun a => (a, f a)) from by
      rw [List.map_map]; rfl]
    exact List.Pairwise.map _ (fun a b hab => hab) (pairwise_lt_range_map_add A m)
  have hsP : (sortPairs (W.map (fun w => (w, f w)))).Perm
      ((List.range m).map (fun j => (A + j, f (A + j)))) :=
    (sortPairs_perm _).trans hperm
  have hRnd : ((List.range m).map (fun j => (A + j, f (A + j)))).map Prod.fst |>.Nodup :=
    (List.Pairwise.map Prod.fst (fun a b h => h) hR).nodup
  have hnod : ((sortPairs (W.map (fun w => (w, f w)))).map Prod.fst).Nodup :=
    ((hsP.map Prod.fst).nodup_iff).mpr hRnd
  have hlt : ((sortPairs (W.map (fun w => (w, f w)))).map Prod.fst).Pairwise (· < ·) :=
    pairwise_lt_of_pairwise_le_of_nodup _
      (List.Pairwise.map Prod.fst (fun a b h => h) (sortPairs_pairwise _)) hnod
  have hsP' : (sortPairs (W.map (fun w => (w, f w)))).Pairwise (fun p q => p.1 < q.1) :=
    List.pairwise_map.mp hlt
  have _inst : Std.Antisymm (fun p q : ℕ × ℕ => p.1 < q.1) :=
    ⟨fun a b h1 h2 => absurd h1 (by omega)⟩
  exact hsP.eq_of_pairwise' hsP' hR

/-! ### The attaining input -/

set_option linter.unusedVariables false in
/-- **The attaining input of length `n`**: the winners are an attaining list of length `n/2`
scaled into the block `[K+M, K+M+m)` with `M = ⌈n/2⌉`, and the `M` items to insert are the
values `K … K+M-1` in the order that makes the Jacobsthal walk insert them decreasingly. -/
def attnList : ℕ → ℕ → List ℕ
  | 0, _ => []
  | 1, K => [K]
  | t + 2, K =>
    let m := (t + 2) / 2
    let M := (t + 3) / 2
    (attnList m (K + M)).flatMap (fun w => [attainVal M K (w - (K + M)), w]) ++
      (if (t + 2) % 2 = 1 then [attainVal M K m] else [])
termination_by n K => n

theorem attnList_succ_succ (t K : ℕ) :
    attnList (t + 2) K
      = (attnList ((t + 2) / 2) (K + (t + 3) / 2)).flatMap
          (fun w => [attainVal ((t + 3) / 2) K (w - (K + (t + 3) / 2)), w]) ++
        (if (t + 2) % 2 = 1 then [attainVal ((t + 3) / 2) K ((t + 2) / 2)] else []) := by
  rw [attnList]

/-- The canonical list of items, written as the pairs of the block plus the unpaired item:
this is the shape `insertItems` produces. -/
theorem range_attnItems (K m M : ℕ) (hmM : m ≤ M) (hMm : M ≤ m + 1) :
    (List.range m).map (fun j => (some (K + M + j), attainVal M K j)) ++
        (if m < M then [(none, attainVal M K m)] else []) = attnItems K m M := by
  rcases Nat.eq_or_lt_of_le hmM with heq | hlt
  · subst heq
    rw [ite_eq_right (by omega : ¬ m < m), List.append_nil, attnItems]
    refine List.map_congr_left ?_
    intro j hj
    rw [List.mem_range] at hj
    rw [ite_eq_left hj]
  · have hM' : M = m + 1 := by omega
    subst hM'
    rw [ite_eq_left (by omega : m < m + 1), attnItems, List.range_succ, List.map_append,
      List.map_cons, List.map_nil]
    have hkey : (List.map
        (fun j => ((if j < m then some (K + (m + 1) + j) else none), attainVal (m + 1) K j))
        (List.range m))
        = (List.map (fun j => (some (K + (m + 1) + j), attainVal (m + 1) K j)) (List.range m)) := by
      refine List.map_congr_left ?_
      intro j hj
      rw [List.mem_range] at hj
      rw [ite_eq_left hj]
    rw [hkey, ite_eq_right (by omega : ¬ m < m)]

/-- **The items and the chain `fjSortJ` builds on `attnList (t+2) K`** are the canonical ones. -/
theorem pairUp_attnList (t K : ℕ)
    (hW : ∀ w ∈ attnList ((t + 2) / 2) (K + (t + 3) / 2),
      K + (t + 3) / 2 ≤ w ∧ w - (K + (t + 3) / 2) < (t + 3) / 2) :
    pairUp (attnList (t + 2) K)
      = (attnList ((t + 2) / 2) (K + (t + 3) / 2),
          (attnList ((t + 2) / 2) (K + (t + 3) / 2)).map
            (fun w => attainVal ((t + 3) / 2) K (w - (K + (t + 3) / 2))),
          if (t + 2) % 2 = 1 then some (attainVal ((t + 3) / 2) K ((t + 2) / 2)) else none) := by
  rw [attnList_succ_succ]
  by_cases hodd : (t + 2) % 2 = 1
  · rw [ite_eq_left hodd, ite_eq_left hodd]
    refine pairUp_flatMap_pairs_cons _ _ ?_ _
    intro w hw
    have h1 := (hW w hw).1
    have h2 := attainVal_lt ((t + 3) / 2) K (w - (K + (t + 3) / 2)) (hW w hw).2
    omega
  · rw [ite_eq_right hodd, ite_eq_right hodd, List.append_nil]
    refine pairUp_flatMap_pairs _ _ ?_
    intro w hw
    have h1 := (hW w hw).1
    have h2 := attainVal_lt ((t + 3) / 2) K (w - (K + (t + 3) / 2)) (hW w hw).2
    omega

/-- Zipping a list with its own image. -/
theorem zip_map_self (W : List ℕ) (f : ℕ → ℕ) :
    W.zip (W.map f) = W.map (fun a => (a, f a)) := by
  induction W with
  | nil => rfl
  | cons w Ws ih => simp [ih]

theorem attainVal_ge (M K j : ℕ) : K ≤ attainVal M K j := by
  simp only [attainVal]
  exact Nat.le_add_right _ _

/-- The pool values of the attaining input, in rank order, are distinct and lie in `[K, K+M)`. -/
theorem nodup_range_attainVal (M K : ℕ) :
    ((List.range M).map (fun j => attainVal M K j)).Nodup := by
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro a ha b hb hab
  rw [List.mem_range] at ha hb
  exact attainVal_inj M K a b ha hb hab

theorem attainVal_mem_range (M K j : ℕ) (hj : j < M) :
    K ≤ attainVal M K j ∧ attainVal M K j < K + M :=
  ⟨attainVal_ge M K j, attainVal_lt M K j hj⟩

/-- **The attaining input has all four properties.** -/
theorem attnList_spec (n : ℕ) : ∀ K : ℕ,
    (attnList n K).Nodup ∧ (attnList n K).length = n ∧
      (∀ x ∈ attnList n K, K ≤ x ∧ x < K + n) ∧
      (fjSortJ (attnList n K)).1 = fjCountJ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K
    match n with
    | 0 =>
      refine ⟨by simp [attnList], by simp [attnList], by simp [attnList], ?_⟩
      rw [fjCountJ_eq_zero 0 (by omega)]
      simp [attnList, fjSortJ]
    | 1 =>
      refine ⟨by simp [attnList], by simp [attnList], ?_, ?_⟩
      · intro x hx
        rw [attnList] at hx
        rw [List.mem_singleton] at hx
        omega
      · rw [fjCountJ_eq_zero 1 (by omega)]
        simp [attnList, fjSortJ]
    | t + 2 =>
      obtain ⟨hWnd, hWlen, hWrange, hWcost⟩ := ih ((t + 2) / 2) (by omega) (K + (t + 3) / 2)
      have hltA : ∀ w ∈ attnList ((t + 2) / 2) (K + (t + 3) / 2),
          K + (t + 3) / 2 ≤ w ∧ w - (K + (t + 3) / 2) < (t + 3) / 2 := by
        intro w hw
        obtain ⟨h1, h2⟩ := hWrange w hw
        exact ⟨h1, by omega⟩
      have hsplit : (t + 3) / 2 = (t + 2) / 2 + (t + 2) % 2 := by omega
      have hlenL : (List.flatMap
          (fun w => [attainVal ((t + 3) / 2) K (w - (K + (t + 3) / 2)), w])
          (attnList ((t + 2) / 2) (K + (t + 3) / 2)) ++
          (if (t + 2) % 2 = 1 then [attainVal ((t + 3) / 2) K ((t + 2) / 2)] else [])).length
          = t + 2 := by
        rw [List.length_append, flatMap_pairs_length, hWlen]
        by_cases hodd : (t + 2) % 2 = 1
        · rw [ite_eq_left hodd, List.length_cons, List.length_nil]
          omega
        · rw [ite_eq_right hodd, List.length_nil]
          omega
      rw [attnList_succ_succ t K]
      have hpair : pairUp (List.flatMap
          (fun w => [attainVal ((t + 3) / 2) K (w - (K + (t + 3) / 2)), w])
          (attnList ((t + 2) / 2) (K + (t + 3) / 2)) ++
          (if (t + 2) % 2 = 1 then [attainVal ((t + 3) / 2) K ((t + 2) / 2)] else []))
          = (attnList ((t + 2) / 2) (K + (t + 3) / 2),
              (attnList ((t + 2) / 2) (K + (t + 3) / 2)).map
                (fun w => attainVal ((t + 3) / 2) K (w - (K + (t + 3) / 2))),
              if (t + 2) % 2 = 1 then some (attainVal ((t + 3) / 2) K ((t + 2) / 2))
                else none) := by
        rw [← attnList_succ_succ t K]
        exact pairUp_attnList t K hltA
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- the input has no repeats
        have hfl : (List.flatMap
            (fun w => [attainVal ((t + 3) / 2) K (w - (K + (t + 3) / 2)), w])
            (attnList ((t + 2) / 2) (K + (t + 3) / 2))).Nodup := by
          refine nodup_flatMap_pairs _ _ (K + (t + 3) / 2) hWnd ?_ ?_ ?_
          · intro w hw
            exact attainVal_lt ((t + 3) / 2) K _ (hltA w hw).2
          · intro w hw; exact (hltA w hw).1
          · intro w hw w' hw' heq
            have h3 := attainVal_inj ((t + 3) / 2) K _ _ (hltA w hw).2 (hltA w' hw').2 heq
            have h4 := (hltA w hw).1
            have h5 := (hltA w' hw').1
            omega
        by_cases hodd : (t + 2) % 2 = 1
        · rw [ite_eq_left hodd, List.nodup_append]
          refine ⟨hfl, by simp, ?_⟩
          intro x hx y hy
          rw [mem_flatMap_pairs] at hx
          rw [List.mem_singleton] at hy
          obtain ⟨v, hv, hxv | hxv⟩ := hx
          · have h1 : v - (K + (t + 3) / 2) < (t + 2) / 2 := by
              have := (hWrange v hv).2
              omega
            intro heq
            rw [hxv, hy] at heq
            have h3 := attainVal_inj ((t + 3) / 2) K (v - (K + (t + 3) / 2)) ((t + 2) / 2)
              (hltA v hv).2 (by omega) heq
            omega
          · intro heq
            rw [hxv, hy] at heq
            have h1 : K + (t + 3) / 2 ≤ v := (hltA v hv).1
            have h2 : attainVal ((t + 3) / 2) K ((t + 2) / 2) < K + (t + 3) / 2 :=
              attainVal_lt ((t + 3) / 2) K ((t + 2) / 2) (by omega)
            exact (Nat.not_le_of_gt h2) (heq ▸ h1)
        · rw [ite_eq_right hodd, List.append_nil]
          exact hfl
      · -- it has `t + 2` elements
        exact hlenL
      · -- all its values lie in `[K, K + (t+2))`
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rw [mem_flatMap_pairs] at hx
          obtain ⟨w, hw, hxw | hxw⟩ := hx
          · have h1 := attainVal_mem_range ((t + 3) / 2) K _ (hltA w hw).2
            refine ⟨?_, ?_⟩
            · rw [hxw]; exact h1.1
            · rw [hxw]; omega
          · obtain ⟨h1, h2⟩ := hWrange w hw
            refine ⟨by omega, ?_⟩
            rw [hxw]
            omega
        · by_cases hodd : (t + 2) % 2 = 1
          · rw [ite_eq_left hodd, List.mem_singleton] at hx
            have h1 := attainVal_mem_range ((t + 3) / 2) K ((t + 2) / 2) (by omega)
            rw [hx]
            exact ⟨h1.1, by omega⟩
          · rw [ite_eq_right hodd] at hx
            exact absurd hx (by simp)
      · -- and merge-insertion spends exactly `fjCountJ (t+2)` on it
        have hchain : (sortedPairs (attnList ((t + 2) / 2) (K + (t + 3) / 2),
            (attnList ((t + 2) / 2) (K + (t + 3) / 2)).map
              (fun w => attainVal ((t + 3) / 2) K (w - (K + (t + 3) / 2))),
            if (t + 2) % 2 = 1 then some (attainVal ((t + 3) / 2) K ((t + 2) / 2))
              else none)).map Prod.fst
            = attnChain (K + (t + 3) / 2) ((t + 2) / 2) := by
          rw [sortedPairs, zip_map_self]
          rw [sortPairs_map_eq _ _ _ _ (perm_range_of_nodup_in_range _ _ _ hWlen hWnd hWrange),
            attnChain]
          simp
        have hitems : insertItems (attnList ((t + 2) / 2) (K + (t + 3) / 2),
            (attnList ((t + 2) / 2) (K + (t + 3) / 2)).map
              (fun w => attainVal ((t + 3) / 2) K (w - (K + (t + 3) / 2))),
            if (t + 2) % 2 = 1 then some (attainVal ((t + 3) / 2) K ((t + 2) / 2))
              else none) = attnItems K ((t + 2) / 2) ((t + 3) / 2) := by
          rw [insertItems, sortedPairs, zip_map_self]
          rw [sortPairs_map_eq _ _ _ _ (perm_range_of_nodup_in_range _ _ _ hWlen hWnd hWrange)]
          rw [List.map_map]
          have hmap : (List.map ((fun q : ℕ × ℕ => (some q.1, q.2)) ∘
              fun j => (K + (t + 3) / 2 + j,
                attainVal ((t + 3) / 2) K (K + (t + 3) / 2 + j - (K + (t + 3) / 2))))
              (List.range ((t + 2) / 2)))
              = (List.range ((t + 2) / 2)).map
                (fun j => (some (K + (t + 3) / 2 + j), attainVal ((t + 3) / 2) K j)) := by
            refine List.map_congr_left ?_
            intro j _
            simp only [Function.comp_apply]
            rw [show K + (t + 3) / 2 + j - (K + (t + 3) / 2) = j from by omega]
          rw [hmap]
          rw [← range_attnItems K ((t + 2) / 2) ((t + 3) / 2) (by omega) (by omega)]
          by_cases hodd : (t + 2) % 2 = 1
          · rw [ite_eq_left hodd, Option.toList_some, List.map_cons, List.map_nil,
              ite_eq_left (by omega : (t + 2) / 2 < (t + 3) / 2)]
          · rw [ite_eq_right hodd, Option.toList_none, List.map_nil,
              ite_eq_right (by omega : ¬ ((t + 2) / 2 < (t + 3) / 2))]
        have hwalk : (insertJacobsthal (insertItems (attnList ((t + 2) / 2) (K + (t + 3) / 2),
            (attnList ((t + 2) / 2) (K + (t + 3) / 2)).map
              (fun w => attainVal ((t + 3) / 2) K (w - (K + (t + 3) / 2))),
            if (t + 2) % 2 = 1 then some (attainVal ((t + 3) / 2) K ((t + 2) / 2))
              else none))
            (insertItems (attnList ((t + 2) / 2) (K + (t + 3) / 2),
            (attnList ((t + 2) / 2) (K + (t + 3) / 2)).map
              (fun w => attainVal ((t + 3) / 2) K (w - (K + (t + 3) / 2))),
            if (t + 2) % 2 = 1 then some (attainVal ((t + 3) / 2) K ((t + 2) / 2))
              else none)).length 0
            ((sortedPairs (attnList ((t + 2) / 2) (K + (t + 3) / 2),
            (attnList ((t + 2) / 2) (K + (t + 3) / 2)).map
              (fun w => attainVal ((t + 3) / 2) K (w - (K + (t + 3) / 2))),
            if (t + 2) % 2 = 1 then some (attainVal ((t + 3) / 2) K ((t + 2) / 2))
              else none)).map Prod.fst)).1 = jacInsertCost ((t + 3) / 2) := by
          rw [hitems, attnItems_length, hchain]
          exact insertJacobsthal_attnItems K ((t + 2) / 2) ((t + 3) / 2) (by omega) (by omega)
        rw [fjSortJ]
        rw [ite_eq_right (by rw [hlenL]; omega)]
        rw [hpair]
        simp only
        rw [hwalk, hWcost, hWlen]
        rw [fjCountJ_le_recurrence (t + 2) (by omega)]

set_option linter.unusedVariables false in
/-- **Merge-insertion's bound is exact for `n ≥ 2`**: there is an input on which the algorithm
spends exactly `fjCountJ n = F(n)` comparisons — as many as `fjSortJ_count_le` allows.  So
`fjCountJ n` is not merely an upper bound: it is the worst-case comparison count of `fjSortJ`
on `n` elements.  (The hypothesis `2 ≤ n` is not needed: the statement also holds for
`n = 0, 1`, where both sides vanish.) -/
theorem fjCountJ_attains (n : ℕ) (hn : 2 ≤ n) :
    ∃ l : List ℕ, l.length = n ∧ (fjSortJ l).1 = fjCountJ n := by
  refine ⟨attnList n 0, ?_, (attnList_spec n 0).2.2.2⟩
  rw [(attnList_spec n 0).2.1]

end SortBounds.Projects.FordJohnson
