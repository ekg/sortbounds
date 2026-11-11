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
    (hcross : ∀ (k k' : ℕ) (q p : Option ℕ × ℕ), k ≤ k' → q ∈ jacBatch items k' →
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
          exact hcross k k' q p (le_trans (Nat.le_succ k) hk') hq hp)
    have hstep : (insertJacobsthal items (fuel + 1) k l).1
        = (insertBatch (jacBatch items k) l).1
          + (insertJacobsthal items fuel (k + 1) (insertBatch (jacBatch items k) l).2).1 := rfl
    rw [hstep, hbatch', htail]
    simp only [jacInsertCostAux, jacLo, jacHi]

end SortBounds.Projects.FordJohnson
