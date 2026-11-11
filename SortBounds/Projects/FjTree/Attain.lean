/-
SortBounds/Projects/FjTree/Attain.lean

**The depth bound of `fjTree` is attained.**  `Main.fjTree_depth_le` says
`depth (fjTree n) ≤ fjCountJ n`; this file proves that some *input* makes the tree pay
every one of those `fjCountJ n` comparisons:

  `fjTree_cost_attains : ∃ x : Fin n → ℕ, Function.Injective x ∧ cost (fjTree n) x = fjCountJ n`

so `fjCountJ n` is the exact cost of `fjTree n` on a worst-case input — the tree-side
analogue of `FordJohnson.fjCountJ_attains`.

The shape of the proof mirrors the list-side `FordJohnson/Attain.lean`:

* `binIns_cost` — **one search on a deepest path**.  If the true rank of the searched item
  is the bottom `lo` of its window, every comparison takes the left (deepest) branch and the
  search costs exactly `⌈log₂ (hi - lo + 1)⌉`;
* `insPhase_cost` — the insertion phase, from an `Arranged` state, costs exactly
  `jacInsertCost M`: every item is below its whole window (rank `0`), and the window of
  batch `k` is `[0, jacLo + jacHi - 1)`, so each of the `jacHi - jacLo` searches of the
  batch costs `⌈log₂ (jacLo + jacHi)⌉`;
* `attnFun` — the attaining input family, the tree-side counterpart of `FordJohnson.attnList`:
  the winners are a scaled attaining input of size `n/2` (so the recursive call also costs
  its full count), and the partner of the winner of rank `j` gets `attainVal M 0 j`, a value
  that *decreases along the Jacobsthal insertion order*;
* `fjTreeFuel_cost` — the induction: `m` pairings + the winner tree's `fjCountJ m` + the
  phase's `jacInsertCost M` is exactly `fjCountJ n`, by `fjCountJ_le_recurrence`.

The one place the tree is *honest* about the count: `Arranged` records the value in every
slot of the arrangement, so "the item is below its window" is derived, not assumed.
-/
import SortBounds.Projects.FjTree.Correct
import SortBounds.Projects.FordJohnson.Attain

set_option linter.unusedSimpArgs false

namespace SortBounds.Projects.FjTree

open SortBounds
open SortBounds.Projects.FordJohnson (jac jacPred jac_pos le_jac jacPred_succ jacInsertCost
  jacInsertCostAux fjCountJ fjCountJ_eq_zero fjCountJ_le_recurrence attainVal attainT
  jacBatchOf jacBatchOf_eq_of_mem attainVal_lt attainVal_inj clog_half_eq jac_lt_succ)

variable {n : ℕ}

/-! ### The cost of a substitution -/

/-- **The cost of a substitution splits**: the stage's cost plus the continuation's cost
from the state the stage leaves behind. -/
theorem cost_substTree (t : Tree n) (f : Equiv.Perm (Fin n) → Tree n) (x : Fin n → ℕ) :
    cost (substTree t f) x = cost t x + cost (f (run t x)) x := by
  induction t with
  | leaf σ => simp only [substTree, cost, run, Nat.zero_add]
  | node i j l r ihl ihr =>
    show 1 + (if x i < x j then cost (substTree l f) x else cost (substTree r f) x)
        = 1 + (if x i < x j then cost l x else cost r x)
          + cost (f (if x i < x j then run l x else run r x)) x
    by_cases h : x i < x j
    · rw [ite_eq_left h, ite_eq_left h, ihl, ite_eq_left h]
      omega
    · rw [ite_eq_right h, ite_eq_right h, ihr, ite_eq_right h]
      omega

/-- The cost of a re-indexed tree is the cost of the inner tree on the restricted input. -/
theorem cost_imageTree {m : ℕ} (e : Fin m → Fin n)
    (L : Equiv.Perm (Fin m) → Equiv.Perm (Fin n)) (t : Tree m) (x : Fin n → ℕ) :
    cost (imageTree e L t) x = cost t (fun i => x (e i)) := by
  induction t with
  | leaf τ => rfl
  | node i j l r ihl ihr =>
    show 1 + (if x (e i) < x (e j) then cost (imageTree e L l) x
        else cost (imageTree e L r) x)
      = 1 + (if x (e i) < x (e j) then cost l (fun i => x (e i))
        else cost r (fun i => x (e i)))
    rw [ihl, ihr]

/-- Shifting all values by a constant does not change the work: only the comparison pattern
matters. -/
theorem cost_add_const (t : Tree n) (K : ℕ) (x : Fin n → ℕ) :
    cost t (fun i => K + x i) = cost t x :=
  cost_eq_of_pattern t (fun i j => by omega)

theorem run_add_const (t : Tree n) (K : ℕ) (x : Fin n → ℕ) :
    run t (fun i => K + x i) = run t x :=
  run_eq_of_pattern t (fun i j => by omega)

/-! ### One search on a deepest path -/

/-- **A search whose item is below its whole window costs the full `⌈log₂ (hi-lo+1)⌉`.**  If
the rank of the searched item is the bottom `lo` of the window, every comparison
`x (σ q) < x (σ mid)` succeeds, so the search descends the left (deepest) branch all the way
and inserts the item at rank `lo`. -/
theorem binIns_cost : ∀ (fuel lo hi c q : ℕ) (hqn : q < n) (hcq : c ≤ q) (hhi : hi ≤ c)
    (_hm : hi - lo ≤ fuel) (_hle : lo ≤ hi) (hjq : lo ≤ q),
    ∀ (σ : Equiv.Perm (Fin n)) (next : Equiv.Perm (Fin n) → Tree n) (x : Fin n → ℕ),
    Function.Injective x → ChainSorted x σ c → rankAt x σ c ⟨q, hqn⟩ = lo →
    cost (binIns fuel lo hi c q hqn hcq hhi σ next) x
      = Nat.clog 2 (hi - lo + 1) + cost (next (insertAt lo q hjq hqn σ)) x
  | 0, lo, hi, c, q, hqn, hcq, hhi, _hm, _hle, hjq, σ, next, x, hx, hchain, hrank => by
    simp only [binIns]
    obtain rfl : hi = lo := by omega
    rw [Nat.sub_self, Nat.clog_one_right, Nat.zero_add]
  | fuel + 1, lo, hi, c, q, hqn, hcq, hhi, _hm, _hle, hjq, σ, next, x, hx, hchain, hrank => by
    simp only [binIns]
    split_ifs with h
    · have hmid_lt : midOf lo hi < hi := midOf_lt h
      have hmidc : midOf lo hi < c := by omega
      have hmidn : midOf lo hi < n := by omega
      have hmidv : (midFin lo hi hmidn).val < c := by
        simp only [midFin_val]; exact hmidc
      have hnot : ¬ x (σ (midFin lo hi hmidn)) < x (σ ⟨q, hqn⟩) := by
        intro hlt
        have h2 := (lt_rankAt_iff hchain (midFin lo hi hmidn) hmidv).1 hlt
        rw [hrank] at h2
        simp only [midFin_val] at h2
        exact absurd h2 (not_lt.mpr (le_midOf lo hi))
      have hcmp : x (σ ⟨q, hqn⟩) < x (σ (midFin lo hi hmidn)) := by
        refine lt_of_le_of_ne (le_of_not_gt hnot) ?_
        intro heq
        have h2 : (⟨q, hqn⟩ : Fin n) = midFin lo hi hmidn := σ.injective (hx heq)
        have h3 : q = midOf lo hi := by simpa using congrArg Fin.val h2
        omega
      simp only [cost]
      rw [ite_eq_left hcmp]
      have hIH := binIns_cost fuel lo (midOf lo hi) c q hqn hcq (le_of_lt hmidc) (by omega)
        (le_midOf lo hi) hjq σ next x hx hchain hrank
      have hlog : Nat.clog 2 (hi - lo + 1) = Nat.clog 2 (midOf lo hi - lo + 1) + 1 := by
        rw [half_eq h]
        exact clog_half_eq (hi - lo) (by omega)
      rw [hIH, hlog]
      ac_rfl
    · obtain rfl : hi = lo := by omega
      rw [Nat.sub_self, Nat.clog_one_right, Nat.zero_add]

/-! ### The arrangement of the insertion phase

The insertion phase of `fjTree` walks the pending items in Jacobsthal order.  To count *exactly*
what it spends we have to know not only that its chain is sorted (which is
`Correct.Invar`) but *which value sits in every slot*: the item must be below its whole
window.  `slotVal` is that bookkeeping. -/

/-- The rank of the item sitting in the `r`-th slot of the pending block at batch `k`,
position `p`: the batch inserts its items in *decreasing* rank order, so the ranks still
pending are `jacLo … jacHi-1-p` in increasing order, followed by the ranks of the later
batches.  It is the number of items below that item. -/
def tailRank (M k p r : ℕ) : ℕ :=
  if r + p < cntB M k then jacLo M k + r else jacHi M k + (r + p - cntB M k)

/-- **The value expected in slot `s` of the arrangement** at batch `k`, position `p`: the
`jacLo + p` items already inserted (newest, hence smallest, first), the `m` sorted winners in
the middle, and the pending items of the batch and the later ones at the end. -/
noncomputable def slotVal (m M k p s : ℕ) : ℕ :=
  if s < jacLo M k + p then M - (jacLo M k + p) + s
  else if s < chainLen m M k p then M + (s - (jacLo M k + p))
  else attainVal M 0 (tailRank M k p (s - chainLen m M k p))

/-- **The arrangement of the insertion phase at batch `k`, position `p`**: the value of *every*
slot is pinned by `slotVal`. -/
def Arranged (x : Fin n → ℕ) (m M k p : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ s : Fin n, x (σ s) = slotVal m M k p s.val

theorem cntB_pos (M k p : ℕ) (hp : p < cntB M k) : 1 ≤ cntB M k := by omega

theorem jacLo_add_p_lt_jacHi (M k p : ℕ) (hp : p < cntB M k) : jacLo M k + p < jacHi M k := by
  have h := jacLo_le_jacHi M k
  simp only [cntB] at hp
  omega

theorem jacLo_add_p_le (M k p : ℕ) (hp : p < cntB M k) : jacLo M k + p < M := by
  have h1 := jacLo_add_p_lt_jacHi M k p hp
  have h2 := jacHi_le M k
  omega

theorem jacLo_add_p_le_chainLen (m M k p : ℕ) : jacLo M k + p ≤ chainLen m M k p := by
  simp only [chainLen]
  omega

/-- **The value of an item of a known rank**, from the Jacobsthal schedule: the rank `j` of
batch `k` is inserted when `jacLo + jacHi - 1 - j` items are already in. -/
theorem attainVal_of_mem {M k j : ℕ} (h1 : jacLo M k ≤ j) (h2 : j < jacHi M k) :
    attainVal M 0 j = M - 1 - (jacLo M k + jacHi M k - 1 - j) := by
  have hb : jacBatchOf j = k := jacBatchOf_eq_of_mem h1 h2
  simp only [attainVal, attainT, hb, Nat.zero_add, FordJohnson.jacLo, FordJohnson.jacHi,
    jacLo, jacHi]

/-- The item sitting in the batch's item slot is the one being inserted. -/
theorem tailRank_itemSlot (M k p : ℕ) (hp : p < cntB M k) :
    tailRank M k p (itemSlot m M k - chainLen m M k p) = jacHi M k - 1 - p := by
  have hp' : jacLo M k + p < jacHi M k := by
    simp only [cntB] at hp
    omega
  have h1 : itemSlot m M k - chainLen m M k p = cntB M k - 1 - p := by
    have h3 : m + jacLo M k + p ≤ m + jacHi M k - 1 := by omega
    simp only [itemSlot, chainLen, cntB]
    omega
  have h2 : cntB M k - 1 - p + p < cntB M k := by
    simp only [cntB]
    omega
  have hc : cntB M k = jacHi M k - jacLo M k := rfl
  rw [h1, tailRank, ite_eq_left h2, hc]
  omega

/-- **The value in the item slot** is the value of the item about to be inserted: the
`(jacLo+p)`-th comparison of the phase. -/
theorem slotVal_itemSlot {m M k p : ℕ} (hp : p < cntB M k) :
    slotVal m M k p (itemSlot m M k) = M - 1 - (jacLo M k + p) := by
  have hp' : jacLo M k + p < jacHi M k := by
    simp only [cntB] at hp
    omega
  have h2 : jacLo M k + p ≤ chainLen m M k p := jacLo_add_p_le_chainLen m M k p
  have h3 : itemSlot m M k = m + jacHi M k - 1 := rfl
  have h4 : ¬ itemSlot m M k < jacLo M k + p := by rw [h3]; omega
  have h5 : ¬ itemSlot m M k < chainLen m M k p := by
    rw [h3]
    simp only [chainLen] at hp' ⊢
    omega
  rw [slotVal, ite_eq_right h4, ite_eq_right h5, tailRank_itemSlot M k p hp,
    attainVal_of_mem (by omega : jacLo M k ≤ jacHi M k - 1 - p)
      (by omega : jacHi M k - 1 - p < jacHi M k)]
  omega

/-- The distance from the end of the chain to the item slot is `cntB - 1 - p`: the batch's
last item sits right behind the chain. -/
theorem itemSlot_sub_chainLen (m M k p : ℕ) (hp : p < cntB M k) :
    itemSlot m M k - chainLen m M k p = cntB M k - 1 - p := by
  have hp' : jacLo M k + p < jacHi M k := by
    simp only [cntB] at hp
    omega
  have h3 : m + jacLo M k + p ≤ m + jacHi M k - 1 := by omega
  simp only [itemSlot, chainLen, cntB]
  omega

theorem chainLen_succ (m M k p : ℕ) : chainLen m M k (p + 1) = chainLen m M k p + 1 := by
  simp only [chainLen]
  omega

/-- **Inside a batch the pending ranks stay put**: the `r`-th pending item after one insertion
was the `r`-th pending item before it as well. -/
theorem tailRank_step_lo (M k p r : ℕ) (h : r + p + 1 < cntB M k) :
    tailRank M k p r = tailRank M k (p + 1) r := by
  have h1 : r + p < cntB M k := by omega
  have h2 : r + (p + 1) < cntB M k := h
  rw [tailRank, tailRank, ite_eq_left h1, ite_eq_left h2]

/-- **Inside a batch the pending ranks shift by one**: once the batch has inserted its item of
the item slot, the `r`-th pending slot holds what was the `r+1`-th. -/
theorem tailRank_step_hi (M k p r : ℕ) (h : ¬ r + p + 1 < cntB M k) :
    tailRank M k p (r + 1) = tailRank M k (p + 1) r := by
  have h1 : ¬ (r + 1 + p < cntB M k) := by omega
  have h2 : ¬ r + (p + 1) < cntB M k := h
  rw [tailRank, tailRank, ite_eq_right h1, ite_eq_right h2]
  omega

/-- **The end of a batch is the start of the next**: at the last position of batch `k` the
pending items are exactly those of batch `k+1` at position `0`. -/
theorem tailRank_batch (M k r : ℕ) : tailRank M k (cntB M k) r = tailRank M (k + 1) 0 r := by
  have h1 : ¬ r + cntB M k < cntB M k := by omega
  have hsub : r + cntB M k - cntB M k = r := Nat.add_sub_cancel _ _
  have hjac : jacLo M (k + 1) = jacHi M k := rfl
  by_cases h2 : r < cntB M (k + 1)
  · have h2' : r + 0 < cntB M (k + 1) := h2
    rw [tailRank, tailRank, ite_eq_right h1, ite_eq_left h2', hjac, hsub]
  · have h2' : ¬ r + 0 < cntB M (k + 1) := h2
    rw [tailRank, tailRank, ite_eq_right h1, ite_eq_right h2']
    simp only [cntB, Nat.add_zero] at h2' ⊢
    rw [hjac]
    have hsub2 : r + (jacHi M k - jacLo M k) - (jacHi M k - jacLo M k) = r :=
      Nat.add_sub_cancel _ _
    rw [hsub2]
    have hmono : jacHi M k ≤ jacHi M (k + 1) :=
      min_le_min_left M (le_of_lt (jac_lt_succ k))
    omega

/-- The value of a slot among the items already inserted. -/
theorem slotVal_of_lt {m M k p s : ℕ} (h : s < jacLo M k + p) :
    slotVal m M k p s = M - (jacLo M k + p) + s := by
  rw [slotVal, ite_eq_left h]

/-- The value of a slot among the sorted winners. -/
theorem slotVal_of_winner {m M k p s : ℕ} (h1 : ¬ s < jacLo M k + p)
    (h2 : s < chainLen m M k p) : slotVal m M k p s = M + (s - (jacLo M k + p)) := by
  rw [slotVal, ite_eq_right h1, ite_eq_left h2]

/-- The value of a slot among the pending items. -/
theorem slotVal_of_pending {m M k p s : ℕ} (h1 : ¬ s < jacLo M k + p)
    (h2 : ¬ s < chainLen m M k p) :
    slotVal m M k p s = attainVal M 0 (tailRank M k p (s - chainLen m M k p)) := by
  rw [slotVal, ite_eq_right h1, ite_eq_right h2]

/-! ### The arrangement is preserved by one insertion -/

/-- **A batch shifts its pending items up by one**: after inserting the item of the item slot
at rank `0`, the value of slot `s` with `1 ≤ s ≤ itemSlot` is the value slot `s-1` had. -/
theorem slotVal_shift (m M k p s : ℕ) (hp : p + 1 < cntB M k) (h1 : 1 ≤ s)
    (h2 : s ≤ itemSlot m M k) :
    slotVal m M k p (s - 1) = slotVal m M k (p + 1) s := by
  have hp0 : p < cntB M k := by omega
  have hc : chainLen m M k (p + 1) = chainLen m M k p + 1 := chainLen_succ m M k p
  have hq : itemSlot m M k - chainLen m M k p = cntB M k - 1 - p :=
    itemSlot_sub_chainLen m M k p hp0
  have ht : jacLo M k + p < M := jacLo_add_p_le M k p hp0
  rcases lt_or_ge (s - 1) (jacLo M k + p) with h3 | h3
  · have h3' : s < jacLo M k + (p + 1) := by omega
    rw [slotVal_of_lt h3, slotVal_of_lt h3']
    omega
  · rcases lt_or_ge (s - 1) (chainLen m M k p) with h4 | h4
    · have h4' : s < chainLen m M k (p + 1) := by rw [hc]; omega
      rw [slotVal_of_winner (by omega) h4, slotVal_of_winner (by omega) h4']
      omega
    · have hs : chainLen m M k (p + 1) ≤ s := by rw [hc]; omega
      have hs1 : ¬ s < chainLen m M k (p + 1) := by omega
      rw [slotVal_of_pending (by omega) (by omega), slotVal_of_pending (by omega) hs1, hc]
      have harg : s - (chainLen m M k p + 1) = s - 1 - chainLen m M k p := by omega
      have hle1 : s - chainLen m M k p ≤ cntB M k - 1 - p := by
        have h := Nat.sub_le_sub_right h2 (chainLen m M k p)
        rwa [hq] at h
      have hA : s - chainLen m M k p + p ≤ cntB M k - 1 := by
        have h := Nat.add_le_add_right hle1 p
        have hp' : p ≤ cntB M k - 1 := by omega
        rwa [Nat.sub_add_cancel hp'] at h
      have hcond : (s - 1 - chainLen m M k p) + p + 1 < cntB M k := by omega
      rw [harg, tailRank_step_lo M k p (s - 1 - chainLen m M k p) hcond]

/-- **Past the item slot nothing moves** inside a batch: the slot beyond the chain is at the
very end of the pending block, so an insertion at `0` leaves it alone. -/
theorem slotVal_tail (m M k p s : ℕ) (hm : 1 ≤ m) (hp : p + 1 < cntB M k)
    (h2 : itemSlot m M k < s) :
    slotVal m M k p s = slotVal m M k (p + 1) s := by
  have hp0 : p < cntB M k := by omega
  have hc : chainLen m M k (p + 1) = chainLen m M k p + 1 := chainLen_succ m M k p
  have hq : itemSlot m M k - chainLen m M k p = cntB M k - 1 - p :=
    itemSlot_sub_chainLen m M k p hp0
  have hcl : chainLen m M k p ≤ itemSlot m M k := chainLen_le_itemSlot m M k p hp0
  have hj : jacLo M k + p < itemSlot m M k := by
    have h : jacLo M k + p < jacHi M k := jacLo_add_p_lt_jacHi M k p hp0
    have h2' : jacHi M k ≤ m + jacHi M k - 1 := by omega
    exact lt_of_lt_of_le h h2'
  have hs1 : ¬ s < chainLen m M k (p + 1) := by rw [hc]; omega
  rw [slotVal_of_pending (by omega) (by omega), slotVal_of_pending (by omega) hs1, hc]
  have harg : s - (chainLen m M k p + 1) = s - 1 - chainLen m M k p := by omega
  have hle : itemSlot m M k - chainLen m M k p ≤ s - chainLen m M k p :=
    Nat.sub_le_sub_right (le_of_lt h2) _
  have hle2 : cntB M k - p ≤ s - chainLen m M k p := by
    rw [hq] at hle
    omega
  have hlow : cntB M k ≤ s - chainLen m M k p + p := Nat.sub_le_iff_le_add.mp hle2
  have hcond : ¬ s - 1 - chainLen m M k p + p + 1 < cntB M k := by omega
  have harg2 : s - 1 - chainLen m M k p + 1 = s - chainLen m M k p := by omega
  rw [harg, ← harg2, tailRank_step_hi M k p (s - 1 - chainLen m M k p) hcond]

/-- At the end of a batch the item slot is the first slot past the chain, so the item there is
the one the next batch expects in slot `0`. -/
theorem slotVal_zero_batch (m M k p : ℕ) (hM1 : 1 ≤ M) (hp : p + 1 = cntB M k) :
    slotVal m M k p (itemSlot m M k) = slotVal m M (k + 1) 0 0 := by
  have hp0 : p < cntB M k := by omega
  have hlt : jacLo M k + p < jacHi M k := jacLo_add_p_lt_jacHi M k p hp0
  have hjc : jacLo M k + p = jacHi M k - 1 := by
    simp only [cntB] at hp
    omega
  have hcl : itemSlot m M k = chainLen m M k p := by
    simp only [itemSlot, chainLen, cntB] at hp ⊢
    omega
  have hjM : jacHi M k ≤ M := jacHi_le M k
  have hj1 : 0 < jacHi M k := by omega
  have hitem : slotVal m M k p (itemSlot m M k) = M - jacHi M k := by
    have hzero : tailRank M k p 0 = jacLo M k := by
      rw [tailRank, ite_eq_left (by omega : 0 + p < cntB M k)]
      omega
    have h1 : ¬ chainLen m M k p < jacLo M k + p := by
      simp only [chainLen]
      omega
    have h2 : ¬ chainLen m M k p < chainLen m M k p := by omega
    rw [hcl, slotVal_of_pending h1 h2, Nat.sub_self, hzero,
      attainVal_of_mem (le_rfl : jacLo M k ≤ jacLo M k) (by omega : jacLo M k < jacHi M k)]
    omega
  have hnew : slotVal m M (k + 1) 0 0 = M - jacHi M k := by
    have hjac : jacLo M (k + 1) = jacHi M k := rfl
    rw [slotVal_of_lt (s := 0) (by rw [hjac, Nat.add_zero]; omega)]
    rw [hjac, Nat.add_zero]
    omega
  rw [hitem, hnew]

/-- **A batch shifts its pending items up by one, across the batch boundary**: after the last
insertion of batch `k`, the value of slot `s` (`1 ≤ s ≤ itemSlot`) is the value slot `s-1` had. -/
theorem slotVal_shift_batch (m M k p s : ℕ) (_hM1 : 1 ≤ M) (hp : p + 1 = cntB M k) (h1 : 1 ≤ s)
    (h2 : s ≤ itemSlot m M k) :
    slotVal m M k p (s - 1) = slotVal m M (k + 1) 0 s := by
  have hp0 : p < cntB M k := by omega
  have hlt : jacLo M k + p < jacHi M k := jacLo_add_p_lt_jacHi M k p hp0
  have hjc : jacLo M k + p = jacHi M k - 1 := by
    simp only [cntB] at hp
    omega
  have hcl : itemSlot m M k = chainLen m M k p := by
    simp only [itemSlot, chainLen, cntB] at hp ⊢
    omega
  have hjac : jacLo M (k + 1) = jacHi M k := rfl
  have hcl' : chainLen m M (k + 1) 0 = chainLen m M k p + 1 := by
    simp only [chainLen]
    rw [hjac]
    simp only [cntB] at hp
    omega
  have hjM : jacHi M k ≤ M := jacHi_le M k
  rcases lt_or_ge (s - 1) (jacLo M k + p) with h3 | h3
  · have h3' : s < jacLo M (k + 1) + 0 := by rw [hjac, Nat.add_zero]; omega
    rw [slotVal_of_lt h3, slotVal_of_lt h3', hjc, hjac, Nat.add_zero]
    omega
  · have h4 : ¬ s < jacLo M (k + 1) + 0 := by
      rw [hjac, Nat.add_zero]
      omega
    have h5 : s < chainLen m M (k + 1) 0 := by rw [hcl']; omega
    rw [slotVal_of_winner (by omega) (by omega), slotVal_of_winner h4 h5, hjc, hjac,
      Nat.add_zero]
    omega

/-- **Past the item slot nothing moves across a batch boundary.** -/
theorem slotVal_tail_batch (m M k p s : ℕ) (hm : 1 ≤ m) (hp : p + 1 = cntB M k)
    (h2 : itemSlot m M k < s) :
    slotVal m M k p s = slotVal m M (k + 1) 0 s := by
  have hp0 : p < cntB M k := by omega
  have hlt : jacLo M k + p < jacHi M k := jacLo_add_p_lt_jacHi M k p hp0
  have hcl : itemSlot m M k = chainLen m M k p := by
    simp only [itemSlot, chainLen, cntB] at hp ⊢
    omega
  have hjac : jacLo M (k + 1) = jacHi M k := rfl
  have hcl' : chainLen m M (k + 1) 0 = chainLen m M k p + 1 := by
    simp only [chainLen]
    rw [hjac]
    simp only [cntB] at hp
    omega
  have hle : itemSlot m M k - chainLen m M k p ≤ s - chainLen m M k p :=
    Nat.sub_le_sub_right (le_of_lt h2) _
  have hsub : itemSlot m M k - chainLen m M k p = cntB M k - 1 - p :=
    itemSlot_sub_chainLen m M k p hp0
  rw [hsub] at hle
  have hcond : ¬ s - 1 - chainLen m M k p + p + 1 < cntB M k := by
    have hlow : cntB M k ≤ s - chainLen m M k p + p := by
      have hle2 : cntB M k - p ≤ s - chainLen m M k p := by omega
      exact Nat.sub_le_iff_le_add.mp hle2
    have hge : s - chainLen m M k p + p ≤ s - 1 - chainLen m M k p + p + 1 := by omega
    omega
  have hjcH : jacHi M k ≤ itemSlot m M k := by
    simp only [itemSlot]
    omega
  have h0 : ¬ s < jacLo M (k + 1) + 0 := by rw [hjac, Nat.add_zero]; omega
  have h0' : ¬ s < jacLo M k + p := by omega
  have h1 : ¬ s < chainLen m M (k + 1) 0 := by rw [hcl']; omega
  rw [slotVal_of_pending h0' (by omega), slotVal_of_pending h0 h1, hcl']
  have harg : s - (chainLen m M k p + 1) = s - 1 - chainLen m M k p := by omega
  rw [harg]
  have harg2 : s - 1 - chainLen m M k p + 1 = s - chainLen m M k p := by omega
  rw [← harg2, tailRank_step_hi M k p (s - 1 - chainLen m M k p) hcond]
  rw [show p + 1 = cntB M k from hp, tailRank_batch]

/-! #### What an arranged state gives -/

/-- **The chain of an arranged state is sorted.** -/
theorem chainSorted_of_arranged {m M k p : ℕ} (hp : p ≤ cntB M k) {x : Fin n → ℕ}
    {σ : Equiv.Perm (Fin n)} (h : Arranged x m M k p σ) : ChainSorted x σ (chainLen m M k p) := by
  have ht : jacLo M k + p ≤ M := by
    have h1 := jacLo_le_jacHi M k
    have h2 := jacHi_le M k
    simp only [cntB] at hp
    omega
  intro i j hi hj hij
  have hi' := h i
  have hj' := h j
  rw [hi', hj']
  rcases lt_or_ge i.val (jacLo M k + p) with h1 | h1
  · rw [slotVal_of_lt h1]
    rcases lt_or_ge j.val (jacLo M k + p) with h2 | h2
    · rw [slotVal_of_lt h2]
      omega
    · rw [slotVal_of_winner (by omega) hj]
      omega
  · have h1' : ¬ i.val < jacLo M k + p := by omega
    have h2' : ¬ j.val < jacLo M k + p := by omega
    rw [slotVal_of_winner h1' hi, slotVal_of_winner h2' hj]
    omega

/-- **The item about to be inserted is below the whole chain** in an arranged state: the
inserted items come first (and are all larger), the winners after them. -/
theorem slotVal_lt_chainLen {m M k p : ℕ} (hp : p < cntB M k) (hM1 : 1 ≤ M) {s : ℕ}
    (hs : s < chainLen m M k p) :
    slotVal m M k p (itemSlot m M k) < slotVal m M k p s := by
  have hlt : jacLo M k + p < jacHi M k := jacLo_add_p_lt_jacHi M k p hp
  have hM : jacLo M k + p < M := jacLo_add_p_le M k p hp
  have hjc : jacLo M k + p ≤ M - 1 := by omega
  have hq : itemSlot m M k = m + jacHi M k - 1 := rfl
  rw [slotVal_itemSlot (m := m) hp]
  rcases lt_or_ge s (jacLo M k + p) with h1 | h1
  · rw [slotVal_of_lt h1]
    omega
  · rw [slotVal_of_winner (by omega) hs]
    omega

/-- **The rank of the item about to be inserted is `0`**: it is below every chain element. -/
theorem rankAt_zero_of_arranged {m M : ℕ} (hmM : m + M ≤ n) (hM1 : 1 ≤ M) {k p : ℕ}
    (hp : p < cntB M k) {x : Fin n → ℕ} {σ : Equiv.Perm (Fin n)}
    (h : Arranged x m M k p σ) :
    rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, itemSlot_lt m M k hmM hM1⟩ = 0 := by
  have hq : itemSlot m M k < n := itemSlot_lt m M k hmM hM1
  rw [rankAt, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨a, ha⟩
  rw [mem_rankSet_iff] at ha
  obtain ⟨h1, h2⟩ := ha
  have h3 : x (σ ⟨itemSlot m M k, hq⟩) < x (σ a) := by
    rw [h ⟨itemSlot m M k, hq⟩, h a]
    exact slotVal_lt_chainLen hp hM1 h1
  omega

/-- **The end of a batch is the start of the next**: at position `cntB` of batch `k` the
arrangement is the one batch `k+1` starts from. -/
theorem slotVal_batch_end (m M k s : ℕ) : slotVal m M k (cntB M k) s = slotVal m M (k + 1) 0 s := by
  have hjac : jacLo M (k + 1) = jacHi M k := rfl
  have hjl := jacLo_le_jacHi M k
  have hle : jacLo M k + cntB M k = jacLo M (k + 1) + 0 := by
    simp only [cntB]
    rw [hjac]
    omega
  have hc : chainLen m M k (cntB M k) = chainLen m M (k + 1) 0 := by
    simp only [chainLen, cntB]
    rw [hjac]
    omega
  rcases lt_or_ge s (jacLo M (k + 1) + 0) with h1 | h1
  · have h1' : s < jacLo M k + cntB M k := by rw [hle]; exact h1
    rw [slotVal_of_lt h1', slotVal_of_lt h1, hle]
  · rcases lt_or_ge s (chainLen m M (k + 1) 0) with h2 | h2
    · have h2' : s < chainLen m M k (cntB M k) := by rw [hc]; exact h2
      rw [slotVal_of_winner (by rw [hle]; omega) h2', slotVal_of_winner (by omega) h2, hle]
    · have h2' : ¬ s < chainLen m M k (cntB M k) := by rw [hc]; omega
      rw [slotVal_of_pending (by rw [hle]; omega) h2',
        slotVal_of_pending (by omega) (by omega), hc]
      rw [tailRank_batch]

/-- **One insertion at rank `0` keeps the arrangement** inside a batch. -/
theorem arranged_step {m M : ℕ} (hm : 1 ≤ m) (hmM : m + M ≤ n) (hM1 : 1 ≤ M) {k p : ℕ}
    (hp : p + 1 < cntB M k) {x : Fin n → ℕ} {σ : Equiv.Perm (Fin n)}
    (h : Arranged x m M k p σ) :
    Arranged x m M k (p + 1)
      (insertAt 0 (itemSlot m M k) (Nat.zero_le _) (itemSlot_lt m M k hmM hM1) σ) := by
  have hp0 : p < cntB M k := by omega
  have hq : itemSlot m M k < n := itemSlot_lt m M k hmM hM1
  intro s
  rcases Nat.eq_zero_or_pos s.val with hs | hs
  · have hstep : insertAt 0 (itemSlot m M k) (Nat.zero_le _) hq σ s = σ ⟨itemSlot m M k, hq⟩ :=
      insertAt_apply_eq 0 (itemSlot m M k) (Nat.zero_le _) hq σ hs
    rw [hstep, h ⟨itemSlot m M k, hq⟩, slotVal_itemSlot (m := m) hp0]
    rw [show s.val = 0 from hs, slotVal_of_lt (s := 0) (by omega)]
    omega
  · rcases le_or_gt s.val (itemSlot m M k) with hle | hgt
    · have hstep : insertAt 0 (itemSlot m M k) (Nat.zero_le _) hq σ s = σ (predFin s) :=
        insertAt_apply_mid 0 (itemSlot m M k) (Nat.zero_le _) hq σ hs hle
      have hpre : predFin s = (⟨s.val - 1, by omega⟩ : Fin n) := Fin.ext (predFin_val s)
      rw [hstep, hpre, h ⟨s.val - 1, by omega⟩]
      exact slotVal_shift m M k p s.val hp hs hle
    · have hstep : insertAt 0 (itemSlot m M k) (Nat.zero_le _) hq σ s = σ s :=
        insertAt_apply_gt 0 (itemSlot m M k) (Nat.zero_le _) hq σ hgt
      rw [hstep, h s]
      exact slotVal_tail m M k p s.val hm hp hgt

/-- **One insertion at rank `0` keeps the arrangement** at the end of a batch, where the next
batch starts. -/
theorem arranged_step_batch {m M : ℕ} (hm : 1 ≤ m) (hmM : m + M ≤ n) (hM1 : 1 ≤ M) {k p : ℕ}
    (hp : p + 1 = cntB M k) {x : Fin n → ℕ} {σ : Equiv.Perm (Fin n)}
    (h : Arranged x m M k p σ) :
    Arranged x m M (k + 1) 0
      (insertAt 0 (itemSlot m M k) (Nat.zero_le _) (itemSlot_lt m M k hmM hM1) σ) := by
  have hq : itemSlot m M k < n := itemSlot_lt m M k hmM hM1
  intro s
  rcases Nat.eq_zero_or_pos s.val with hs | hs
  · have hstep : insertAt 0 (itemSlot m M k) (Nat.zero_le _) hq σ s = σ ⟨itemSlot m M k, hq⟩ :=
      insertAt_apply_eq 0 (itemSlot m M k) (Nat.zero_le _) hq σ hs
    rw [hstep, h ⟨itemSlot m M k, hq⟩, slotVal_zero_batch m M k p hM1 hp,
      show s.val = 0 from hs]
  · rcases le_or_gt s.val (itemSlot m M k) with hle | hgt
    · have hstep : insertAt 0 (itemSlot m M k) (Nat.zero_le _) hq σ s = σ (predFin s) :=
        insertAt_apply_mid 0 (itemSlot m M k) (Nat.zero_le _) hq σ hs hle
      have hpre : predFin s = (⟨s.val - 1, by omega⟩ : Fin n) := Fin.ext (predFin_val s)
      rw [hstep, hpre, h ⟨s.val - 1, by omega⟩]
      exact slotVal_shift_batch m M k p s.val hM1 hp hs hle
    · have hstep : insertAt 0 (itemSlot m M k) (Nat.zero_le _) hq σ s = σ s :=
        insertAt_apply_gt 0 (itemSlot m M k) (Nat.zero_le _) hq σ hgt
      rw [hstep, h s]
      exact slotVal_tail_batch m M k p s.val hm hp hgt

/-- The end of a batch is the start of the next, as an arrangement. -/
theorem arranged_next_batch {m M k : ℕ} {x : Fin n → ℕ} {σ : Equiv.Perm (Fin n)}
    (h : Arranged x m M k (cntB M k) σ) : Arranged x m M (k + 1) 0 σ := by
  intro s
  rw [h s, slotVal_batch_end]

/-! ### The cost of the insertion phase

With the arrangement in hand the count is a computation: every search of the phase is a
deepest-path search in a window of `jacLo + jacHi - 1` slots. -/

/-- The state after an insertion depends on the rank only through its value: the two proofs
`j ≤ q` are irrelevant. -/
theorem insertAt_congr {j j' q : ℕ} (h : j = j') (hjq : j ≤ q) (hjq' : j' ≤ q) (hqn : q < n)
    (σ : Equiv.Perm (Fin n)) : insertAt j q hjq hqn σ = insertAt j' q hjq' hqn σ := by
  subst h
  rfl

/-- The start of a batch read as the end of the previous one. -/
theorem arranged_batch_end {m M k : ℕ} {x : Fin n → ℕ} {σ : Equiv.Perm (Fin n)}
    (h : Arranged x m M (k + 1) 0 σ) : Arranged x m M k (cntB M k) σ := by
  intro s
  rw [slotVal_batch_end]
  exact h s

/-- `⌈log₂ (winWindow + 1)⌉ = ⌈log₂ (jacLo + jacHi)⌉`: the window of a batch. -/
theorem clog_winWindow (M k : ℕ) (hM1 : 1 ≤ M) :
    Nat.clog 2 (winWindow M k - 0 + 1) = Nat.clog 2 (jacLo M k + jacHi M k) := by
  have hp := jacHi_pos M k hM1
  simp only [winWindow]
  rw [Nat.sub_zero]
  congr 1
  omega

/-- **A batch costs exactly `|batch| · ⌈log₂ (jacLo + jacHi)⌉`**: every item of the batch is
below its whole window, so each of the `jacHi - jacLo` searches descends the deepest branch,
and the state is arranged at the end of the batch. -/
theorem insBatch_cost {m M : ℕ} (hm : 1 ≤ m) (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M)
    {x : Fin n → ℕ} (hx : Function.Injective x) (next : Equiv.Perm (Fin n) → Tree n) :
    ∀ (k j : ℕ) (hj : j ≤ cntB M k) (σ : Equiv.Perm (Fin n)),
      Arranged x m M k (cntB M k - j) σ →
      Arranged x m M k (cntB M k)
          (run (insBatch m M hmM hM hM1 (fun σ => Tree.leaf σ) k j hj σ) x) ∧
        cost (insBatch m M hmM hM hM1 next k j hj σ) x
          = j * Nat.clog 2 (jacLo M k + jacHi M k)
            + cost (next (run (insBatch m M hmM hM hM1 (fun σ => Tree.leaf σ) k j hj σ) x)) x
  | k, 0, _, σ, h => by
    have h1 : cntB M k - 0 = cntB M k := Nat.sub_zero _
    rw [h1] at h
    refine ⟨h, ?_⟩
    simp only [insBatch, run, Nat.zero_mul, Nat.zero_add]
  | k, j + 1, hj, σ, h => by
    have hpos : cntB M k - (j + 1) = cntB M k - 1 - j := by omega
    rw [hpos] at h
    have hp : cntB M k - 1 - j < cntB M k := by omega
    have hq : itemSlot m M k < n := itemSlot_lt m M k hmM hM1
    have hchain := chainSorted_of_arranged (p := cntB M k - 1 - j) (by omega) h
    have hwin : rankAt x σ (chainLen m M k (cntB M k - 1 - j))
        ⟨itemSlot m M k, hq⟩ = 0 := rankAt_zero_of_arranged hmM hM1 hp h
    have hstep' : Arranged x m M k (cntB M k - 1 - j + 1)
        (insertAt 0 (itemSlot m M k) (Nat.zero_le _) hq σ) := by
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · have hp1 : cntB M k - 1 - j + 1 = cntB M k := by omega
        have hb := arranged_step_batch (m := m) (M := M) hm hmM hM1
          (k := k) (p := cntB M k - 1 - j) (by omega) h
        rw [hp1]
        exact arranged_batch_end hb
      · exact arranged_step (m := m) (M := M) hm hmM hM1 (k := k) (p := cntB M k - 1 - j)
          (by omega) h
    have he : cntB M k - j = cntB M k - 1 - j + 1 := by omega
    have hIH := insBatch_cost hm hmM hM hM1 hx next k j (by omega)
      (insertAt 0 (itemSlot m M k) (Nat.zero_le _) hq σ) (by rw [he]; exact hstep')
    -- the search itself
    have hcost := binIns_cost (winWindow M k) 0 (winWindow M k) (chainLen m M k (cntB M k - 1 - j))
      (itemSlot m M k) hq (chainLen_le_itemSlot m M k (cntB M k - 1 - j) hp)
      (winWindow_le_chainLen m M k (cntB M k - 1 - j) hM hM1)
      (le_rfl : winWindow M k - 0 ≤ winWindow M k) (Nat.zero_le _) (Nat.zero_le _)
      σ (insBatch m M hmM hM hM1 next k j (by omega)) x hx hchain hwin
    have hrun := binIns_run (winWindow M k) 0 (winWindow M k) (chainLen m M k (cntB M k - 1 - j))
      (itemSlot m M k) hq (chainLen_le_itemSlot m M k (cntB M k - 1 - j) hp)
      (winWindow_le_chainLen m M k (cntB M k - 1 - j) hM hM1)
      (le_rfl : winWindow M k - 0 ≤ winWindow M k) σ
      (insBatch m M hmM hM hM1 (fun σ => Tree.leaf σ) k j (by omega)) x hx hchain
      (Nat.zero_le _) (by rw [hwin]; omega)
    have hlog := clog_winWindow M k hM1
    have hrle : rankAt x σ (chainLen m M k (cntB M k - 1 - j)) ⟨itemSlot m M k, hq⟩
        ≤ itemSlot m M k := by
      have h1 := rankAt_le x σ (chainLen m M k (cntB M k - 1 - j)) ⟨itemSlot m M k, hq⟩
      omega
    have hstate : insertAt (rankAt x σ (chainLen m M k (cntB M k - 1 - j))
          ⟨itemSlot m M k, hq⟩) (itemSlot m M k) hrle hq σ
        = insertAt 0 (itemSlot m M k) (Nat.zero_le _) hq σ :=
      insertAt_congr hwin _ _ hq σ
    refine ⟨?_, ?_⟩
    · rw [insBatch_succ (next := fun σ => Tree.leaf σ), hrun, hstate]
      exact hIH.1
    · rw [insBatch_succ (next := next), hcost, hIH.2, hlog]
      rw [insBatch_succ (next := fun σ => Tree.leaf σ), hrun, hstate]
      ring

/-- **The insertion phase costs exactly `jacInsertCost M`**: the batches run to the end, each
costing its own `|batch| · ⌈log₂ (jacLo + jacHi)⌉`. -/
theorem insBatches_cost {m M : ℕ} (hm : 1 ≤ m) (hmM : m + M ≤ n) (hM : M ≤ m + 1)
    (hM1 : 1 ≤ M) {x : Fin n → ℕ} (hx : Function.Injective x) :
    ∀ (fuel k : ℕ), k + fuel = M → ∀ σ : Equiv.Perm (Fin n), Arranged x m M k 0 σ →
      cost (insBatches m M hmM hM hM1 (fun σ => Tree.leaf σ) fuel k σ) x
        = jacInsertCostAux M fuel k
  | 0, k, _, σ, _ => by
    simp only [insBatches, jacInsertCostAux, cost]
  | fuel + 1, k, hk, σ, h => by
    have h' : Arranged x m M k (cntB M k - cntB M k) σ := by
      rw [Nat.sub_self]
      exact h
    have haux := insBatch_cost hm hmM hM hM1 hx
      (insBatches m M hmM hM hM1 (fun σ => Tree.leaf σ) fuel (k + 1))
      k (cntB M k) le_rfl σ h'
    have hrec := insBatches_cost hm hmM hM hM1 hx fuel (k + 1) (by omega)
      (run (insBatch m M hmM hM hM1 (fun σ => Tree.leaf σ) k (cntB M k) le_rfl σ) x)
      (arranged_next_batch haux.1)
    show cost (insBatch m M hmM hM hM1
      (insBatches m M hmM hM hM1 (fun σ => Tree.leaf σ) fuel (k + 1)) k (cntB M k) le_rfl σ) x
      = jacInsertCostAux M (fuel + 1) k
    rw [haux.2, hrec]
    simp only [jacInsertCostAux, cntB, jacLo, jacHi]

/-- **The insertion phase costs exactly `jacInsertCost M`**, from the state the transport
leaves behind. -/
theorem insPhase_cost {m M : ℕ} (hm : 1 ≤ m) (hmM : m + M ≤ n) (_hMn : m + M = n)
    (hM : M ≤ m + 1) (hM1 : 1 ≤ M) {x : Fin n → ℕ} (hx : Function.Injective x)
    {σ : Equiv.Perm (Fin n)} (h : Arranged x m M 0 0 σ) :
    cost (insPhase m M hmM hM hM1 σ) x = jacInsertCost M := by
  have hres := insBatches_cost hm hmM hM hM1 hx M 0 (by omega) σ h
  simpa only [insPhase, jacInsertCost] using hres

/-! ### The attaining input

The tree-side counterpart of `FordJohnson.attnList`: the winners (`i < n/2`) are a scaled
attaining input of size `n/2`, so the recursive call also pays its full count, and the partner
of the winner at position `p` gets `attainVal M 0 (value at p)` — a value that *decreases along
the Jacobsthal insertion order*, so every item is below everything inserted before it. -/

/-- A strictly increasing map on `Fin m` is at least the identity. -/
theorem le_strictMono_val {m : ℕ} {f : Fin m → ℕ} (hf : StrictMono f) :
    ∀ (i : ℕ) (h : i < m), i ≤ f ⟨i, h⟩ := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · omega
    · have h1 : i - 1 ≤ f ⟨i - 1, by omega⟩ := ih (i - 1) (by omega) (by omega)
      have h2 : f ⟨i - 1, by omega⟩ < f ⟨i, hi⟩ := by
        refine hf ?_
        simp only [Fin.lt_def]
        omega
      omega

/-- A strictly increasing map from `Fin m` into `[0, m)` is the identity. -/
theorem eq_val_of_strictMono {m : ℕ} {f : Fin m → ℕ} (hf : StrictMono f) (hb : ∀ i, f i < m) :
    ∀ i : Fin m, f i = i.val := by
  have hlow := le_strictMono_val hf
  have hg : StrictMono fun j : Fin m => m - 1 - f (Fin.rev j) := by
    intro a b hab
    have h3 : Fin.rev b < Fin.rev a := by
      simp only [Fin.rev, Fin.lt_def]
      have := a.isLt
      have := b.isLt
      omega
    have h4 : f (Fin.rev b) < f (Fin.rev a) := hf h3
    have h5 : f (Fin.rev a) < m := hb _
    show m - 1 - f (Fin.rev a) < m - 1 - f (Fin.rev b)
    omega
  have hgb : ∀ j : Fin m, m - 1 - f (Fin.rev j) < m := by
    intro j
    have := hb (Fin.rev j)
    omega
  have hhigh : ∀ (i : ℕ) (h : i < m), f ⟨i, h⟩ ≤ i := by
    intro i hi
    have h6 := le_strictMono_val hg (m - 1 - i) (by omega)
    have h7 : (⟨m - 1 - i, by omega⟩ : Fin m) = Fin.rev ⟨i, hi⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; omega)
    rw [h7, Fin.rev_rev] at h6
    have h8 : f ⟨i, hi⟩ < m := hb _
    omega
  intro i
  exact le_antisymm (hhigh i.val i.isLt) (hlow i.val i.isLt)

/-- **The attaining input of the tree**, by position: merge-insertion's worst case.  The winners
(`i < n/2`) are a scaled attaining input of size `n/2`; the partner of the winner at position
`p` gets `attainVal M 0 (value at p)`, a value that decreases along the Jacobsthal insertion
order; the unpaired element of an odd input gets `attainVal M 0 (n/2)`. -/
noncomputable def attnFun : (n : ℕ) → Fin n → ℕ
  | 0 => fun i => i.elim0
  | 1 => fun _ => 0
  | k + 2 => fun i =>
      if h : i.val < (k + 2) / 2 then
        ((k + 2) - (k + 2) / 2) + attnFun ((k + 2) / 2) ⟨i.val, h⟩
      else if h2 : i.val < 2 * ((k + 2) / 2) then
        attainVal ((k + 2) - (k + 2) / 2) 0
          (attnFun ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩)
      else attainVal ((k + 2) - (k + 2) / 2) 0 ((k + 2) / 2)
  termination_by n => n

theorem attnFun_succ_succ (k : ℕ) :
    attnFun (k + 2) = fun i : Fin (k + 2) =>
      if h : i.val < (k + 2) / 2 then
        ((k + 2) - (k + 2) / 2) + attnFun ((k + 2) / 2) ⟨i.val, h⟩
      else if h2 : i.val < 2 * ((k + 2) / 2) then
        attainVal ((k + 2) - (k + 2) / 2) 0
          (attnFun ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩)
      else attainVal ((k + 2) - (k + 2) / 2) 0 ((k + 2) / 2) := by
  rw [attnFun]

/-- A winner's value. -/
theorem attnFun_winner {k : ℕ} (i : Fin (k + 2)) (h : i.val < (k + 2) / 2) :
    attnFun (k + 2) i = ((k + 2) - (k + 2) / 2) + attnFun ((k + 2) / 2) ⟨i.val, h⟩ := by
  rw [attnFun_succ_succ]
  simp only [dite_eq_left h]

/-- A partner's value: it is the item whose rank is the value of the winner it is paired with. -/
theorem attnFun_item {k : ℕ} (i : Fin (k + 2)) (h1 : ¬ i.val < (k + 2) / 2)
    (h2 : i.val < 2 * ((k + 2) / 2)) :
    attnFun (k + 2) i = attainVal ((k + 2) - (k + 2) / 2) 0
      (attnFun ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩) := by
  rw [attnFun_succ_succ]
  simp only [dite_eq_right h1, dite_eq_left h2]

/-- The unpaired element's value (odd `n`). -/
theorem attnFun_last {k : ℕ} (i : Fin (k + 2)) (h1 : ¬ i.val < (k + 2) / 2)
    (h2 : ¬ i.val < 2 * ((k + 2) / 2)) :
    attnFun (k + 2) i = attainVal ((k + 2) - (k + 2) / 2) 0 ((k + 2) / 2) := by
  rw [attnFun_succ_succ]
  simp only [dite_eq_right h1, dite_eq_right h2]

/-- Every value of the attaining input is a position: the input is a permutation of `[0, n)`. -/
theorem attnFun_lt (n : ℕ) : ∀ i : Fin n, attnFun n i < n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => intro i; exact absurd i.isLt (by omega)
    | 1 => intro i; rw [attnFun]; show (0 : ℕ) < 1; omega
    | k + 2 =>
      intro i
      have hm : (k + 2) / 2 < k + 2 := by omega
      by_cases h : i.val < (k + 2) / 2
      · rw [attnFun_winner i h]
        have := ih ((k + 2) / 2) hm ⟨i.val, h⟩
        have := one_le_sub_div (k + 2) (by omega)
        omega
      · by_cases h2 : i.val < 2 * ((k + 2) / 2)
        · rw [attnFun_item i h h2]
          have := ih ((k + 2) / 2) hm ⟨i.val - (k + 2) / 2, by omega⟩
          have hM := one_le_sub_div (k + 2) (by omega)
          have := attainVal_lt ((k + 2) - (k + 2) / 2) 0 (attnFun ((k + 2) / 2)
            ⟨i.val - (k + 2) / 2, by omega⟩) (by omega)
          omega
        · rw [attnFun_last i h h2]
          have hM := one_le_sub_div (k + 2) (by omega)
          have := attainVal_lt ((k + 2) - (k + 2) / 2) 0 ((k + 2) / 2) (by omega)
          omega

/-- The winner block of the attaining input starts at `M = n - n/2`. -/
theorem attnFun_winner_ge {k : ℕ} (i : Fin (k + 2)) (h : i.val < (k + 2) / 2) :
    (k + 2) - (k + 2) / 2 ≤ attnFun (k + 2) i := by
  rw [attnFun_winner i h]
  exact Nat.le_add_right _ _

/-- Every value below the winner block is below `M`. -/
theorem attnFun_nonwinner_lt {k : ℕ} (i : Fin (k + 2)) (h : ¬ i.val < (k + 2) / 2) :
    attnFun (k + 2) i < (k + 2) - (k + 2) / 2 := by
  have hm : (k + 2) / 2 < k + 2 := by omega
  by_cases h2 : i.val < 2 * ((k + 2) / 2)
  · rw [attnFun_item i h h2]
    have hlt := attnFun_lt ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩
    have hj : attnFun ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩
        < (k + 2) - (k + 2) / 2 := by omega
    simpa only [Nat.zero_add] using attainVal_lt ((k + 2) - (k + 2) / 2) 0
      (attnFun ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩) hj
  · rw [attnFun_last i h h2]
    have hodd : 2 * ((k + 2) / 2) < k + 2 := by omega
    simpa only [Nat.zero_add] using
      attainVal_lt ((k + 2) - (k + 2) / 2) 0 ((k + 2) / 2) (by omega)

/-- **The attaining input is injective.** -/
theorem attnFun_injective (n : ℕ) : Function.Injective (attnFun n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => exact fun i => i.elim0
    | 1 => exact fun i j _ => Subsingleton.elim i j
    | k + 2 =>
      have hm : (k + 2) / 2 < k + 2 := by omega
      intro i j hij
      by_cases hi : i.val < (k + 2) / 2
      · by_cases hj : j.val < (k + 2) / 2
        · rw [attnFun_winner i hi, attnFun_winner j hj] at hij
          have h1 : attnFun ((k + 2) / 2) ⟨i.val, hi⟩ = attnFun ((k + 2) / 2) ⟨j.val, hj⟩ := by
            omega
          have h2 := ih ((k + 2) / 2) hm h1
          exact Fin.ext (by simpa using congrArg Fin.val h2)
        · exact absurd hij (by
            have h2 := attnFun_nonwinner_lt j hj
            rw [attnFun_winner i hi] at hij
            omega)
      · by_cases hj : j.val < (k + 2) / 2
        · exact absurd hij (by
            have h2 := attnFun_nonwinner_lt i hi
            rw [attnFun_winner j hj] at hij
            omega)
        · by_cases h2i : i.val < 2 * ((k + 2) / 2)
          · by_cases h2j : j.val < 2 * ((k + 2) / 2)
            · rw [attnFun_item i hi h2i, attnFun_item j hj h2j] at hij
              have hlti := attnFun_lt ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩
              have hltj := attnFun_lt ((k + 2) / 2) ⟨j.val - (k + 2) / 2, by omega⟩
              have h3 : attnFun ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩
                  = attnFun ((k + 2) / 2) ⟨j.val - (k + 2) / 2, by omega⟩ :=
                attainVal_inj (M := (k + 2) - (k + 2) / 2) (K := 0)
                  (j := attnFun ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩)
                  (j' := attnFun ((k + 2) / 2) ⟨j.val - (k + 2) / 2, by omega⟩)
                  (by omega) (by omega) hij
              have h4 := ih ((k + 2) / 2) hm h3
              have h5 : i.val - (k + 2) / 2 = j.val - (k + 2) / 2 := by
                simpa using congrArg Fin.val h4
              exact Fin.ext (by omega)
            · exact absurd hij (by
                have hlti := attnFun_lt ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩
                have hodd : 2 * ((k + 2) / 2) < k + 2 := by omega
                rw [attnFun_item i hi h2i, attnFun_last j hj h2j] at hij
                have h6 : attnFun ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩
                    = (k + 2) / 2 :=
                  attainVal_inj (M := (k + 2) - (k + 2) / 2) (K := 0)
                    (j := attnFun ((k + 2) / 2) ⟨i.val - (k + 2) / 2, by omega⟩)
                    (j' := (k + 2) / 2) (by omega) (by omega) hij
                omega)
          · by_cases h2j : j.val < 2 * ((k + 2) / 2)
            · exact absurd hij (by
                have hltj := attnFun_lt ((k + 2) / 2) ⟨j.val - (k + 2) / 2, by omega⟩
                have hodd : 2 * ((k + 2) / 2) < k + 2 := by omega
                rw [attnFun_item j hj h2j, attnFun_last i hi h2i] at hij
                have h6 : attnFun ((k + 2) / 2) ⟨j.val - (k + 2) / 2, by omega⟩
                    = (k + 2) / 2 :=
                  attainVal_inj (M := (k + 2) - (k + 2) / 2) (K := 0)
                    (j := attnFun ((k + 2) / 2) ⟨j.val - (k + 2) / 2, by omega⟩)
                    (j' := (k + 2) / 2) (by omega) (by omega) hij.symm
                omega)
            · exact Fin.ext (by
                have hodd : 2 * ((k + 2) / 2) < k + 2 := by omega
                have := i.isLt
                have := j.isLt
                omega)

/-! ### The pairing stage and the transported state -/

/-- The pairing stage costs exactly `n/2` comparisons: every leaf is at depth `n/2`. -/
theorem cost_pairAux_eq (m : ℕ) (hm : 2 * m ≤ n) :
    ∀ (k : ℕ) (hk : k ≤ m) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℕ),
      cost (pairAux m hm k hk σ) x = k
  | 0, _, σ, x => rfl
  | k + 1, hk, σ, x => by
    simp only [pairAux, cost]
    have h1 := cost_pairAux_eq m hm k (by omega) (σ * Equiv.swap ⟨k, by omega⟩ ⟨m + k, by omega⟩) x
    have h2 := cost_pairAux_eq m hm k (by omega) σ x
    split_ifs <;> omega

theorem cost_pairTree (n : ℕ) (x : Fin n → ℕ) : cost (pairTree n) x = n / 2 :=
  cost_pairAux_eq (n / 2) (Nat.mul_div_le n 2) (n / 2) le_rfl 1 x

/-- If the winner of every pair is in the lower slot, the pairing stage does not move at all. -/
theorem run_pairAux_one (m : ℕ) (hm : 2 * m ≤ n) (x : Fin n → ℕ)
    (hx : ∀ (t : ℕ) (ht : t < m), x ⟨m + t, by omega⟩ < x ⟨t, by omega⟩) :
    ∀ (k : ℕ) (hk : k ≤ m), run (pairAux m hm k hk (1 : Equiv.Perm (Fin n))) x = 1
  | 0, _ => rfl
  | k + 1, hk => by
    have hlt : k < m := by omega
    simp only [pairAux, run]
    have hcmp : ¬ x ((1 : Equiv.Perm (Fin n)) ⟨k, by omega⟩)
        < x ((1 : Equiv.Perm (Fin n)) ⟨m + k, by omega⟩) := by
      have h := hx k hlt
      simpa using not_lt.mpr (le_of_lt h)
    rw [ite_eq_right hcmp]
    exact run_pairAux_one m hm x hx k (by omega)

theorem run_pairTree_one (n : ℕ) (x : Fin n → ℕ)
    (hx : ∀ (t : ℕ) (ht : t < n / 2), x ⟨n / 2 + t, by omega⟩ < x ⟨t, by omega⟩) :
    run (pairTree n) x = 1 :=
  run_pairAux_one (n / 2) (Nat.mul_div_le n 2) x hx (n / 2) le_rfl

/-- At the start of the phase the pending block is in rank order. -/
theorem tailRank_zero (M r : ℕ) : tailRank M 0 0 r = r := by
  have h0 : jacLo M 0 = 0 := by simp [jacLo, jacPred]
  have hc : cntB M 0 = jacHi M 0 := by simp only [cntB, h0, Nat.sub_zero]
  by_cases h : r < cntB M 0
  · rw [tailRank, ite_eq_left (by omega), h0, Nat.zero_add]
  · rw [tailRank, ite_eq_right (by omega), hc]
    omega

/-- **The state the insertion phase starts from**, for the attaining input: the `o`-th smallest
winner in slot `o` with value `M + o`, its partner in slot `m + o` with value `attainVal M 0 o`,
and the unpaired element of an odd input last. -/
theorem arranged_transport {m M : ℕ} (hm : 2 * m ≤ n) (hMn : m + M = n) (hM : M ≤ m + 1)
    (x : Fin n → ℕ)
    (τ : Equiv.Perm (Fin m))
    (hw : ∀ o : Fin m, x ⟨(τ o).val, by have := (τ o).isLt; omega⟩ = M + o.val)
    (hl : ∀ o : Fin m, x ⟨m + (τ o).val, by have := (τ o).isLt; omega⟩
      = attainVal M 0 o.val)
    (hlast : ∀ (h : 2 * m < n), x ⟨2 * m, h⟩ = attainVal M 0 m) :
    Arranged x m M 0 0 (transport m hm (1 : Equiv.Perm (Fin n)) τ) := by
  have hj0 : jacLo M 0 = 0 := by simp [jacLo, jacPred]
  have hcl : chainLen m M 0 0 = m := by simp only [chainLen, hj0, Nat.add_zero]
  intro s
  rcases lt_or_ge s.val m with hs | hs
  · have htr : transport m hm (1 : Equiv.Perm (Fin n)) τ s
        = ⟨(τ ⟨s.val, hs⟩).val, by have := (τ ⟨s.val, hs⟩).isLt; omega⟩ :=
      transport_winner (o := s.val) m hm 1 τ hs
    rw [htr, hw ⟨s.val, hs⟩]
    have h1 : ¬ s.val < jacLo M 0 + 0 := by simp only [hj0, Nat.add_zero]; omega
    have h2 : s.val < chainLen m M 0 0 := by rw [hcl]; exact hs
    rw [slotVal_of_winner h1 h2, hj0, Nat.add_zero, Nat.sub_zero]
  · rcases lt_or_ge s.val (2 * m) with hs2 | hs2
    · have hse : s = (⟨m + (s.val - m), by omega⟩ : Fin n) := Fin.ext (by simp only; omega)
      have htr0 := transport_loser (o := s.val - m) m hm (1 : Equiv.Perm (Fin n)) τ
        (show s.val - m < m by omega)
      have hped : pendIdx m (show s.val - m < m by omega) = (⟨s.val - m, by omega⟩ : Fin m) := by
        refine Fin.ext ?_
        rw [pendIdx_val]
      have hfin : (1 : Equiv.Perm (Fin n))
            ⟨m + (τ (pendIdx m (show s.val - m < m by omega))).val, by
              have := (τ (pendIdx m (show s.val - m < m by omega))).isLt; omega⟩
          = ⟨m + (τ ⟨s.val - m, by omega⟩).val, by
              have := (τ ⟨s.val - m, by omega⟩).isLt; omega⟩ := by
        refine Fin.ext ?_
        exact congrArg (fun v => m + v) (congrArg Fin.val (congrArg τ hped))
      have htr : transport m hm (1 : Equiv.Perm (Fin n)) τ ⟨m + (s.val - m), by omega⟩
          = ⟨m + (τ ⟨s.val - m, by omega⟩).val, by
              have := (τ ⟨s.val - m, by omega⟩).isLt; omega⟩ := htr0.trans hfin
      rw [hse, htr, hl ⟨s.val - m, by omega⟩]
      have hv : (⟨m + (s.val - m), by omega⟩ : Fin n).val = m + (s.val - m) := rfl
      have h1 : ¬ (⟨m + (s.val - m), by omega⟩ : Fin n).val < jacLo M 0 + 0 := by
        rw [hv]; simp only [hj0, Nat.add_zero]; omega
      have h2 : ¬ (⟨m + (s.val - m), by omega⟩ : Fin n).val < chainLen m M 0 0 := by
        rw [hv, hcl]; omega
      rw [slotVal_of_pending h1 h2, hcl, tailRank_zero]
      congr 1
      simp only [Fin.val_mk]
      omega
    · have hsv : s.val = 2 * m := by omega
      have hse : s = (⟨2 * m, by omega⟩ : Fin n) := Fin.ext (by simp only; omega)
      have htr : transport m hm (1 : Equiv.Perm (Fin n)) τ ⟨2 * m, by omega⟩
          = ⟨2 * m, by omega⟩ := transport_last m hm (by omega) 1 τ
      rw [hse, htr, hlast (by omega)]
      have hv : (⟨2 * m, by omega⟩ : Fin n).val = 2 * m := rfl
      have h1 : ¬ (⟨2 * m, by omega⟩ : Fin n).val < jacLo M 0 + 0 := by
        rw [hv]; simp only [hj0, Nat.add_zero]; omega
      have h2 : ¬ (⟨2 * m, by omega⟩ : Fin n).val < chainLen m M 0 0 := by
        rw [hv, hcl]; omega
      rw [slotVal_of_pending h1 h2, hcl, tailRank_zero]
      congr 1
      omega

/-! ### The count is attained -/

theorem fjTreeFuel_cost_attn : ∀ (fuel n : ℕ), n ≤ fuel →
    cost (fjTreeFuel fuel n) (attnFun n) = fjCountJ n
  | 0, n, hn => by
    have hn0 : n = 0 := by omega
    subst hn0
    simp only [fjTreeFuel, cost]
    exact (fjCountJ_eq_zero 0 (by omega)).symm
  | fuel + 1, 0, _ => by
    simp only [fjTreeFuel, cost]
    exact (fjCountJ_eq_zero 0 (by omega)).symm
  | fuel + 1, 1, _ => by
    simp only [fjTreeFuel, cost]
    exact (fjCountJ_eq_zero 1 (by omega)).symm
  | fuel + 1, k + 2, _ => by
    have hm2 : 2 * ((k + 2) / 2) ≤ k + 2 := Nat.mul_div_le (k + 2) 2
    have hMn : (k + 2) / 2 + ((k + 2) - (k + 2) / 2) = k + 2 := by omega
    have hMle : (k + 2) - (k + 2) / 2 ≤ (k + 2) / 2 + 1 := sub_div_le (k + 2)
    have hM1 : 1 ≤ (k + 2) - (k + 2) / 2 := one_le_sub_div (k + 2) (by omega)
    have hm1 : 1 ≤ (k + 2) / 2 := by omega
    have hrec : cost (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2))
        = fjCountJ ((k + 2) / 2) := fjTreeFuel_cost_attn fuel ((k + 2) / 2) (by omega)
    -- the pairing stage decides every pair in favour of the winner
    have hpairs : ∀ (t : ℕ) (ht : t < (k + 2) / 2),
        attnFun (k + 2) ⟨(k + 2) / 2 + t, by omega⟩ < attnFun (k + 2) ⟨t, by omega⟩ := by
      intro t ht
      rw [attnFun_winner (i := (⟨t, by omega⟩ : Fin (k + 2))) ht]
      have hlt := attnFun_nonwinner_lt (i := (⟨(k + 2) / 2 + t, by omega⟩ : Fin (k + 2)))
        (by simp only [Fin.val_mk]; omega)
      have h2 : attnFun (k + 2) ⟨(k + 2) / 2 + t, by omega⟩
          < (k + 2) - (k + 2) / 2 := hlt
      omega
    rw [fjTreeFuel, cost_substTree, cost_pairTree, run_pairTree_one (k + 2) _ hpairs]
    -- the stage: the winners are sorted, transported, and the losers inserted
    have hsorts : Sorts (attnFun ((k + 2) / 2))
        (run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2))) :=
      (fjTreeFuel_correct fuel ((k + 2) / 2) (by omega)) _ (attnFun_injective _)
    have hτval : ∀ o : Fin ((k + 2) / 2),
        attnFun ((k + 2) / 2) ((run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2))) o)
          = o.val :=
      eq_val_of_strictMono hsorts (fun i => attnFun_lt _ ((run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2))) i))
    have hwin : ∀ o : Fin ((k + 2) / 2),
        attnFun (k + 2) ⟨((run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2))) o).val,
          by have := (run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2)) o).isLt; omega⟩
          = ((k + 2) - (k + 2) / 2) + o.val := by
      intro o
      have hlt : ((run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2))) o).val
          < (k + 2) / 2 := (run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2)) o).isLt
      rw [attnFun_winner (i := (⟨((run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2))) o).val,
        by omega⟩ : Fin (k + 2))) hlt]
      congr 1
      exact hτval o
    have hitem : ∀ o : Fin ((k + 2) / 2),
        attnFun (k + 2) ⟨(k + 2) / 2 + ((run (fjTreeFuel fuel ((k + 2) / 2))
            (attnFun ((k + 2) / 2))) o).val,
          by have := (run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2)) o).isLt; omega⟩
          = attainVal ((k + 2) - (k + 2) / 2) 0 o.val := by
      intro o
      have hlt : ((run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2))) o).val
          < (k + 2) / 2 := (run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2)) o).isLt
      rw [attnFun_item (i := (⟨(k + 2) / 2 + ((run (fjTreeFuel fuel ((k + 2) / 2))
        (attnFun ((k + 2) / 2))) o).val, by omega⟩ : Fin (k + 2))) (by simp only [Fin.val_mk]; omega)
        (by simp only [Fin.val_mk]; omega)]
      congr 1
      have hidx : (⟨(k + 2) / 2 + ((run (fjTreeFuel fuel ((k + 2) / 2))
          (attnFun ((k + 2) / 2))) o).val - (k + 2) / 2, by omega⟩ : Fin ((k + 2) / 2))
          = (run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2))) o :=
        Fin.ext (by simp only [Fin.val_mk]; omega)
      rw [hidx]
      exact hτval o
    have hlast : ∀ (h : 2 * ((k + 2) / 2) < k + 2),
        attnFun (k + 2) ⟨2 * ((k + 2) / 2), h⟩ = attainVal ((k + 2) - (k + 2) / 2) 0 ((k + 2) / 2) := by
      intro h
      rw [attnFun_last (i := (⟨2 * ((k + 2) / 2), h⟩ : Fin (k + 2)))
        (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
    have harr := arranged_transport hm2 hMn hMle (attnFun (k + 2))
      (run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2))) hwin hitem hlast
    have himg : cost (imageTree (fun i : Fin ((k + 2) / 2) =>
          (1 : Equiv.Perm (Fin (k + 2))) ⟨i.val, by have := i.isLt; omega⟩)
        (fun τ => transport ((k + 2) / 2) hm2 (1 : Equiv.Perm (Fin (k + 2))) τ)
        (fjTreeFuel fuel ((k + 2) / 2))) (attnFun (k + 2)) = fjCountJ ((k + 2) / 2) := by
      rw [cost_imageTree]
      have hfun : (fun i : Fin ((k + 2) / 2) => attnFun (k + 2)
          ((1 : Equiv.Perm (Fin (k + 2))) ⟨i.val, by have := i.isLt; omega⟩))
          = fun i : Fin ((k + 2) / 2) => ((k + 2) - (k + 2) / 2) + attnFun ((k + 2) / 2) i := by
        funext i
        exact attnFun_winner (i := (⟨i.val, by omega⟩ : Fin (k + 2))) i.isLt
      rw [hfun, cost_add_const, hrec]
    have hrunimg : run (imageTree (fun i : Fin ((k + 2) / 2) =>
          (1 : Equiv.Perm (Fin (k + 2))) ⟨i.val, by have := i.isLt; omega⟩)
        (fun τ => transport ((k + 2) / 2) hm2 (1 : Equiv.Perm (Fin (k + 2))) τ)
        (fjTreeFuel fuel ((k + 2) / 2))) (attnFun (k + 2))
        = transport ((k + 2) / 2) hm2 (1 : Equiv.Perm (Fin (k + 2)))
          (run (fjTreeFuel fuel ((k + 2) / 2)) (attnFun ((k + 2) / 2))) := by
      rw [run_imageTree]
      have hfun : (fun i : Fin ((k + 2) / 2) => attnFun (k + 2)
          ((1 : Equiv.Perm (Fin (k + 2))) ⟨i.val, by have := i.isLt; omega⟩))
          = fun i : Fin ((k + 2) / 2) => ((k + 2) - (k + 2) / 2) + attnFun ((k + 2) / 2) i := by
        funext i
        exact attnFun_winner (i := (⟨i.val, by omega⟩ : Fin (k + 2))) i.isLt
      rw [hfun, run_add_const]
    rw [fjStage, cost_substTree, himg, hrunimg,
      insPhase_cost hm1 (by omega) hMn hMle hM1 (attnFun_injective (k + 2)) harr]
    rw [fjCountJ_le_recurrence (k + 2) (by omega),
      show (k + 2 + 1) / 2 = (k + 2) - (k + 2) / 2 from (sub_div_eq (k + 2)).symm]
    omega

/-- **The depth bound of `fjTree` is attained.**  There is an input on which the tree of
merge-insertion makes exactly `fjCountJ n` comparisons — every comparison of the analysis
happens: `n/2` pairings, the winner tree's `fjCountJ (n/2)`, and `jacInsertCost ⌈n/2⌉` for the
insertion phase, where each of the `jacHi - jacLo` searches of a batch descends its deepest
branch.  So `fjCountJ n` is the exact cost of `fjTree n` on a worst-case input, the tree-side
analogue of `FordJohnson.fjCountJ_attains`. -/
theorem fjTree_cost_attains (n : ℕ) :
    ∃ x : Fin n → ℕ, Function.Injective x ∧ cost (fjTree n) x = fjCountJ n :=
  ⟨attnFun n, attnFun_injective n, fjTreeFuel_cost_attn n n le_rfl⟩

/-- **The depth bound is exact, not merely attained.**  `cost ≤ depth ≤ fjCountJ` and some
input costs `fjCountJ n`, so the depth of `fjTree n` *is* `fjCountJ n`: no leaf of the tree is
deeper than the count and at least one leaf is exactly that deep. -/
theorem fjTree_depth_eq (n : ℕ) : depth (fjTree n) = fjCountJ n := by
  have h1 := fjTree_depth_le n
  have h2 := cost_le_depth (fjTree n) (attnFun n)
  have h3 : cost (fjTree n) (attnFun n) = fjCountJ n := fjTreeFuel_cost_attn n n le_rfl
  omega

end SortBounds.Projects.FjTree
