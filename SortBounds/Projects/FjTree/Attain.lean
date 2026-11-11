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

namespace SortBounds.Projects.FjTree

open SortBounds
open SortBounds.Projects.FordJohnson (jac jacPred jac_pos le_jac jacPred_succ jacInsertCost
  jacInsertCostAux fjCountJ fjCountJ_eq_zero fjCountJ_le_recurrence attainVal attainT
  jacBatchOf jacBatchOf_eq_of_mem attainVal_lt clog_half_eq)

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
    (hm : hi - lo ≤ fuel) (hle : lo ≤ hi) (hjq : lo ≤ q),
    ∀ (σ : Equiv.Perm (Fin n)) (next : Equiv.Perm (Fin n) → Tree n) (x : Fin n → ℕ),
    Function.Injective x → ChainSorted x σ c → rankAt x σ c ⟨q, hqn⟩ = lo →
    cost (binIns fuel lo hi c q hqn hcq hhi σ next) x
      = Nat.clog 2 (hi - lo + 1) + cost (next (insertAt lo q hjq hqn σ)) x
  | 0, lo, hi, c, q, hqn, hcq, hhi, _hm, _hle, hjq, σ, next, x, hx, hchain, hrank => by
    simp only [binIns]
    obtain rfl : hi = lo := by omega
    rw [Nat.sub_self, Nat.clog_one_right, Nat.zero_add]
  | fuel + 1, lo, hi, c, q, hqn, hcq, hhi, hm, hle, hjq, σ, next, x, hx, hchain, hrank => by
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
  simp only [attainVal, attainT, hb, Nat.zero_add]

/-- The item sitting in the batch's item slot is the one being inserted. -/
theorem tailRank_itemSlot (M k p : ℕ) (hp : p < cntB M k) :
    tailRank M k p (itemSlot m M k - chainLen m M k p) = jacHi M k - 1 - p := by
  have hle := jacLo_le_jacHi M k
  have h1 : itemSlot m M k - chainLen m M k p = cntB M k - 1 - p := by
    simp only [itemSlot, chainLen, cntB]
    omega
  have h2 : cntB M k - 1 - p + p < cntB M k := by omega
  rw [h1, tailRank, ite_eq_left h2]
  omega

/-- **The value in the item slot** is the value of the item about to be inserted: the
`(jacLo+p)`-th insertion of the phase. -/
theorem slotVal_itemSlot {m M k p : ℕ} (hp : p < cntB M k) :
    slotVal m M k p (itemSlot m M k) = M - 1 - (jacLo M k + p) := by
  have h1 := jacLo_add_p_lt_jacHi M k p hp
  have h2 := jacLo_add_p_le_chainLen m M k p
  have h3 : ¬ itemSlot m M k < jacLo M k + p := by
    simp only [itemSlot, chainLen, cntB] at h1 h2 ⊢
    omega
  have h4 : ¬ itemSlot m M k < chainLen m M k p := by
    simp only [itemSlot, chainLen, cntB] at h1 h2 ⊢
    omega
  rw [slotVal, if_neg h3, if_neg h4, tailRank_itemSlot M k p hp, attainVal_of_mem
    (by omega : jacLo M k ≤ jacHi M k - 1 - p) h1]
  have h5 := jacLo_le_jacHi M k
  have h6 := jacHi_pos M k
  simp only [chainLen]
  omega
