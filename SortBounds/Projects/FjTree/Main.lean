/-
SortBounds/Projects/FjTree/Main.lean

**The decision tree of merge-insertion.**  This file assembles the stages of
`SortBounds/Projects/FjTree/Setup.lean` into one `Tree n` and bounds its depth by
`fjCountJ n`, the literature's comparison count:

* `pairTree` — `n/2` comparisons put the winner of each pair in slot `k` (`k < n/2`);
* the recursive tree `fjTree (n/2)` (embedded by `imageTree`) sorts the winners;
  the state afterwards is `transport`'s: winners in slots `0 … m-1`, their losers in
  slots `m … n-1`;
* `insBatch`/`insBatches` — the insertion phase: the losers are inserted in Jacobsthal
  order, each in a window of `jacLo + jacHi` slots (`jacLo`/`jacHi` are the batch
  boundaries of `FordJohnson.Jacobsthal`), which makes the depth at most
  `jacInsertCost` — the same sum by construction, so no arithmetic identification is
  needed.

`fjTree n = fjTreeFuel n n` (fuel = the halvings, so the recursion is structural), and

  `fjTree_depth_le : depth (fjTree n) ≤ fjCountJ n`.

**What is not here: `fjTree_correct`.**  The depth is proved; correctness still needs the
invariant of the insertion phase (see the lane's `README.md`, "What remains").  The
layout it will use is fixed by `transport`: the pending losers are ordered by their
partner's *rank*, so the loser of the `t`-th smallest winner sits in slot `m + t - 1`,
whence the item slot `m + jacHi M k - 1` of `insBatch` is constant within a batch, and
the window `jacLo + jacHi - 1` of `binIns` is exactly `(t - 1) + (#already inserted)` —
zero slack, which is why the count is tight.
-/
import SortBounds.Projects.FjTree.Setup

namespace SortBounds.Projects.FjTree

open SortBounds
open SortBounds.Projects.FordJohnson (jac jacPred jacPred_le_jac jac_pos le_jac jacPred_succ
  jacInsertCost jacInsertCostAux fjCountJ fjCountJ_eq_zero fjCountJ_le_recurrence)

variable {n : ℕ}

/-! ### The Jacobsthal batches -/

/-- Number of items inserted before batch `k` (and the last rank of batch `k-1`). -/
def jacLo (M k : ℕ) : ℕ := min M (jacPred k)

/-- One past the last rank of batch `k`. -/
def jacHi (M k : ℕ) : ℕ := min M (jac k)

theorem jacLo_succ (M k : ℕ) : jacLo M (k + 1) = jacHi M k := rfl

theorem jacLo_le_jacHi (M k : ℕ) : jacLo M k ≤ jacHi M k :=
  min_le_min_left M (jacPred_le_jac k)

theorem jacLo_le (M k : ℕ) : jacLo M k ≤ M := min_le_left M _

theorem jacHi_le (M k : ℕ) : jacHi M k ≤ M := min_le_left M _

theorem jacHi_pos (M k : ℕ) (hM : 1 ≤ M) : 1 ≤ jacHi M k := le_min hM (jac_pos k)

/-- All `M` items are inserted after `M` batches. -/
theorem jacLo_self (M : ℕ) (hM : 1 ≤ M) : jacLo M M = M := by
  have h : M ≤ jacPred M := by
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    show k + 1 ≤ jacPred (k + 1)
    rw [jacPred_succ]
    exact le_jac k
  simp only [jacLo, min_eq_left h]

/-! ### The insertion phase -/

/-- The number of items of batch `k`. -/
def cntB (M k : ℕ) : ℕ := jacHi M k - jacLo M k

/-- The chain length of batch `k` at position `p` (i.e. with `p` items of the batch already
inserted). -/
def chainLen (m M k p : ℕ) : ℕ := m + jacLo M k + p

/-- The slot the items of batch `k` come from: the insertions shift the next item of the
batch up into exactly this slot. -/
def itemSlot (m M k : ℕ) : ℕ := m + jacHi M k - 1

/-- The window of every item of batch `k`: the `jacLo` winners below the partner plus the
`jacHi` items in the chain once the batch is done, minus one. -/
def winWindow (M k : ℕ) : ℕ := jacLo M k + jacHi M k - 1

/-- The item slot of batch `k` is a slot of the arrangement. -/
theorem itemSlot_lt (m M k : ℕ) (hmM : m + M ≤ n) (hM1 : 1 ≤ M) : itemSlot m M k < n := by
  have h1 := jacHi_le M k
  have h2 := jacHi_pos M k hM1
  simp only [itemSlot]
  omega

/-- The item slot of batch `k` lies above every chain length the batch visits. -/
theorem chainLen_le_itemSlot (m M k p : ℕ) (hp : p < cntB M k) :
    chainLen m M k p ≤ itemSlot m M k := by
  have h := jacLo_le_jacHi M k
  simp only [chainLen, itemSlot, cntB] at *
  omega

/-- The window of batch `k` is inside the chain the batch visits. -/
theorem winWindow_le_chainLen (m M k p : ℕ) (hM : M ≤ m + 1) (hM1 : 1 ≤ M) :
    winWindow M k ≤ chainLen m M k p := by
  have h1 := jacHi_le M k
  have h2 := jacHi_pos M k hM1
  simp only [winWindow, chainLen]
  omega

/-- The window of batch `k` is inside the item slot of a nonempty batch. -/
theorem winWindow_le_itemSlot (m M k : ℕ) (hM : M ≤ m + 1) (hcnt : 0 < cntB M k) :
    winWindow M k ≤ itemSlot m M k := by
  have h1 := jacHi_le M k
  have h2 := jacLo_le_jacHi M k
  simp only [winWindow, itemSlot, cntB] at *
  omega

/-- Insert the items of batch `k` (there are `jacHi M k - jacLo M k` of them, the highest
rank first), starting at position `cntB - 1 - j` (`j` counts insertions still to come), then continue with `next`.  Every item of a batch
is searched for in the same window `[0, jacLo + jacHi - 1)`, and the pending item of rank
`t` sits in slot `m + t - 1`, so the item slot `m + jacHi - 1` is constant within the
batch while the chain grows. -/
noncomputable def insBatch (m M : ℕ) (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M)
    (next : Equiv.Perm (Fin n) → Tree n) :
    (k : ℕ) → (j : ℕ) → j ≤ cntB M k → Equiv.Perm (Fin n) → Tree n
  | k, 0, _, σ => next σ
  | k, j + 1, hj, σ =>
    binIns (winWindow M k) 0 (winWindow M k)
      (chainLen m M k (cntB M k - 1 - j)) (itemSlot m M k)
      (itemSlot_lt m M k hmM hM1)
      (chainLen_le_itemSlot m M k (cntB M k - 1 - j) (by omega))
      (winWindow_le_chainLen m M k (cntB M k - 1 - j) hM hM1)
      σ (insBatch m M hmM hM hM1 next k j (by omega))

/-- One unfolding step of `insBatch`: it searches for the item at position `j` of the
batch, i.e. the last one the batch still has to insert. -/
theorem insBatch_succ (m M : ℕ) (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M)
    (next : Equiv.Perm (Fin n) → Tree n) (k j : ℕ) (hj : j + 1 ≤ cntB M k)
    (σ : Equiv.Perm (Fin n)) :
    insBatch m M hmM hM hM1 next k (j + 1) hj σ
      = binIns (winWindow M k) 0 (winWindow M k) (chainLen m M k (cntB M k - 1 - j))
          (itemSlot m M k) (itemSlot_lt m M k hmM hM1)
          (chainLen_le_itemSlot m M k (cntB M k - 1 - j) (by omega))
          (winWindow_le_chainLen m M k (cntB M k - 1 - j) hM hM1) σ
          (insBatch m M hmM hM hM1 next k j (by omega)) := rfl

/-- The insertion phase: `fuel` batches starting at batch `k`. -/
noncomputable def insBatches (m M : ℕ) (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M)
    (next : Equiv.Perm (Fin n) → Tree n) :
    (fuel k : ℕ) → Equiv.Perm (Fin n) → Tree n
  | 0, _, σ => next σ
  | fuel + 1, k, σ =>
    insBatch m M hmM hM hM1 (insBatches m M hmM hM hM1 next fuel (k + 1)) k
      (jacHi M k - jacLo M k) le_rfl σ

/-- **Depth of one batch**: `jacHi - jacLo - j` searches, each of depth at most
`⌈log₂ (jacLo + jacHi)⌉`. -/
theorem insBatch_depth (m M : ℕ) (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M)
    (next : Equiv.Perm (Fin n) → Tree n) (B : ℕ) (hB : ∀ σ, depth (next σ) ≤ B) :
    ∀ (k j : ℕ) (hj : j ≤ cntB M k) (σ : Equiv.Perm (Fin n)),
      depth (insBatch m M hmM hM hM1 next k j hj σ)
        ≤ j * Nat.clog 2 (jacLo M k + jacHi M k) + B := by
  intro k j
  induction j with
  | zero =>
    intro hj σ
    simp only [insBatch]
    have := hB σ
    omega
  | succ j ih =>
    intro hj σ
    have hstep := binIns_depth_le (winWindow M k) 0 (winWindow M k)
      (chainLen m M k (cntB M k - 1 - j))
      (itemSlot m M k) (itemSlot_lt m M k hmM hM1)
      (chainLen_le_itemSlot m M k (cntB M k - 1 - j) (by omega))
      (winWindow_le_chainLen m M k (cntB M k - 1 - j) hM hM1) σ
      (insBatch m M hmM hM hM1 next k j (by omega))
      (j * Nat.clog 2 (jacLo M k + jacHi M k) + B)
      (fun σ' => ih (by omega) σ') (by omega)
    have hlog : Nat.clog 2 (winWindow M k - 0 + 1)
        = Nat.clog 2 (jacLo M k + jacHi M k) := by
      have hp := jacHi_pos M k hM1
      simp only [winWindow]
      rw [Nat.sub_zero]
      congr 1
      omega
    rw [hlog] at hstep
    rw [insBatch_succ]
    calc depth (binIns (winWindow M k) 0 (winWindow M k)
          (chainLen m M k (cntB M k - 1 - j)) (itemSlot m M k)
          _ _ _ σ (insBatch m M hmM hM hM1 next k j _))
        ≤ Nat.clog 2 (jacLo M k + jacHi M k)
            + (j * Nat.clog 2 (jacLo M k + jacHi M k) + B) := hstep
      _ = (j + 1) * Nat.clog 2 (jacLo M k + jacHi M k) + B := by ring

/-- **Depth of the insertion phase**: at most the Jacobsthal batch sum of
`FordJohnson.jacInsertCostAux`. -/
theorem insBatches_depth (m M : ℕ) (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M)
    (next : Equiv.Perm (Fin n) → Tree n) (B : ℕ) (hB : ∀ σ, depth (next σ) ≤ B) :
    ∀ (fuel k : ℕ) (σ : Equiv.Perm (Fin n)),
      depth (insBatches m M hmM hM hM1 next fuel k σ) ≤ jacInsertCostAux M fuel k + B := by
  intro fuel
  induction fuel with
  | zero =>
    intro k σ
    simp only [insBatches, jacInsertCostAux]
    have := hB σ
    omega
  | succ fuel ih =>
    intro k σ
    have hstep := insBatch_depth m M hmM hM hM1
      (insBatches m M hmM hM hM1 next fuel (k + 1)) (jacInsertCostAux M fuel (k + 1) + B)
      (fun σ' => ih (k + 1) σ') k (jacHi M k - jacLo M k) le_rfl σ
    show depth (insBatch m M hmM hM hM1 (insBatches m M hmM hM hM1 next fuel (k + 1)) k
        (jacHi M k - jacLo M k) le_rfl σ) ≤ jacInsertCostAux M (fuel + 1) k + B
    rw [show jacInsertCostAux M (fuel + 1) k
        = (jacHi M k - jacLo M k) * Nat.clog 2 (jacLo M k + jacHi M k)
          + jacInsertCostAux M fuel (k + 1) from rfl]
    have := hstep
    omega

/-- The insertion phase as a function of the state. -/
noncomputable def insPhase (m M : ℕ) (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M) :
    Equiv.Perm (Fin n) → Tree n :=
  insBatches m M hmM hM hM1 (fun σ => Tree.leaf σ) M 0

theorem insPhase_depth (m M : ℕ) (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M)
    (σ : Equiv.Perm (Fin n)) :
    depth (insPhase m M hmM hM hM1 σ) ≤ jacInsertCost M := by
  have h := insBatches_depth m M hmM hM hM1 (fun σ => Tree.leaf σ) 0
    (fun σ => by simp [depth]) M 0 σ
  simpa only [insPhase, jacInsertCost, Nat.add_zero] using h

/-! ### The stages of one level -/

/-- **One level of merge-insertion**: given the (already built) tree for the winners,
sort the winners, transport their losers into the pending block, and run the insertion
phase. -/
noncomputable def fjStage (m M : ℕ) (hm : 2 * m ≤ n) (hmM : m + M ≤ n) (hM : M ≤ m + 1)
    (hM1 : 1 ≤ M) (rec : Tree m) (ρ : Equiv.Perm (Fin n)) : Tree n :=
  substTree
    (imageTree (fun i : Fin m => ρ ⟨i.val, by have := i.isLt; omega⟩)
      (fun τ => transport m hm ρ τ) rec)
    (insPhase m M hmM hM hM1)

theorem fjStage_depth (m M : ℕ) (hm : 2 * m ≤ n) (hmM : m + M ≤ n) (hM : M ≤ m + 1)
    (hM1 : 1 ≤ M) (rec : Tree m) (ρ : Equiv.Perm (Fin n)) :
    depth (fjStage m M hm hmM hM hM1 rec ρ) ≤ depth rec + jacInsertCost M := by
  have h := depth_substTree_le
    (imageTree (fun i : Fin m => ρ ⟨i.val, by have := i.isLt; omega⟩)
      (fun τ => transport m hm ρ τ) rec)
    (insPhase m M hmM hM hM1) (jacInsertCost M) (fun σ => insPhase_depth m M hmM hM hM1 σ)
  rw [depth_imageTree] at h
  exact h

/-! ### The tree -/

/-- `k - k/2 ≤ k/2 + 1`: the number of items is at most one more than the number of
winners. -/
theorem sub_div_le (k : ℕ) : k - k / 2 ≤ k / 2 + 1 := by
  have h1 : 2 * (k / 2) + k % 2 = k := Nat.div_add_mod k 2
  have h2 : k % 2 < 2 := Nat.mod_lt k (by norm_num)
  omega

/-- `k - k/2 = (k+1)/2`: the two forms of the number of items. -/
theorem sub_div_eq (k : ℕ) : k - k / 2 = (k + 1) / 2 := by
  have h1 : 2 * (k / 2) + k % 2 = k := Nat.div_add_mod k 2
  have h2 : k % 2 < 2 := Nat.mod_lt k (by norm_num)
  have h3 : 2 * ((k + 1) / 2) + (k + 1) % 2 = k + 1 := Nat.div_add_mod (k + 1) 2
  have h4 : (k + 1) % 2 < 2 := Nat.mod_lt (k + 1) (by norm_num)
  omega

/-- At least one item. -/
theorem one_le_sub_div (k : ℕ) (h : 1 ≤ k) : 1 ≤ k - k / 2 := by
  have h1 : 2 * (k / 2) + k % 2 = k := Nat.div_add_mod k 2
  have h2 : k % 2 < 2 := Nat.mod_lt k (by norm_num)
  omega

/-- The number of halvings needed: the recursion on `k` is structural in the fuel. -/
noncomputable def fjTreeFuel : (fuel n : ℕ) → Tree n
  | 0, _ => Tree.leaf 1
  | fuel + 1, 0 => Tree.leaf 1
  | fuel + 1, 1 => Tree.leaf 1
  | fuel + 1, k + 2 =>
    substTree (pairTree (k + 2)) fun ρ =>
      fjStage ((k + 2) / 2) ((k + 2) - (k + 2) / 2) (Nat.mul_div_le (k + 2) 2)
        (by omega) (sub_div_le (k + 2))
        (one_le_sub_div (k + 2) (by omega))
        (fjTreeFuel fuel ((k + 2) / 2)) ρ

/-- **The decision tree of merge-insertion on `n` elements.** -/
noncomputable def fjTree (n : ℕ) : Tree n := fjTreeFuel n n

/-- **`depth (fjTree n) ≤ fjCountJ n`** for the tree built by `fjTree` — a depth bound
only; `fjTree_correct` is what makes the tree sort. -/
theorem fjTreeFuel_depth : ∀ (fuel k : ℕ), k ≤ fuel → depth (fjTreeFuel fuel k) ≤ fjCountJ k
  | 0, k, hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [fjTreeFuel, depth]
    exact le_of_eq (fjCountJ_eq_zero 0 (by omega)).symm
  | fuel + 1, 0, _ => by
    simp only [fjTreeFuel, depth]
    exact le_of_eq (fjCountJ_eq_zero 0 (by omega)).symm
  | fuel + 1, 1, _ => by
    simp only [fjTreeFuel, depth]
    exact le_of_eq (fjCountJ_eq_zero 1 (by omega)).symm
  | fuel + 1, k + 2, hk => by
    have hB : ∀ ρ : Equiv.Perm (Fin (k + 2)),
        depth (fjStage ((k + 2) / 2) ((k + 2) - (k + 2) / 2) (Nat.mul_div_le (k + 2) 2)
          (by omega) (sub_div_le (k + 2)) (one_le_sub_div (k + 2) (by omega))
          (fjTreeFuel fuel ((k + 2) / 2)) ρ)
          ≤ fjCountJ ((k + 2) / 2) + jacInsertCost ((k + 2) - (k + 2) / 2) := by
      intro ρ
      have h1 := fjStage_depth ((k + 2) / 2) ((k + 2) - (k + 2) / 2)
        (Nat.mul_div_le (k + 2) 2) (by omega) (sub_div_le (k + 2))
        (one_le_sub_div (k + 2) (by omega)) (fjTreeFuel fuel ((k + 2) / 2)) ρ
      have h2 := fjTreeFuel_depth fuel ((k + 2) / 2) (by omega)
      omega
    have hpair := depth_substTree_le (pairTree (k + 2))
      (fun ρ => fjStage ((k + 2) / 2) ((k + 2) - (k + 2) / 2) (Nat.mul_div_le (k + 2) 2)
        (by omega) (sub_div_le (k + 2)) (one_le_sub_div (k + 2) (by omega))
        (fjTreeFuel fuel ((k + 2) / 2)) ρ)
      (fjCountJ ((k + 2) / 2) + jacInsertCost ((k + 2) - (k + 2) / 2)) hB
    have hpt : depth (pairTree (k + 2)) = (k + 2) / 2 := by
      simp only [pairTree]
      exact (pairTree_spec (Nat.mul_div_le (k + 2) 2) (fun i => (i : ℕ))
        (fun _ _ h => Fin.ext h)).1
    have hrec2 : fjCountJ (k + 2) = (k + 2) / 2 + fjCountJ ((k + 2) / 2)
        + jacInsertCost ((k + 2) - (k + 2) / 2) := by
      rw [fjCountJ_le_recurrence (k + 2) (by omega),
        show (k + 2 + 1) / 2 = (k + 2) - (k + 2) / 2 from (sub_div_eq (k + 2)).symm]
    rw [hpt] at hpair
    simp only [fjTreeFuel]
    omega

theorem fjTree_depth_le (n : ℕ) : depth (fjTree n) ≤ fjCountJ n :=
  fjTreeFuel_depth n n le_rfl

end SortBounds.Projects.FjTree
