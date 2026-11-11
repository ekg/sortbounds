/-
SortBounds/Projects/FjTree/Correct.lean

**The tree of merge-insertion sorts.**  This is the obligation that the depth bound alone
does not settle: `fjTree n` is a correct comparison tree on `n` positions.

The tree runs the stages of `Main.fjStage`:

* `pairTree` decides every pair, putting the **larger** element of pair `k` in slot `k` and
  its smaller partner in slot `m + k` (`pairTree_spec`);
* the recursive tree on the `m` larger elements sorts them (`imageTree`);
* `transport` lays the sorted winners out in slots `0 … m-1` with the partner of the `o`-th
  smallest winner in slot `m + o` (`transport_winner`, `transport_loser`);
* the insertion phase (`insPhase`) inserts the partners in Jacobsthal order.

Correctness is carried by one invariant through the insertion phase
(`Invar` below, at batch `k`, position `p`, chain length `chainLen m M k p = m + jacLo k + p`):

`ChainSorted x σ c`  ∧  `W ⊆ chainSet σ c`  ∧  `∀ o, cntWin x W (σ ⟨c+o⟩) ≤ pendBound M k p o`.

The third conjunct is the whole content.  `cntWin x W q` counts the *winners* below the
position `q`; by `Setup.rankAt_le_cntWin`, the rank of the pending item in slot `q` is at
most `cntWin + (c - m)`, and `pendBound` is exactly `rank - 1` of the item sitting in slot
`c + o`: the items of the current batch come first, in *descending* rank (that is why the
item slot `m + jacHi - 1` is constant within the batch), followed by the items of the later
batches in ascending rank.  At the one position that matters — `o = cntB - 1 - p`, the slot
the batch takes its item from — the bound is

`cntWin ≤ jacHi - 1 - p`,  hence  `rankAt ≤ (jacHi - 1 - p) + (jacLo + p) = jacLo + jacHi - 1`,

which is *exactly* the window `winWindow` of `binIns`: no slack, as the count is tight.

The initial invariant (`k = p = 0`) is where the pairing pays: slot `m + o` holds the
partner of the `o`-th smallest winner, which is smaller than that winner, so at most `o`
winners lie below it (`cntWin_transport_le`).

**Fixed while proving this** (both defects were invisible to the depth bound, which only
counts comparisons):

* `Main.insBatch` used `m + jacLo + j` as the chain length while `j` counts the insertions
  still to come, i.e. it inserted the last item of a batch into the *shortest* chain
  (`chainLen` is now indexed by the position `p` in the batch);
* `Setup.pairAux` put the *smaller* element of each pair into the chain slot.  With the
  smaller element as the "winner", the inserted partner's rank is not bounded by its
  partner's chain position at all (`n = 4`, `x = (0,1,2,3)` inserts the value `2` at rank
  `0`), so `fjTree` was not a correct tree for any `n ≥ 4`.  The branch is flipped: the
  larger element goes into the chain, the smaller one is inserted, and the single pairing
  comparison is the rank bound.
-/
import SortBounds.Projects.FjTree.Main

namespace SortBounds.Projects.FjTree

open SortBounds
open SortBounds.Projects.FordJohnson (jacPred jacPred_le_jac jac_pos le_jac jacPred_succ)

variable {n : ℕ}

/-! ### The state the insertion phase starts from -/

/-- The transported state has the same winners in its chain as the pairing state: the
transport only permutes the winners among slots `0 … m-1` and moves their partners up. -/
theorem chainSet_transport {m : ℕ} (hm : 2 * m ≤ n) (ρ : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin m)) : chainSet (transport m hm ρ τ) m = chainSet ρ m := by
  ext p
  rw [mem_chainSet, mem_chainSet]
  constructor
  · rintro ⟨i, hi, hpi⟩
    refine ⟨⟨(τ ⟨i.val, hi⟩).val, by have := (τ ⟨i.val, hi⟩).isLt; omega⟩, by
      have := (τ ⟨i.val, hi⟩).isLt; omega, ?_⟩
    have h1 : transport m hm ρ τ ⟨i.val, by omega⟩
        = ρ ⟨(τ ⟨i.val, hi⟩).val, by have := (τ ⟨i.val, hi⟩).isLt; omega⟩ :=
      transport_winner m hm ρ τ hi
    rw [← hpi, h1]
  · rintro ⟨k, hk, hpk⟩
    obtain ⟨kk, hkk⟩ : ∃ kk : Fin m, kk.val = k.val := ⟨⟨k.val, hk⟩, rfl⟩
    refine ⟨⟨(τ.symm kk).val, by have := (τ.symm kk).isLt; omega⟩,
      by have := (τ.symm kk).isLt; omega, ?_⟩
    have h1 : transport m hm ρ τ ⟨(τ.symm kk).val, by have := (τ.symm kk).isLt; omega⟩
        = ρ ⟨(τ ⟨(τ.symm kk).val, by have := (τ.symm kk).isLt; omega⟩).val, by
          have := (τ ⟨(τ.symm kk).val, by have := (τ.symm kk).isLt; omega⟩).isLt; omega⟩ :=
      transport_winner m hm ρ τ (by have := (τ.symm kk).isLt; omega)
    have hτ : τ ⟨(τ.symm kk).val, by have := (τ.symm kk).isLt; omega⟩ = kk :=
      Equiv.apply_symm_apply τ kk
    have h2 : (⟨(τ ⟨(τ.symm kk).val, by have := (τ.symm kk).isLt; omega⟩).val, by
          have := (τ ⟨(τ.symm kk).val, by have := (τ.symm kk).isLt; omega⟩).isLt; omega⟩ : Fin n)
        = ⟨kk.val, by have := kk.isLt; omega⟩ := by
      refine Fin.ext ?_
      dsimp only
      exact congrArg Fin.val hτ
    rw [h1, h2]
    have hk' : (⟨kk.val, by have := kk.isLt; omega⟩ : Fin n) = k := by
      refine Fin.ext ?_
      dsimp only
      exact hkk
    rw [hk', hpk]

/-- **The partner is below the winner it is paired with**: in the transported state, slot
`m + o` holds an element smaller than the winner in slot `o`. -/
theorem transport_loser_lt {m : ℕ} (hm : 2 * m ≤ n) (ρ : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin m)) (x : Fin n → ℕ)
    (hpair : ∀ t : Fin m, x (ρ ⟨m + t.val, by have := t.isLt; omega⟩)
      < x (ρ ⟨t.val, by have := t.isLt; omega⟩)) {o : ℕ} (ho : o < m) :
    x (transport m hm ρ τ ⟨m + o, by omega⟩) < x (transport m hm ρ τ ⟨o, by omega⟩) := by
  have h1 : transport m hm ρ τ ⟨o, by omega⟩
      = ρ ⟨(τ ⟨o, ho⟩).val, by have := (τ ⟨o, ho⟩).isLt; omega⟩ :=
    transport_winner m hm ρ τ ho
  have hp : pendIdx m ho = (⟨o, ho⟩ : Fin m) := Fin.ext (pendIdx_val m ho)
  have hpe : (τ (pendIdx m ho)).val = (τ ⟨o, ho⟩).val := by rw [hp]
  have h2' : (⟨m + (τ (pendIdx m ho)).val, by have := (τ (pendIdx m ho)).isLt; omega⟩ : Fin n)
      = ⟨m + (τ ⟨o, ho⟩).val, by have := (τ ⟨o, ho⟩).isLt; omega⟩ := by
    refine Fin.ext ?_
    dsimp only
    exact congrArg (fun v => m + v) hpe
  have h2 : transport m hm ρ τ ⟨m + o, by omega⟩
      = ρ ⟨m + (τ ⟨o, ho⟩).val, by have := (τ ⟨o, ho⟩).isLt; omega⟩ := by
    rw [transport_loser m hm ρ τ ho, h2']
  rw [h1, h2]
  exact hpair ⟨(τ ⟨o, ho⟩).val, by have := (τ ⟨o, ho⟩).isLt; omega⟩

/-- **The pairing comparison bounds the rank of the partner**: in the transported state, at
most `o` winners lie below the element of slot `m + o`. -/
theorem cntWin_transport_le {m : ℕ} (hm : 2 * m ≤ n) (ρ : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin m)) (x : Fin n → ℕ)
    (hchain : ChainSorted x (transport m hm ρ τ) m)
    (hpair : ∀ t : Fin m, x (ρ ⟨m + t.val, by have := t.isLt; omega⟩)
      < x (ρ ⟨t.val, by have := t.isLt; omega⟩)) {o : ℕ} (ho : o < m) :
    cntWin x (chainSet (transport m hm ρ τ) m) (transport m hm ρ τ ⟨m + o, by omega⟩) ≤ o := by
  have hon : o < n := by omega
  have hmon : m + o < n := by omega
  have hpart : x (transport m hm ρ τ ⟨m + o, hmon⟩)
      < x (transport m hm ρ τ ⟨o, hon⟩) := transport_loser_lt hm ρ τ x hpair ho
  have hsub : (chainSet (transport m hm ρ τ) m).filter
        (fun p => x p < x (transport m hm ρ τ ⟨m + o, hmon⟩))
      ⊆ (Finset.univ.filter (fun b : Fin n => b.val < o)).image (transport m hm ρ τ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨i, hi, hpi⟩ := mem_chainSet.1 hp.1
    rw [Finset.mem_image]
    refine ⟨i, ?_, hpi⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hcon
    push Not at hcon
    have h3 : x (transport m hm ρ τ i) < x (transport m hm ρ τ ⟨m + o, hmon⟩) := by
      rw [hpi]; exact hp.2
    rcases lt_or_eq_of_le hcon with h' | h'
    · have h1 : x (transport m hm ρ τ ⟨o, hon⟩) < x (transport m hm ρ τ i) :=
        hchain ⟨o, hon⟩ i ho hi h'
      exact absurd (lt_trans (lt_trans h3 hpart) h1) (lt_irrefl _)
    · have h4 : transport m hm ρ τ i = transport m hm ρ τ ⟨o, hon⟩ := by
        rw [show i = (⟨o, hon⟩ : Fin n) from Fin.ext h'.symm]
      rw [h4] at h3
      exact absurd h3 (not_lt.2 (le_of_lt hpart))
  calc cntWin x (chainSet (transport m hm ρ τ) m) (transport m hm ρ τ ⟨m + o, by omega⟩)
      = ((chainSet (transport m hm ρ τ) m).filter
          (fun p => x p < x (transport m hm ρ τ ⟨m + o, hmon⟩))).card := rfl
    _ ≤ ((Finset.univ.filter (fun b : Fin n => b.val < o)).image
          (transport m hm ρ τ)).card := Finset.card_le_card hsub
    _ = (Finset.univ.filter (fun b : Fin n => b.val < o)).card :=
        Finset.card_image_of_injective _ (transport m hm ρ τ).injective
    _ = o := SortBounds.Projects.SortTree.card_filter_val_lt (by omega)

/-! ### The pending bound and the invariant of the insertion phase -/

/-- The number of winners that may lie below the item in slot `chainLen + o`, i.e. one less
than its rank: the items of batch `k` still inside the chain come first, in descending rank
(`o + p < cntB`), the items of the later batches follow in ascending rank. -/
def pendBound (M k p o : ℕ) : ℕ :=
  jacLo M k + (if o + p < cntB M k then o else p + o)

theorem pendBound_zero (M o : ℕ) : pendBound M 0 0 o = o := by
  have hj : jacLo M 0 = 0 := by simp [jacLo, jacPred]
  by_cases h : o + 0 < cntB M 0
  · rw [pendBound, hj, ite_eq_left h]; omega
  · rw [pendBound, hj, ite_eq_right h]; omega

/-- At the position the batch takes its item from (`o = cntB - 1 - p`) the bound is
`jacHi - 1 - p`, which is the window minus the `c - m` non-winners in the chain. -/
theorem pendBound_itemSlot (M k p : ℕ) (hp : p < cntB M k) :
    pendBound M k p (cntB M k - 1 - p) = jacHi M k - 1 - p := by
  have hc : cntB M k - 1 - p + p < cntB M k := by omega
  rw [pendBound, ite_eq_left hc]
  have h := jacLo_le_jacHi M k
  simp only [cntB] at *
  omega

/-- The bound at position `p + 1` for the item in slot `c + o` is the bound at position `p`
for the same item, as long as that item is still inside the batch. -/
theorem pendBound_shift_lo (M k p o : ℕ) (h : o + p + 1 < cntB M k) :
    pendBound M k (p + 1) o = pendBound M k p o := by
  have h1 : o + p < cntB M k := by omega
  have h' : o + (p + 1) < cntB M k := by omega
  rw [pendBound, pendBound, ite_eq_left h', ite_eq_left h1]

/-- The bound at position `p + 1` for the item in slot `c + o` is the bound at position `p`
for the item in slot `c + (o + 1)`: one insertion shifts it. -/
theorem pendBound_shift_hi (M k p o : ℕ) (h : ¬ o + p + 1 < cntB M k) :
    pendBound M k (p + 1) o = pendBound M k p (o + 1) := by
  have h1 : ¬ ((o + 1) + p < cntB M k) := by omega
  have h' : ¬ (o + (p + 1) < cntB M k) := by omega
  rw [pendBound, pendBound, ite_eq_right h', ite_eq_right h1]
  omega

/-- At the end of batch `k` the invariant is the invariant of the start of batch `k + 1`. -/
theorem pendBound_batch (M k o : ℕ) : pendBound M (k + 1) 0 o = pendBound M k (cntB M k) o := by
  have h2 : ¬ (o + cntB M k < cntB M k) := by omega
  have h4 : jacLo M k + (cntB M k + o) = jacHi M k + o := by
    have := jacLo_le_jacHi M k
    simp only [cntB] at *
    omega
  rw [pendBound, pendBound, ite_eq_right h2, h4]
  by_cases hc : o + 0 < cntB M (k + 1)
  · rw [ite_eq_left hc, jacLo_succ]
  · rw [ite_eq_right hc, jacLo_succ]
    omega

/-- The chain length of batch `k` at position `p`, plus the offset of the batch's item slot,
is the item slot itself. -/
theorem chainLen_add_eq_itemSlot (m M k p : ℕ) (hp : p < cntB M k) :
    chainLen m M k p + (cntB M k - 1 - p) = itemSlot m M k := by
  have h := jacLo_le_jacHi M k
  simp only [chainLen, itemSlot, cntB] at *
  omega

/-- **The invariant of the insertion phase**, at batch `k` and position `p`: the chain is
sorted, it holds all winners, and every pending item has at most `pendBound` winners below
it. -/
def Invar (x : Fin n → ℕ) (W : Finset (Fin n)) (m M k p : ℕ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ChainSorted x σ (chainLen m M k p) ∧
    W ⊆ chainSet σ (chainLen m M k p) ∧
    ∀ (o : ℕ) (ho : chainLen m M k p + o < n),
      cntWin x W (σ ⟨chainLen m M k p + o, ho⟩) ≤ pendBound M k p o

/-- **The rank of the batch's item is inside the window.**  This is where the invariant pays:
`rankAt ≤ cntWin + (c - m)` and both terms are bounded by the Jacobsthal schedule, so the
rank is at most `jacLo + jacHi - 1`, the window `binIns` searches. -/
theorem rankAt_le_winWindow {m M k p : ℕ} {x : Fin n → ℕ} {W : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} (hmM : m + M ≤ n) (hM1 : 1 ≤ M)
    (hW : W.card = m) (hp : p < cntB M k) (h : Invar x W m M k p σ) :
    rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, itemSlot_lt m M k hmM hM1⟩ ≤ winWindow M k := by
  have hlt : itemSlot m M k < n := itemSlot_lt m M k hmM hM1
  have hpj : p < jacHi M k := by
    have h := hp
    simp only [cntB] at h
    omega
  have hcl : chainLen m M k p ≤ n := by
    have := chainLen_le_itemSlot m M k p hp
    omega
  have hstep := rankAt_le_cntWin x σ W ⟨itemSlot m M k, hlt⟩ hcl hW h.2.1
  have hbound : cntWin x W (σ ⟨itemSlot m M k, hlt⟩) ≤ jacHi M k - 1 - p := by
    have hb := h.2.2 (cntB M k - 1 - p) (by
      rw [chainLen_add_eq_itemSlot m M k p hp]; exact hlt)
    have heq : (⟨chainLen m M k p + (cntB M k - 1 - p), by
          rw [chainLen_add_eq_itemSlot m M k p hp]; exact hlt⟩ : Fin n)
        = ⟨itemSlot m M k, hlt⟩ := Fin.ext (chainLen_add_eq_itemSlot m M k p hp)
    rw [heq, pendBound_itemSlot M k p hp] at hb
    exact hb
  have hcm : chainLen m M k p - m = jacLo M k + p := by
    simp only [chainLen]
    omega
  calc rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, hlt⟩
      ≤ cntWin x W (σ ⟨itemSlot m M k, hlt⟩) + (chainLen m M k p - m) := hstep
    _ = cntWin x W (σ ⟨itemSlot m M k, hlt⟩) + (jacLo M k + p) := by rw [hcm]
    _ ≤ (jacHi M k - 1 - p) + (jacLo M k + p) := Nat.add_le_add_right hbound _
    _ = winWindow M k := by
        have hjl := jacLo_le_jacHi M k
        have hp1 := jacHi_pos M k hM1
        simp only [winWindow]
        omega

/-- The rank of the batch's item is below its slot, so the insertion is well defined. -/
theorem rankAt_le_itemSlot {m M k p : ℕ} {x : Fin n → ℕ} {W : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M)
    (hW : W.card = m) (hp : p < cntB M k) (h : Invar x W m M k p σ) :
    rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, itemSlot_lt m M k hmM hM1⟩ ≤ itemSlot m M k := by
  have hcn : 0 < cntB M k := by omega
  exact le_trans (rankAt_le_winWindow hmM hM1 hW hp h) (winWindow_le_itemSlot m M k hM hcn)

/-- **One insertion keeps the invariant**: inserting the item in slot `q` at its rank
extends the chain by one, keeps all winners inside it, and shifts the pending items so that
each keeps a bound that is at most its old one. -/
theorem invar_step {m M k p : ℕ} {x : Fin n → ℕ} (hx : Function.Injective x)
    {W : Finset (Fin n)} (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M)
    (hW : W.card = m) (hp : p < cntB M k) {σ : Equiv.Perm (Fin n)}
    (h : Invar x W m M k p σ) {σ' : Equiv.Perm (Fin n)}
    (hσ' : σ' = insertAt (rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, itemSlot_lt m M k hmM hM1⟩) (itemSlot m M k)
      (rankAt_le_itemSlot hmM hM hM1 hW hp h) (itemSlot_lt m M k hmM hM1) σ) :
    Invar x W m M k (p + 1) σ' := by
  have hcn : 0 < cntB M k := by omega
  have hcq : chainLen m M k p ≤ itemSlot m M k := chainLen_le_itemSlot m M k p hp
  have hlt : itemSlot m M k < n := itemSlot_lt m M k hmM hM1
  have hrle : rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, hlt⟩ ≤ chainLen m M k p := by
    have h1 : rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, hlt⟩ ≤ winWindow M k :=
      rankAt_le_winWindow hmM hM1 hW hp h
    have h2 : winWindow M k ≤ chainLen m M k p := winWindow_le_chainLen m M k p hM hM1
    omega
  have hqj : itemSlot m M k = chainLen m M k p + (cntB M k - 1 - p) :=
    (chainLen_add_eq_itemSlot m M k p hp).symm
  have hlen : chainLen m M k (p + 1) = chainLen m M k p + 1 := by
    simp only [chainLen]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hσ', hlen]
    exact chainSorted_insertAt (c := chainLen m M k p) (q := ⟨itemSlot m M k, hlt⟩) hcq hx h.1
  · rw [hσ', hlen]
    exact Finset.Subset.trans h.2.1
      (chainSet_insertAt_subset (j := rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, hlt⟩)
        (c := chainLen m M k p) (q := itemSlot m M k)
        (rankAt_le_itemSlot hmM hM hM1 hW hp h) hlt hcq σ)
  · intro o ho
    have ho' : chainLen m M k p + 1 + o < n := by omega
    have hfin : (⟨chainLen m M k (p + 1) + o, ho⟩ : Fin n)
        = ⟨chainLen m M k p + 1 + o, ho'⟩ := Fin.ext (by dsimp only; omega)
    rw [hfin, hσ']
    rcases le_or_gt (chainLen m M k p + 1 + o) (itemSlot m M k) with hle | hgt
    · have hrank : rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, itemSlot_lt m M k hmM hM1⟩
          < chainLen m M k p + 1 + o := by omega
      have hpred : predFin (⟨chainLen m M k p + 1 + o, ho'⟩ : Fin n)
          = ⟨chainLen m M k p + o, by omega⟩ :=
        Fin.ext (by simp only [predFin_val]; omega)
      rw [insertAt_apply_mid (rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, itemSlot_lt m M k hmM hM1⟩) (itemSlot m M k)
        _ _ σ (k := ⟨chainLen m M k p + 1 + o, ho'⟩) hrank hle, hpred]
      have hcond : o + p + 1 < cntB M k := by omega
      rw [pendBound_shift_lo M k p o hcond]
      exact h.2.2 o (by omega)
    · have hval : (insertAt (rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, itemSlot_lt m M k hmM hM1⟩) (itemSlot m M k)
          (rankAt_le_itemSlot hmM hM hM1 hW hp h) (itemSlot_lt m M k hmM hM1) σ)
          ⟨chainLen m M k p + 1 + o, ho'⟩
          = σ ⟨chainLen m M k p + (o + 1), by omega⟩ := by
        rw [insertAt_apply_gt (rankAt x σ (chainLen m M k p) ⟨itemSlot m M k, itemSlot_lt m M k hmM hM1⟩) (itemSlot m M k)
          _ _ σ hgt]
        congr 1
        exact Fin.ext (by dsimp only; omega)
      rw [hval]
      have hcond : ¬ o + p + 1 < cntB M k := by omega
      rw [pendBound_shift_hi M k p o hcond]
      exact h.2.2 (o + 1) (by omega)

/-- A state satisfying the invariant at the end of batch `k` satisfies it at the start of
batch `k + 1`. -/
theorem invar_next_batch {m M k : ℕ} {x : Fin n → ℕ} {W : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} (h : Invar x W m M k (cntB M k) σ) :
    Invar x W m M (k + 1) 0 σ := by
  have hlen : chainLen m M k (cntB M k) = chainLen m M (k + 1) 0 := by
    have h1 := jacLo_le_jacHi M k
    simp only [chainLen, cntB, jacLo_succ, Nat.add_zero]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [← hlen]; exact h.1
  · rw [← hlen]; exact h.2.1
  · intro o ho
    have ho' : chainLen m M k (cntB M k) + o < n := by omega
    have hfin : (⟨chainLen m M (k + 1) 0 + o, ho⟩ : Fin n)
        = ⟨chainLen m M k (cntB M k) + o, ho'⟩ := Fin.ext (by dsimp only; omega)
    rw [hfin, pendBound_batch]
    exact h.2.2 o ho'

/-! ### The insertion phase sorts -/

/-- **One batch, step by step**: from a state satisfying the invariant at position `0`, the
`cntB` insertions of batch `k` end in a state satisfying the invariant at position `cntB`,
and running the batch with any continuation is the same as running it with the leaf
continuation and then the continuation — because each of its binary searches finds the rank
inside the window (`binIns_run`). -/
theorem insBatch_aux {m M k : ℕ} {x : Fin n → ℕ} (hx : Function.Injective x)
    (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M) {W : Finset (Fin n)}
    (hW : W.card = m) (next : Equiv.Perm (Fin n) → Tree n) :
    ∀ (j : ℕ) (hj : j ≤ cntB M k) (σ : Equiv.Perm (Fin n)),
      Invar x W m M k (cntB M k - j) σ →
      Invar x W m M k (cntB M k)
          (run (insBatch m M hmM hM hM1 (fun σ => Tree.leaf σ) k j hj σ) x) ∧
        run (insBatch m M hmM hM hM1 next k j hj σ) x
          = run (next (run (insBatch m M hmM hM hM1 (fun σ => Tree.leaf σ) k j hj σ) x)) x
  | 0, _, σ, h => by
    have h1 : cntB M k - 0 = cntB M k := Nat.sub_zero _
    rw [h1] at h
    exact ⟨h, rfl⟩
  | j + 1, hj, σ, h => by
    have hpos : cntB M k - (j + 1) = cntB M k - 1 - j := by omega
    rw [hpos] at h
    have hp : cntB M k - 1 - j < cntB M k := by omega
    have hwin := rankAt_le_winWindow hmM hM1 hW hp h
    have hrun_next := binIns_run (winWindow M k) 0 (winWindow M k)
      (chainLen m M k (cntB M k - 1 - j)) (itemSlot m M k)
      (itemSlot_lt m M k hmM hM1)
      (chainLen_le_itemSlot m M k (cntB M k - 1 - j) hp)
      (winWindow_le_chainLen m M k (cntB M k - 1 - j) hM hM1) (by omega) σ
      (insBatch m M hmM hM hM1 next k j (by omega)) x hx
      h.1 (Nat.zero_le _) hwin
    have hrun_leaf := binIns_run (winWindow M k) 0 (winWindow M k)
      (chainLen m M k (cntB M k - 1 - j)) (itemSlot m M k)
      (itemSlot_lt m M k hmM hM1)
      (chainLen_le_itemSlot m M k (cntB M k - 1 - j) hp)
      (winWindow_le_chainLen m M k (cntB M k - 1 - j) hM hM1) (by omega) σ
      (insBatch m M hmM hM hM1 (fun σ => Tree.leaf σ) k j (by omega)) x hx
      h.1 (Nat.zero_le _) hwin
    have hstep : Invar x W m M k (cntB M k - 1 - j + 1)
        (insertAt (rankAt x σ (chainLen m M k (cntB M k - 1 - j))
            ⟨itemSlot m M k, itemSlot_lt m M k hmM hM1⟩)
          (itemSlot m M k) (rankAt_le_itemSlot hmM hM hM1 hW hp h)
          (itemSlot_lt m M k hmM hM1) σ) :=
      invar_step hx hmM hM hM1 hW hp h rfl
    have he : cntB M k - j = cntB M k - 1 - j + 1 := by omega
    have hIH := insBatch_aux hx hmM hM hM1 hW next j (by omega : j ≤ cntB M k)
      (insertAt (rankAt x σ (chainLen m M k (cntB M k - 1 - j))
          ⟨itemSlot m M k, itemSlot_lt m M k hmM hM1⟩)
        (itemSlot m M k) (rankAt_le_itemSlot hmM hM hM1 hW hp h)
        (itemSlot_lt m M k hmM hM1) σ) (by rw [he]; exact hstep)
    refine ⟨?_, ?_⟩
    · rw [insBatch_succ, hrun_leaf]
      exact hIH.1
    · rw [insBatch_succ (next := next), hrun_next,
        insBatch_succ (next := fun σ => Tree.leaf σ), hrun_leaf, hIH.2]

/-- The insertion phase of one batch ends in the invariant of the next batch. -/
theorem insBatch_invar_start {m M k : ℕ} {x : Fin n → ℕ} (hx : Function.Injective x)
    (hmM : m + M ≤ n) (hM : M ≤ m + 1) (hM1 : 1 ≤ M) {W : Finset (Fin n)}
    (hW : W.card = m) {σ : Equiv.Perm (Fin n)} (h : Invar x W m M k 0 σ) :
    Invar x W m M (k + 1) 0
      (run (insBatch m M hmM hM hM1 (fun σ => Tree.leaf σ) k (cntB M k) le_rfl σ) x) := by
  have h0 : cntB M k - cntB M k = 0 := Nat.sub_self _
  have h' : Invar x W m M k (cntB M k - cntB M k) σ := by rw [h0]; exact h
  exact invar_next_batch (insBatch_aux hx hmM hM hM1 hW (fun σ => Tree.leaf σ)
    (cntB M k) le_rfl σ h').1

/-- **The insertion phase sorts**: the batches run until every item is in the chain, and a
sorted chain of length `n` is a sorting permutation. -/
theorem insBatches_sorts {m M : ℕ} (hmM : m + M ≤ n) (hMn : m + M = n) (hM : M ≤ m + 1)
    (hM1 : 1 ≤ M) (x : Fin n → ℕ) (hx : Function.Injective x) {W : Finset (Fin n)}
    (hW : W.card = m) :
    ∀ (fuel k : ℕ), k + fuel = M → ∀ σ : Equiv.Perm (Fin n),
      Invar x W m M k 0 σ →
      Sorts x (run (insBatches m M hmM hM hM1 (fun σ => Tree.leaf σ) fuel k σ) x)
  | 0, k, hk, σ, h => by
    have hkM : k = M := by omega
    simp only [insBatches]
    have hlen : chainLen m M k 0 = n := by
      have hj := jacLo_self M hM1
      rw [hkM]
      simp only [chainLen, Nat.add_zero]
      omega
    have hchain : ChainSorted x σ n := hlen ▸ h.1
    intro i j hij
    exact hchain i j i.isLt j.isLt hij
  | fuel + 1, k, hk, σ, h => by
    have h' : Invar x W m M k (cntB M k - cntB M k) σ := by
      rw [Nat.sub_self]; exact h
    have haux := insBatch_aux hx hmM hM hM1 hW
      (insBatches m M hmM hM hM1 (fun σ => Tree.leaf σ) fuel (k + 1)) (cntB M k) le_rfl σ h'
    have hrec := insBatches_sorts hmM hMn hM hM1 x hx hW fuel (k + 1) (by omega)
      (run (insBatch m M hmM hM hM1 (fun σ => Tree.leaf σ) k (cntB M k) le_rfl σ) x)
      (invar_next_batch haux.1)
    rw [show insBatches m M hmM hM hM1 (fun σ => Tree.leaf σ) (fuel + 1) k σ
          = insBatch m M hmM hM hM1 (insBatches m M hmM hM hM1 (fun σ => Tree.leaf σ) fuel (k + 1))
              k (cntB M k) le_rfl σ from rfl]
    rw [haux.2]
    exact hrec

/-- **The insertion phase sorts**, from the state the transport leaves behind: the winner
chain is sorted and each pending item has at most its own position many winners below it. -/
theorem insPhase_sorts {m M : ℕ} (hmM : m + M ≤ n) (hMn : m + M = n) (hM : M ≤ m + 1)
    (hM1 : 1 ≤ M) (x : Fin n → ℕ) (hx : Function.Injective x) {σ : Equiv.Perm (Fin n)}
    (hchain : ChainSorted x σ m)
    (hpend : ∀ (o : ℕ) (ho : m + o < n), cntWin x (chainSet σ m) (σ ⟨m + o, ho⟩) ≤ o) :
    Sorts x (run (insPhase m M hmM hM hM1 σ) x) := by
  have hlen0 : chainLen m M 0 0 = m := by
    have hj : jacLo M 0 = 0 := by simp [jacLo, jacPred]
    simp only [chainLen, Nat.add_zero, hj]
  have hinit : Invar x (chainSet σ m) m M 0 0 σ := by
    have h1 : ChainSorted x σ (chainLen m M 0 0) := by rw [hlen0]; exact hchain
    have h2 : chainSet σ m ⊆ chainSet σ (chainLen m M 0 0) := by rw [hlen0]
    refine ⟨h1, h2, ?_⟩
    intro o ho
    have ho' : m + o < n := by omega
    have hfin : (⟨chainLen m M 0 0 + o, ho⟩ : Fin n) = ⟨m + o, ho'⟩ :=
      Fin.ext (by dsimp only; omega)
    rw [hfin, pendBound_zero]
    exact hpend o ho'
  have hcard : (chainSet σ m).card = m := chainSet_card σ (by omega)
  have hres := insBatches_sorts hmM hMn hM hM1 x hx hcard M 0 (by omega) σ hinit
  simpa only [insPhase] using hres

/-! ### One level of the tree -/

/-- **The level sorts**: the stage replaces the state by the transported one, after which the
insertion phase sorts, and the winner chain it starts from is the recursive tree's output —
sorted by the induction hypothesis. -/
theorem fjStage_sorts {m M : ℕ} (hm : 2 * m ≤ n) (hmM : m + M ≤ n) (hMn : m + M = n)
    (hM : M ≤ m + 1) (hM1 : 1 ≤ M) (rec : Tree m) (hrec : Correct (α := ℕ) rec)
    (x : Fin n → ℕ) (hx : Function.Injective x) (ρ : Equiv.Perm (Fin n))
    (hpair : ∀ t : Fin m, x (ρ ⟨m + t.val, by have := t.isLt; omega⟩)
      < x (ρ ⟨t.val, by have := t.isLt; omega⟩)) :
    Sorts x (run (fjStage m M hm hmM hM hM1 rec ρ) x) := by
  have hinj : Function.Injective
      (fun i : Fin m => x (ρ ⟨i.val, by have := i.isLt; omega⟩)) := by
    intro i j hij
    have h1 : (⟨i.val, by have := i.isLt; omega⟩ : Fin n) = ⟨j.val, by have := j.isLt; omega⟩ :=
      ρ.injective (hx hij)
    exact Fin.ext (by simpa using congrArg Fin.val h1)
  have hwin := hrec (fun i : Fin m => x (ρ ⟨i.val, by have := i.isLt; omega⟩)) hinj
  have hchain : ChainSorted x
      (transport m hm ρ (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩)))) m := by
    intro i j hi hj hij
    have h1 : transport m hm ρ (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩)))
          ⟨i.val, by omega⟩
        = ρ ⟨(run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩))
            ⟨i.val, hi⟩).val, by
          have := (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩))
            ⟨i.val, hi⟩).isLt; omega⟩ :=
      transport_winner m hm ρ (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩))) hi
    have h2 : transport m hm ρ (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩)))
          ⟨j.val, by omega⟩
        = ρ ⟨(run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩))
            ⟨j.val, hj⟩).val, by
          have := (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩))
            ⟨j.val, hj⟩).isLt; omega⟩ :=
      transport_winner m hm ρ (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩))) hj
    rw [h1, h2]
    exact hwin (by simpa using hij)
  have hpend : ∀ (o : ℕ) (ho : m + o < n),
      cntWin x
        (chainSet (transport m hm ρ (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩)))) m)
        (transport m hm ρ (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩)))
          ⟨m + o, ho⟩) ≤ o := by
    intro o ho
    rcases lt_or_ge o m with hlt | hge
    · exact cntWin_transport_le hm ρ _ x hchain hpair hlt
    · have hcard : (chainSet (transport m hm ρ
          (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩)))) m).card = m :=
        chainSet_card _ (by omega)
      have hle : cntWin x
            (chainSet (transport m hm ρ
              (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩)))) m)
            (transport m hm ρ (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩)))
              ⟨m + o, ho⟩)
          ≤ (chainSet (transport m hm ρ
            (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩)))) m).card := by
        rw [cntWin]
        exact Finset.card_filter_le _ _
      omega
  have hrun : run (fjStage m M hm hmM hM hM1 rec ρ) x
      = run (insPhase m M hmM hM hM1
          (transport m hm ρ (run rec (fun i => x (ρ ⟨i.val, by have := i.isLt; omega⟩))))) x := by
    rw [fjStage, run_substTree, run_imageTree]
  rw [hrun]
  exact insPhase_sorts hmM hMn hM hM1 x hx hchain hpend

/-! ### The tree sorts -/

/-- A tree with a single leaf on at most one position is a correct tree. -/
theorem correct_leaf_one {k : ℕ} (hk : k ≤ 1) :
    Correct (α := ℕ) (Tree.leaf (1 : Equiv.Perm (Fin k))) := by
  intro x _ i j hij
  have := i.isLt
  have := j.isLt
  exact absurd hij (by omega)

/-- **Every level of the tree sorts**, by induction on the fuel. -/
theorem fjTreeFuel_correct : ∀ (fuel k : ℕ), k ≤ fuel → Correct (α := ℕ) (fjTreeFuel fuel k)
  | 0, k, hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [fjTreeFuel]
    exact correct_leaf_one (by omega)
  | fuel + 1, 0, _ => by
    simp only [fjTreeFuel]
    exact correct_leaf_one (by omega)
  | fuel + 1, 1, _ => by
    simp only [fjTreeFuel]
    exact correct_leaf_one (by omega)
  | fuel + 1, k + 2, hk => by
    have hmk : (k + 2) / 2 ≤ fuel := by omega
    have hrec := fjTreeFuel_correct fuel ((k + 2) / 2) hmk
    have hMn : (k + 2) / 2 + ((k + 2) - (k + 2) / 2) = k + 2 := by omega
    refine substTree_correct (P := fun ρ x => ∀ t : Fin ((k + 2) / 2),
      x (ρ ⟨(k + 2) / 2 + t.val, by have := t.isLt; omega⟩)
        < x (ρ ⟨t.val, by have := t.isLt; omega⟩)) ?_ ?_
    · intro x hx t
      exact (pairTree_spec (Nat.mul_div_le (k + 2) 2) x hx).2 t.val t.isLt
    · intro ρ x hx hpair
      exact fjStage_sorts (Nat.mul_div_le (k + 2) 2) (by omega) hMn (sub_div_le (k + 2))
        (one_le_sub_div (k + 2) (by omega)) (fjTreeFuel fuel ((k + 2) / 2)) hrec x hx ρ hpair

/-- **The tree of merge-insertion sorts `n` numbers.** -/
theorem fjTree_correct (n : ℕ) : Correct (α := ℕ) (fjTree n) :=
  fjTreeFuel_correct n n le_rfl

end SortBounds.Projects.FjTree
