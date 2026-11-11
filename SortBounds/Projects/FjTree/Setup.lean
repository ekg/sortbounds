/-
SortBounds/Projects/FjTree/Setup.lean

**The two stages before the losers are inserted**: pairing, and transporting the losers
along the recursive sort of the winners.

* `chainSet σ s` — the set of positions sitting in the sorted chain (the first `s` slots);
  `cntWin x W q` — how many *winners* are below the position `q`.  These two reduce the
  question "how big is the search window of a loser?" to counting: the chain contains at
  most `s - m` non-winners, so `rankAt ≤ cntWin + (s - m)` (`rankAt_le_cntWin`).
* `pairTree` — compare the `n/2` pairs `{k, m+k}`; the state it leaves has the *larger*
  element of pair `k` in slot `k` and its smaller partner in slot `m+k` (`pairTree_spec`).
  The larger element is the one that goes on to be sorted (the "winner" of the
  merge-insertion literature); the smaller one is inserted into that sorted chain later,
  and the single pairing comparison is exactly the bound on its rank.  Pairing `k` with
  `m+k` (rather than `2k` with `2k+1`) keeps the target layout contiguous, so the pairing
  perm is a product of disjoint slot swaps and no de-interleaving permutation is needed.
* `transport` — after the recursive call has sorted the winners, put the sorted winners in
  slots `0 … m-1` and their losers in slots `m … n-1` (`transport_winner`,
  `transport_loser`, `transport_last`).  This is the layout the insertion phase starts
  from: the pending item in slot `m+o` is the loser paired with the `o`-th smallest
  winner.
-/
import SortBounds.Projects.FjTree.Basic
import SortBounds.Projects.FordJohnson.Jacobsthal

namespace SortBounds.Projects.FjTree

open SortBounds

variable {n : ℕ}

/-! ### The chain as a set of positions -/

/-- The set of positions occupying the chain slots `0 … s-1`. -/
noncomputable def chainSet (σ : Equiv.Perm (Fin n)) (s : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin n => i.val < s)).image σ

theorem mem_chainSet {σ : Equiv.Perm (Fin n)} {s : ℕ} {p : Fin n} :
    p ∈ chainSet σ s ↔ ∃ i : Fin n, i.val < s ∧ σ i = p := by
  simp only [chainSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem chainSet_card (σ : Equiv.Perm (Fin n)) {s : ℕ} (hs : s ≤ n) :
    (chainSet σ s).card = s := by
  rw [chainSet, Finset.card_image_of_injective _ σ.injective,
    SortBounds.Projects.SortTree.card_filter_val_lt (n := n) (m := s) hs]

/-- The chain of slots `0 … s-1` grows when a further element is inserted. -/
theorem chainSet_insertAt_subset (j c q : ℕ) (hjq : j ≤ q) (hqn : q < n) (hcq : c ≤ q)
    (σ : Equiv.Perm (Fin n)) :
    chainSet σ c ⊆ chainSet (insertAt j q hjq hqn σ) (c + 1) := by
  intro p hp
  rw [mem_chainSet] at hp ⊢
  obtain ⟨i, hi, rfl⟩ := hp
  rcases lt_or_ge i.val j with h' | h'
  · exact ⟨i, by omega, insertAt_apply_lt j q hjq hqn σ h'⟩
  · refine ⟨⟨i.val + 1, by omega⟩, by simp only [Fin.val_mk]; omega, ?_⟩
    rw [insertAt_apply_mid j q hjq hqn σ (k := ⟨i.val + 1, by omega⟩)
      (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
    rfl

theorem fin_ext_eq {a b : ℕ} (ha : a < n) (hb : b < n) (h : a = b) :
    (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ := Fin.ext h

/-- The number of winners below the position `q`. -/
noncomputable def cntWin (x : Fin n → ℕ) (W : Finset (Fin n)) (q : Fin n) : ℕ :=
  (W.filter (fun w => x w < x q)).card

theorem rankAt_eq_card (x : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (c : ℕ) (q : Fin n) :
    rankAt x σ c q = ((chainSet σ c).filter (fun p => x p < x (σ q))).card := by
  have h1 : rankSet x σ c q =
      (Finset.univ.filter (fun i : Fin n => i.val < c)).filter
        (fun i => x (σ i) < x (σ q)) := by
    rw [rankSet, Finset.filter_filter]
  have h2 : ((Finset.univ.filter (fun i : Fin n => i.val < c)).filter
        (fun i => x (σ i) < x (σ q))).image σ
      = (chainSet σ c).filter (fun p => x p < x (σ q)) := by
    rw [chainSet, Finset.filter_image]
  rw [rankAt, h1, ← h2, Finset.card_image_of_injective _ σ.injective]

/-- **How wide the search window of a loser has to be**: the chain contains all `m`
winners and at most `s - m` non-winners, so the number of chain elements below an element
is at most the number of winners below it plus `s - m`. -/
theorem rankAt_le_cntWin (x : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (W : Finset (Fin n))
    {c m : ℕ} (q : Fin n) (hcn : c ≤ n) (hWcard : W.card = m) (hWs : W ⊆ chainSet σ c) :
    rankAt x σ c q ≤ cntWin x W (σ q) + (c - m) := by
  have hsub : (chainSet σ c).filter (fun p => x p < x (σ q))
      ⊆ (W.filter (fun w => x w < x (σ q)))
        ∪ ((chainSet σ c \ W).filter (fun p => x p < x (σ q))) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hW : p ∈ W
    · exact Or.inl ⟨hW, hp.2⟩
    · exact Or.inr ⟨Finset.mem_sdiff.2 ⟨hp.1, hW⟩, hp.2⟩
  have hcard : (chainSet σ c \ W).card = c - m := by
    rw [Finset.card_sdiff, (Finset.inter_eq_left).2 hWs, chainSet_card σ hcn, hWcard]
  have h1 : ((chainSet σ c \ W).filter (fun p => x p < x (σ q))).card ≤ c - m := by
    rw [← hcard]
    exact Finset.card_filter_le _ _
  calc rankAt x σ c q
      = ((chainSet σ c).filter (fun p => x p < x (σ q))).card := rankAt_eq_card x σ c q
    _ ≤ ((W.filter (fun w => x w < x (σ q)))
          ∪ ((chainSet σ c \ W).filter (fun p => x p < x (σ q)))).card :=
        Finset.card_le_card hsub
    _ ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ cntWin x W (σ q) + (c - m) := Nat.add_le_add le_rfl h1

/-! ### The pairing stage

Pair `k` with `m + k` (`k < m = n/2`); the unpaired element of an odd-length input stays
in slot `2m = n-1`.  The state left behind lists the winner of pair `k` in slot `k` and
the loser in slot `m+k`, so the winners already occupy a contiguous prefix. -/

/-- The pairing stage: compare the two slots of pair `k` and, if the first is smaller, swap
them, so that slot `k` ends up holding the **larger** element of the pair and slot `m+k` the
smaller one.  The larger elements go on to be sorted (they are the candidate "winners" of
the merge-insertion literature, the ones whose order is settled first); the smaller ones
are inserted into that sorted chain, where the pairing comparison is exactly the bound on
their rank. -/
noncomputable def pairAux (m : ℕ) (hm : 2 * m ≤ n) :
    (k : ℕ) → k ≤ m → Equiv.Perm (Fin n) → Tree n
  | 0, _, σ => Tree.leaf σ
  | k + 1, hk, σ =>
    Tree.node (σ ⟨k, by omega⟩) (σ ⟨m + k, by omega⟩)
      (pairAux m hm k (by omega) (σ * Equiv.swap ⟨k, by omega⟩ ⟨m + k, by omega⟩))
      (pairAux m hm k (by omega) σ)

/-- **The pairing tree** for `n` positions. -/
noncomputable def pairTree (n : ℕ) : Tree n :=
  pairAux (n / 2) (Nat.mul_div_le n 2) (n / 2) le_rfl 1

/-- The slots outside the pairs below `k` are untouched by `pairAux`. -/
theorem pairAux_agree (m : ℕ) (hm : 2 * m ≤ n) :
    ∀ (k : ℕ) (hk : k ≤ m) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℕ) (i : Fin n),
      (k ≤ i.val ∧ i.val < m) ∨ m + k ≤ i.val → run (pairAux m hm k hk σ) x i = σ i
  | 0, _, σ, x, i, _ => rfl
  | k + 1, hk, σ, x, i, hi => by
    have hlt : k < m := by omega
    have hik : k ≤ i.val := by rcases hi with ⟨a, -⟩ | a <;> omega
    simp only [pairAux, run]
    by_cases h : x (σ ⟨k, by omega⟩) < x (σ ⟨m + k, by omega⟩)
    · rw [ite_eq_left h]
      have hstep := pairAux_agree m hm k (by omega)
        (σ * Equiv.swap ⟨k, by omega⟩ ⟨m + k, by omega⟩) x i (by
          rcases hi with ⟨a, b⟩ | a
          · exact Or.inl ⟨by omega, b⟩
          · exact Or.inr (by omega))
      rw [hstep]
      show σ ((Equiv.swap ⟨k, by omega⟩ ⟨m + k, by omega⟩) i) = σ i
      rw [Equiv.swap_apply_of_ne_of_ne
        (by intro hc; have h2 := congrArg Fin.val hc; simp only [Fin.val_mk] at h2; omega)
        (by intro hc; have h2 := congrArg Fin.val hc; simp only [Fin.val_mk] at h2; omega)]
    · rw [ite_eq_right h]
      exact pairAux_agree m hm k (by omega) σ x i (by
        rcases hi with ⟨a, b⟩ | a
        · exact Or.inl ⟨by omega, b⟩
        · exact Or.inr (by omega))

/-- **The pairing tree decides every pair below `k`**: the *smaller* element of pair `t`
sits in slot `m + t` and the larger one in slot `t`, whatever state the tree starts from. -/
theorem pairAux_decided (m : ℕ) (hm : 2 * m ≤ n) :
    ∀ (k : ℕ) (hk : k ≤ m) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℕ)
      (hx : Function.Injective x) (i j : Fin n)
      (hex : ∃ t, t < k ∧ i.val = t ∧ j.val = m + t),
      x (run (pairAux m hm k hk σ) x j) < x (run (pairAux m hm k hk σ) x i)
  | 0, _, σ, x, hx, i, j, hex => by
    obtain ⟨t, ht, -, -⟩ := hex
    omega
  | k + 1, hk, σ, x, hx, i, j, hex => by
    obtain ⟨t, ht, hi, hj⟩ := hex
    have hlt : k < m := by omega
    have hkn : k < n := by omega
    have hmkn : m + k < n := by omega
    simp only [pairAux, run]
    by_cases h : x (σ ⟨k, hkn⟩) < x (σ ⟨m + k, hmkn⟩)
    · rw [ite_eq_left h]
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h' | h'
      · exact pairAux_decided m hm k (by omega) _ x hx i j ⟨t, h', hi, hj⟩
      · have hiv : (i : ℕ) = k := by omega
        have hjv : (j : ℕ) = m + k := by omega
        clear hi hj ht h'
        have hik : i = ⟨k, by omega⟩ := fin_ext_eq i.isLt (by omega) hiv
        have hjk : j = ⟨m + k, by omega⟩ := fin_ext_eq j.isLt (by omega) hjv
        rw [hik, hjk,
          pairAux_agree m hm k (by omega) _ x ⟨k, by omega⟩ (Or.inl ⟨le_rfl, hlt⟩),
          pairAux_agree m hm k (by omega) _ x ⟨m + k, by omega⟩ (Or.inr le_rfl)]
        show x ((σ * Equiv.swap (⟨k, by omega⟩ : Fin n) ⟨m + k, by omega⟩)
            (⟨m + k, by omega⟩ : Fin n))
          < x ((σ * Equiv.swap (⟨k, by omega⟩ : Fin n) ⟨m + k, by omega⟩)
            (⟨k, by omega⟩ : Fin n))
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
          Equiv.swap_apply_left]
        exact h
    · rw [ite_eq_right h]
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h' | h'
      · exact pairAux_decided m hm k (by omega) σ x hx i j ⟨t, h', hi, hj⟩
      · have hiv : (i : ℕ) = k := by omega
        have hjv : (j : ℕ) = m + k := by omega
        clear hi hj ht h'
        have hik : i = ⟨k, by omega⟩ := fin_ext_eq i.isLt (by omega) hiv
        have hjk : j = ⟨m + k, by omega⟩ := fin_ext_eq j.isLt (by omega) hjv
        rw [hik, hjk,
          pairAux_agree m hm k (by omega) σ x ⟨k, by omega⟩ (Or.inl ⟨le_rfl, hlt⟩),
          pairAux_agree m hm k (by omega) σ x ⟨m + k, by omega⟩ (Or.inr le_rfl)]
        refine lt_of_le_of_ne (not_lt.1 h) (fun hc => ?_)
        have h2 : (⟨m + k, hmkn⟩ : Fin n) = (⟨k, hkn⟩ : Fin n) := σ.injective (hx hc)
        have h3 : m + k = k := by simpa using congrArg Fin.val h2
        omega

/-- **The depth of the pairing stage** is one comparison per pair. -/
theorem pairAux_depth (m : ℕ) (hm : 2 * m ≤ n) :
    ∀ (k : ℕ) (hk : k ≤ m) (σ : Equiv.Perm (Fin n)), depth (pairAux m hm k hk σ) = k
  | 0, _, σ => rfl
  | k + 1, hk, σ => by
    simp only [pairAux, depth, pairAux_depth]
    omega

/-- **Correctness of the pairing stage**: it decides every pair, so the larger element of
pair `t` sits in slot `t` and the smaller one in slot `m+t`. -/
theorem pairTree_spec {m : ℕ} (hm : 2 * m ≤ n) (x : Fin n → ℕ) (hx : Function.Injective x) :
    depth (pairAux m hm m le_rfl (1 : Equiv.Perm (Fin n))) = m ∧
      ∀ (t : ℕ) (ht : t < m),
        x (run (pairAux m hm m le_rfl 1) x ⟨m + t, by omega⟩)
          < x (run (pairAux m hm m le_rfl 1) x ⟨t, by omega⟩) :=
  ⟨pairAux_depth m hm m le_rfl 1, fun t ht =>
    pairAux_decided m hm m le_rfl 1 x hx ⟨t, by omega⟩ ⟨m + t, by omega⟩
      ⟨t, ht, rfl, rfl⟩⟩

/-! ### Transporting the losers along the sorted winners

After the recursive call has sorted the winners, slot `k` of its state holds the pair index
of the `k`-th smallest winner.  The transport moves the winners into slots `0 … m-1` in
sorted order, their losers into slots `m … 2m-1`, and leaves the unpaired element of an
odd-length input in the last slot. -/

/-- The slot map of the transport: the winners are permuted by `τ`, the loser of the
`k`-th smallest winner moves to slot `m+k`. -/
def transportFun (m : ℕ) (hm : 2 * m ≤ n) (τ : Equiv.Perm (Fin m)) (k : Fin n) : Fin n :=
  if h : k.val < m then ⟨(τ ⟨k.val, h⟩).val, by have := (τ ⟨k.val, h⟩).isLt; omega⟩
  else if h' : k.val < 2 * m then
    ⟨m + (τ ⟨k.val - m, by omega⟩).val, by have := (τ ⟨k.val - m, by omega⟩).isLt; omega⟩
  else k

theorem transportFun_val_lt (m : ℕ) (hm : 2 * m ≤ n) (τ : Equiv.Perm (Fin m)) {k : Fin n}
    (h : k.val < m) :
    (transportFun (n := n) m hm τ k).val = (τ ⟨k.val, h⟩).val := by
  simp only [transportFun, dif_pos h, Fin.val_mk]

theorem transportFun_val_mid (m : ℕ) (hm : 2 * m ≤ n) (τ : Equiv.Perm (Fin m)) {k : Fin n}
    (h : ¬ k.val < m) (h' : k.val < 2 * m) :
    (transportFun (n := n) m hm τ k).val = m + (τ ⟨k.val - m, by omega⟩).val := by
  simp only [transportFun, dif_neg h, dif_pos h', Fin.val_mk]

theorem transportFun_val_hi (m : ℕ) (hm : 2 * m ≤ n) (τ : Equiv.Perm (Fin m)) {k : Fin n}
    (h : ¬ k.val < m) (h' : ¬ k.val < 2 * m) :
    (transportFun (n := n) m hm τ k).val = k.val := by
  simp only [transportFun, dif_neg h, dif_neg h', Fin.val_mk]

theorem transportFun_injective (m : ℕ) (hm : 2 * m ≤ n) (τ : Equiv.Perm (Fin m)) :
    Function.Injective (transportFun (n := n) m hm τ) := by
  intro a b hab
  have hval := congrArg Fin.val hab
  by_cases h1 : a.val < m
  · by_cases h2 : b.val < m
    · rw [transportFun_val_lt m hm τ h1, transportFun_val_lt m hm τ h2] at hval
      have hτ : (⟨a.val, h1⟩ : Fin m) = ⟨b.val, h2⟩ := τ.injective (Fin.ext hval)
      exact Fin.ext (by have := congrArg Fin.val hτ; simpa using this)
    · have ha := (τ ⟨a.val, h1⟩).isLt
      rw [transportFun_val_lt m hm τ h1] at hval
      by_cases h3 : b.val < 2 * m
      · rw [transportFun_val_mid m hm τ h2 h3] at hval; omega
      · rw [transportFun_val_hi m hm τ h2 h3] at hval; omega
  · by_cases h2 : b.val < m
    · have hb := (τ ⟨b.val, h2⟩).isLt
      rw [transportFun_val_lt m hm τ h2] at hval
      by_cases h3 : a.val < 2 * m
      · rw [transportFun_val_mid m hm τ h1 h3] at hval; omega
      · rw [transportFun_val_hi m hm τ h1 h3] at hval; omega
    · by_cases h3 : a.val < 2 * m
      · by_cases h4 : b.val < 2 * m
        · have ha := (τ ⟨a.val - m, by omega⟩).isLt
          rw [transportFun_val_mid m hm τ h1 h3, transportFun_val_mid m hm τ h2 h4] at hval
          have hτ : (⟨a.val - m, by omega⟩ : Fin m) = ⟨b.val - m, by omega⟩ :=
            τ.injective (Fin.ext (by omega))
          exact Fin.ext (by
            have h2 := congrArg Fin.val hτ
            simp only [Fin.val_mk] at h2
            omega)
        · rw [transportFun_val_mid m hm τ h1 h3, transportFun_val_hi m hm τ h2 h4] at hval
          have := (τ ⟨a.val - m, by omega⟩).isLt; omega
      · by_cases h4 : b.val < 2 * m
        · rw [transportFun_val_hi m hm τ h1 h3, transportFun_val_mid m hm τ h2 h4] at hval
          have := (τ ⟨b.val - m, by omega⟩).isLt; omega
        · rw [transportFun_val_hi m hm τ h1 h3, transportFun_val_hi m hm τ h2 h4] at hval
          exact Fin.ext hval

theorem transportFun_lt (m : ℕ) (hm : 2 * m ≤ n) (τ : Equiv.Perm (Fin m)) {k : Fin n}
    (h : k.val < m) :
    transportFun m hm τ k = ⟨(τ ⟨k.val, h⟩).val, by have := (τ ⟨k.val, h⟩).isLt; omega⟩ :=
  Fin.ext (transportFun_val_lt m hm τ h)

theorem transportFun_mid (m : ℕ) (hm : 2 * m ≤ n) (τ : Equiv.Perm (Fin m)) {k : Fin n}
    (h : ¬ k.val < m) (h' : k.val < 2 * m) :
    transportFun m hm τ k
      = ⟨m + (τ ⟨k.val - m, by omega⟩).val, by have := (τ ⟨k.val - m, by omega⟩).isLt; omega⟩ :=
  Fin.ext (transportFun_val_mid m hm τ h h')

theorem transportFun_hi (m : ℕ) (hm : 2 * m ≤ n) (τ : Equiv.Perm (Fin m)) {k : Fin n}
    (h : ¬ k.val < m) (h' : ¬ k.val < 2 * m) : transportFun m hm τ k = k :=
  Fin.ext (transportFun_val_hi m hm τ h h')

/-- The slot map of the transport, as a permutation of the `n` slots. -/
noncomputable def transportPerm (m : ℕ) (hm : 2 * m ≤ n) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective (transportFun m hm τ)
    ⟨transportFun_injective m hm τ, Finite.surjective_of_injective (transportFun_injective m hm τ)⟩

/-- **The state after the winners are sorted**: the winners in sorted order, then their
losers. -/
noncomputable def transport (m : ℕ) (hm : 2 * m ≤ n) (ρ : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin n) :=
  ρ * transportPerm m hm τ

theorem transport_apply (m : ℕ) (hm : 2 * m ≤ n) (ρ : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin m)) (k : Fin n) :
    transport m hm ρ τ k = ρ (transportFun m hm τ k) := rfl

theorem transport_winner (m : ℕ) (hm : 2 * m ≤ n) (ρ : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin m)) {o : ℕ} (ho : o < m) :
    transport m hm ρ τ ⟨o, by omega⟩ = ρ ⟨(τ ⟨o, ho⟩).val, by have := (τ ⟨o, ho⟩).isLt; omega⟩ := by
  rw [transport_apply, transportFun_lt m hm τ (by simpa using ho)]

def pendIdx (m : ℕ) {o : ℕ} (ho : o < m) : Fin m := ⟨m + o - m, by omega⟩

theorem pendIdx_val (m : ℕ) {o : ℕ} (ho : o < m) : (pendIdx m ho).val = o := by
  simp only [pendIdx, Fin.val_mk, Nat.add_sub_cancel_left]

theorem transport_loser (m : ℕ) (hm : 2 * m ≤ n) (ρ : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin m)) {o : ℕ} (ho : o < m) :
    transport m hm ρ τ ⟨m + o, by omega⟩
      = ρ ⟨m + (τ (pendIdx m ho)).val, by have := (τ (pendIdx m ho)).isLt; omega⟩ := by
  rw [transport_apply, transportFun_mid m hm τ (by simp only [Fin.val_mk]; omega)
    (by simp only [Fin.val_mk]; omega)]
  congr 2

/-- The unpaired element of an odd-length input keeps its slot. -/
theorem transport_last (m : ℕ) (hm : 2 * m ≤ n) (hodd : 2 * m < n)
    (ρ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) :
    transport m hm ρ τ ⟨2 * m, hodd⟩ = ρ ⟨2 * m, hodd⟩ := by
  rw [transport_apply,
    transportFun_hi m hm τ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]

end SortBounds.Projects.FjTree
