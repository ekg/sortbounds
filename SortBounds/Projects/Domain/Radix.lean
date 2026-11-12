/-
SortBounds/Projects/Domain/Radix.lean

**`d` probes suffice: radix sort attains the bound.**

`Lower.lean` proved that a `p`-probe plan with `p < d` cannot sort the `b ^ d` keys of `Key d b`.
Here the matching upper bound is exhibited in the same model: the plan that reads digit `q` at step
`q` — no adaptivity needed — and digests the digits as the base-`b` integer they spell,

* `radixProc_sortsAllKeys` : `SortsAllKeys (radixProc d b)`, i.e. the digest refines the radix
  order on keys (`lowLt_digitsVal`: the base-`b` value embeds the lexicographic order, with
  `digitsVal_lt` supplying the range invariant) and separates distinct keys (`digitsVal_inj`:
  base-`b` expansions are unique, from Mathlib's `finFunctionFinEquiv`);
* `radix_sorts_Key` : `Instances.Radix.radixSort` — reused, not re-proved — sorts and permutes
  every list of keys;
* `radix_passes` : `d` passes of `n + b` elementary operations and `0` comparisons, which is the
  `Instances.Radix` cost model specialised to `Key d b`.

So `d = log_b (b ^ d)` digit reads per key are both necessary (`passes_lower`) and sufficient.
-/
import SortBounds.Projects.Domain.Lower

namespace SortBounds.Projects.Domain

open Finset

/-! ### The base-`b` value of a digit vector -/

/-- The integer that a digit vector spells in base `b`, digit `0` being the least significant. -/
def digitsVal {p b : ℕ} (v : Fin p → Fin b) : ℕ :=
  ∑ q : Fin p, (v q).val * b ^ (q : ℕ)

/-- Mathlib's `finFunctionFinEquiv` (`Fin p → Fin b ≃ Fin (b ^ p)`) computes exactly this base-`b`
value, which hands us injectivity and the range bound for free. -/
theorem digitsVal_eq_equiv {p b : ℕ} (v : Fin p → Fin b) :
    digitsVal v = (finFunctionFinEquiv v : ℕ) := by
  rw [digitsVal, finFunctionFinEquiv_apply]

/-- **Base-`b` expansions are unique**: distinct digit vectors spell distinct integers. -/
theorem digitsVal_inj {p b : ℕ} {v v' : Fin p → Fin b} (h : digitsVal v = digitsVal v') : v = v' := by
  refine finFunctionFinEquiv.injective (Fin.ext ?_)
  rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
  exact h

/-- A `p`-digit vector in base `b` spells an integer below `b ^ p`. -/
theorem digitsVal_lt {p b : ℕ} (v : Fin p → Fin b) : digitsVal v < b ^ p := by
  rw [digitsVal_eq_equiv]
  exact (finFunctionFinEquiv v).isLt

/-- The digit vector of `p + 1` digits, split as its `p` low digits and the new leading one. -/
theorem digitsVal_snoc {p b : ℕ} (v : Fin p → Fin b) (x : Fin b) :
    digitsVal (Fin.snoc v x) = x.val * b ^ p + digitsVal v := by
  rw [digitsVal, Fin.sum_univ_castSucc, digitsVal]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.val_castSucc]
  omega

/-- The first `p` digits of a key. -/
def restrict {d b : ℕ} (p : ℕ) (hp : p ≤ d) (k : Key d b) : Fin p → Fin b :=
  fun q => k (Fin.castLE hp q)

/-- Splitting off the last of the first `p + 1` digits. -/
theorem restrict_succ {d b : ℕ} (p : ℕ) (hp : p + 1 ≤ d) (k : Key d b) :
    restrict (p + 1) hp k
      = Fin.snoc (restrict p (Nat.le_of_succ_le hp) k) (k ⟨p, Nat.lt_of_succ_le hp⟩) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;>
    simp [restrict, Fin.castLE]

/-- **The base-`b` value embeds the radix order**: if the first `p` digits of `k` are lexicographically
below those of `k'` (digit `p - 1` most significant), then `k` spells a strictly smaller integer. -/
theorem lowLt_digitsVal {d b : ℕ} {k k' : Key d b} :
    ∀ (p : ℕ) (hp : p ≤ d), lowLt d b (fun k => k) p hp k k' →
      digitsVal (restrict p hp k) < digitsVal (restrict p hp k')
  | 0, _, h => h.elim
  | (p + 1), hp, h => by
      rw [lowLt_succ] at h
      have hsplit : ∀ k : Key d b,
          digitsVal (restrict (p + 1) hp k)
            = (k ⟨p, Nat.lt_of_succ_le hp⟩).val * b ^ p
              + digitsVal (restrict p (Nat.le_of_succ_le hp) k) := by
        intro k
        rw [restrict_succ p hp k, digitsVal_snoc]
      rw [hsplit, hsplit]
      rcases h with hlt | ⟨heq, hrec⟩
      · -- the differing digit already decides it
        have hstep : (k ⟨p, Nat.lt_of_succ_le hp⟩).val * b ^ p + b ^ p
            ≤ (k' ⟨p, Nat.lt_of_succ_le hp⟩).val * b ^ p := by
          rw [← Nat.succ_mul]
          exact Nat.mul_le_mul_right _ (by omega)
        have hlow := digitsVal_lt (restrict p (Nat.le_of_succ_le hp) k)
        omega
      · -- equal leading digit: induct on the rest
        rw [heq]
        have hlow := lowLt_digitsVal p (Nat.le_of_succ_le hp) hrec
        omega

/-! ### The radix plan -/

/-- **The radix plan**: at step `q` read digit `q` (no adaptivity), and digest the `d` digits read
as the base-`b` integer they spell. -/
def radixProc (d b : ℕ) : KeyProc d b d where
  next := fun q hq _ => ⟨q, hq⟩
  code := fun v => digitsVal v

/-- The radix plan reads digit `q` at step `q`, so its observation of a key is the key. -/
theorem obs_radixProc (d b : ℕ) (k : Key d b) : ∀ (q : ℕ) (hq : q < d),
    (radixProc d b).obs k q hq = k ⟨q, hq⟩ := by
  intro q hq
  rw [KeyProc.obs_eq]
  rfl

theorem valsAt_radixProc (d b : ℕ) (k : Key d b) : (radixProc d b).valsAt k = k :=
  funext fun q => obs_radixProc d b k q.val q.isLt

theorem codeOf_radixProc (d b : ℕ) (k : Key d b) : (radixProc d b).codeOf k = digitsVal k := by
  rw [KeyProc.codeOf, valsAt_radixProc]
  rfl

/-- **`d` probes suffice.**  The radix plan sorts every key of `Key d b` after exactly `d` digit
reads per key: its digest is the base-`b` value of the key, which separates all `b ^ d` keys
(`digitsVal_inj`) and orders them correctly (`lowLt_digitsVal`). -/
theorem radixProc_sortsAllKeys {d b : ℕ} : SortsAllKeys (radixProc d b) := by
  refine ⟨?_, ?_⟩
  · intro k k' hle
    rw [codeOf_radixProc, codeOf_radixProc] at hle
    intro hlt
    exact absurd (lowLt_digitsVal d le_rfl hlt) (not_lt.mpr hle)
  · intro k k' he
    rw [codeOf_radixProc, codeOf_radixProc] at he
    exact digitsVal_inj he

/-- **The counting hypothesis is attainable, and attained exactly.**  The radix plan's observation
of a key *is* the key (`valsAt_radixProc`), so equal observations off it are equal keys — the fibre
hypothesis of `card_le_pow_probes` holds for the whole key domain with `p = d` — and the `b ^ d`
observations carry `b ^ d` keys.  So `card_le_pow_probes` is not a vacuous hypothesis: it is exactly
tight at `p = d`. -/
theorem card_le_pow_probes_attained (d b : ℕ) :
    (∀ k₁ ∈ (univ : Finset (Key d b)), ∀ k₂ ∈ univ,
        (∀ q, ((radixProc d b).trace k₁ q).2 = ((radixProc d b).trace k₂ q).2) → k₁ = k₂) ∧
      (univ : Finset (Key d b)).card = b ^ d := by
  have htrace : ∀ k : Key d b, ∀ q, ((radixProc d b).trace k q).2 = k q :=
    fun k q => congrFun (valsAt_radixProc d b k) q
  refine ⟨fun k₁ _ k₂ _ h => ?_, by rw [Finset.card_univ, card_Key]⟩
  funext q
  exact (htrace k₁ q).symm.trans ((h q).trans (htrace k₂ q))

/-- **The bound `log_b U` is tight.**  `d` digit reads per key are necessary (`probes_lower`) and
`d` suffice (`radixProc`), so for `U = b ^ d` the two sides meet exactly at `log_b U = d`
(`logb_card_Key`); no ceiling appears because `U` is an exact power of `b`. -/
theorem probes_tight (d b : ℕ) (hb : 2 ≤ b) :
    (∀ (p : ℕ) (P : KeyProc d b p), SortsAllKeys P → d ≤ p) ∧
      (∃ P : KeyProc d b d, SortsAllKeys P) :=
  ⟨fun _ _ h => probes_lower hb h, radixProc d b, radixProc_sortsAllKeys⟩

/-! ### Radix sort on keys, reused from `Instances.Radix` -/

/-- **Radix sort sorts and permutes every list of keys.**  (`Instances.Radix.radixSort_sorted` and
`radixSort_perm`, specialised to `α := Key d b` and `keys := id`.) -/
theorem radix_sorts_Key (d b : ℕ) (l : List (Key d b)) :
    (radixSort d b (fun k => k) l).Perm l ∧
      (radixSort d b (fun k => k) l).Pairwise (KeyLe d b) :=
  ⟨radixSort_perm d b (fun k => k) l, radixSort_sorted d b (fun k => k) l⟩

/-- Radix sort is complete on keys: with pairwise distinct input keys the output is strictly
increasing for the radix order. -/
theorem radix_sorts_Key_strict (d b : ℕ) {l : List (Key d b)} (hnd : l.Nodup) :
    (radixSort d b (fun k => k) l).Pairwise (KeyLt d b) :=
  pairwise_keyLt_of_pairwise_keyLe
    ((List.Perm.nodup_iff ((radixSort_perm d b (fun k => k) l).map (fun k => k))).mpr
      (by simpa using hnd))
    (radixSort_sorted d b (fun k => k) l)

/-- **The cost of sorting `n` keys**: `d` passes of `n + b` elementary operations — `d` digit
reads per key, no comparisons — i.e. `d = log_b U` passes for a domain of `U = b ^ d` keys. -/
theorem radix_passes (d n b : ℕ) :
    ((List.range d).map (fun _ => passCost n b)).length = d ∧
      radixCost d n b = d * (n + b) ∧ radixComparisons d n b = 0 :=
  ⟨by simp, rfl, rfl⟩

/-! ### Sanity checks -/

/-- `Key 2 10` is the `100` two-digit decimal keys. -/
example : Fintype.card (Key 2 10) = 100 := by norm_num [card_Key]

/-- Base-`10` digests with digit `0` least significant: `[3, 1]` is `3·10^0 + 1·10^1 = 13`. -/
example : digitsVal (fun i : Fin 2 => if i.val = 0 then (3 : Fin 10) else 1) = 13 := by
  rw [digitsVal, Fin.sum_univ_two]
  norm_num

/-- The `d`-digit base-`b` digest of a key is below `b ^ d`. -/
example (k : Key 3 5) : digitsVal k < 125 := by
  have := digitsVal_lt k
  norm_num at this ⊢
  exact this

/-- Radix sort on the four keys of `Key 2 2`, with `![a, b]` the key whose digit `0` is `a` and
whose digit `1` is `b`: digit `1` is the more significant one, so `![0, 1]` (value `2`) comes after
`![1, 0]` (value `1`). -/
example : radixSort 2 2 (fun k => k) ([![1, 1], ![0, 1], ![1, 0], ![0, 0]] : List (Key 2 2))
    = [![0, 0], ![1, 0], ![0, 1], ![1, 1]] := by
  decide

/-- The sort order of the example above is the numeric order of the base-`2` digests. -/
example : digitsVal (![1, 0] : Key 2 2) < digitsVal (![0, 1] : Key 2 2) := by
  decide

end SortBounds.Projects.Domain
