/-
SortBounds/Projects/Domain/Lower.lean

**`log_b U` probes are necessary.**

`Model.lean` set up the probe plan (`KeyProc`) and the counting engine (`card_le_pow_probes`).  Here
the plans are asked to *sort*, and the counting engine is applied:

* `SortsAllKeys P` — the model of "`P` sorts every list of keyed items": the digest `P.codeOf` must
  refine the radix order on keys (so that sorting by digest sorts by key) and must separate
  distinct keys (so that no tie between different keys is left to the input order, which the probe
  plan cannot see).  The derivation of the second clause from "sorts every list" is spelled out
  in the definition's comment;
* `passes_lower` — with `2 ≤ b` and `p < d`, no `p`-probe plan sorts all `b ^ d` keys;
* `probes_lower`, `probes_lower_logb` — the same, in the units of the contract: `log_b U = d`
  probes per key are necessary;
* `exists_obs_eq_of_lt` — the operational reason: a run of `p < d` probes reads at most `p` of the
  `d` digit positions, so there is a digit it never looks at, and changing that digit of a key
  changes nothing it observes.

**The hypothesis `2 ≤ b` is part of the theorem, not decoration** (`passes_lower_needs_two`): for
`b ≤ 1` the key domain has at most one element, every list is already sorted, and a `0`-probe plan
sorts all of them.  So the contract's unqualified `p < d` is false, and `2 ≤ b` is the exact
hypothesis that makes it true.
-/
import SortBounds.Projects.Domain.Model

namespace SortBounds.Projects.Domain

open Finset

/-! ### The radix order on keys -/

/-- The radix order on keys — `Instances.Radix.keyLe` specialised to `keys := id`. -/
abbrev KeyLe (d b : ℕ) : Key d b → Key d b → Prop := keyLe d b fun k => k

/-- The strict radix order on keys — `Instances.Radix.keyLt` specialised to `keys := id`. -/
abbrev KeyLt (d b : ℕ) : Key d b → Key d b → Prop := keyLt d b fun k => k

/-- A key is never strictly below itself, in the radix order of `Instances.Radix`. -/
theorem not_lowLt_self {d b : ℕ} (keys : Key d b → Fin d → Fin b) (a : Key d b) :
    ∀ (k : ℕ) (hk : k ≤ d), ¬ lowLt d b keys k hk a a
  | 0, _ => by
      intro h
      exact h
  | (k + 1), hk => by
      rintro (hlt | ⟨-, hrec⟩)
      · exact lt_irrefl _ hlt
      · exact not_lowLt_self keys a k (Nat.le_of_succ_le hk) hrec

/-- In a key domain with at most one key, the radix order is trivial. -/
theorem keyLe_of_subsingleton {d b : ℕ} [Subsingleton (Key d b)] (a c : Key d b) : KeyLe d b a c := by
  have h : c = a := Subsingleton.elim c a
  rw [h]
  exact not_lowLt_self (fun k => k) a d le_rfl

/-! ### The model: plans that sort -/

/-- **A `p`-probe plan sorts all keys** if its digest `codeOf`

* *refines* the radix order on keys — `codeOf k ≤ codeOf k' → KeyLe k k'` — so that ordering items
  by their digests orders them by their keys, and
* *separates* distinct keys — `codeOf k = codeOf k' → k = k'`.

Both clauses are forced by "sorts every list of keyed items".  The second is the subtle one: if two
distinct keys `k ≠ k'` had equal digests, take two items `a`, `b` carrying those keys.  The plan
outputs items ordered by their digests and has access to nothing else — it cannot see which item
came first, since its only input is digit values.  So on the two input lists `[a, b]` and `[b, a]`
it produces the same arrangement of `a` and `b`, and since `k ≠ k'` at most one of the two
arrangements is sorted by key.  A plan that is right on every input therefore has to separate every
pair of keys. -/
def SortsAllKeys {d b p : ℕ} (P : KeyProc d b p) : Prop :=
  (∀ k k' : Key d b, P.codeOf k ≤ P.codeOf k' → KeyLe d b k k') ∧
    ∀ k k' : Key d b, P.codeOf k = P.codeOf k' → k = k'

/-- The separating clause: a sorting plan's digest is injective on keys. -/
theorem SortsAllKeys.code_injective {d b p : ℕ} {P : KeyProc d b p} (h : SortsAllKeys P) :
    Function.Injective P.codeOf :=
  fun _ _ hkk' => h.2 _ _ hkk'

/-- Every key domain with at most one key is sorted by the `0`-probe plan that outputs the code
`0`.  (This is the reason `passes_lower` needs `2 ≤ b`.) -/
theorem exists_sortsAllKeys_zero_probe {d b : ℕ} [Subsingleton (Key d b)] :
    ∃ P : KeyProc d b 0, SortsAllKeys P := by
  refine ⟨⟨fun q hq => absurd hq (Nat.not_lt_zero q), fun _ => 0⟩, ?_, fun k k' _ => ?_⟩
  · intro k k' _
    exact keyLe_of_subsingleton k k'
  · exact Subsingleton.elim k k'

/-- **`p < d` with `b ≤ 1` does not rule out sorting**: on a one-element key domain the
`0`-probe plan sorts, although `0 < d`.  Hence the hypothesis `2 ≤ b` in `passes_lower` cannot be
dropped. -/
theorem passes_lower_needs_two :
    (∃ P : KeyProc 2 1 0, SortsAllKeys P) ∧ (∃ P : KeyProc 1 0 0, SortsAllKeys P) :=
  ⟨exists_sortsAllKeys_zero_probe, exists_sortsAllKeys_zero_probe⟩

/-! ### The lower bound -/

/-- **No `p < d` probe plan has an injective digest** — whatever else it does.

The plan's transcript reads at most `b ^ p` distinct value sequences (`card_le_pow_probes`), and its
digest is a function of what it read, so an injective digest would inject the `b ^ d` keys into
`b ^ p` sequences; `b ≥ 2` makes `b ^ ·` strictly monotone, giving `d ≤ p`.  This is the strong form
of the bound: `passes_lower` is its corollary for plans that sort. -/
theorem no_injective_code_of_lt {d b p : ℕ} (hb : 2 ≤ b) (hp : p < d) (P : KeyProc d b p) :
    ¬ Function.Injective P.codeOf := by
  intro hinj
  have hfib : ∀ k₁ ∈ (univ : Finset (Key d b)), ∀ k₂ ∈ univ,
      (∀ q, (P.trace k₁ q).2 = (P.trace k₂ q).2) → k₁ = k₂ := by
    intro k₁ _ k₂ _ h
    exact hinj (congrArg P.code (funext h))
  have hcard := card_le_pow_probes d b p P.trace univ hfib
  rw [Finset.card_univ, card_Key] at hcard
  have hle : d ≤ p := (pow_le_pow_iff_right₀ (by omega : 1 < b)).mp hcard
  omega

/-- **Pigeonhole form of the bound, for any key domain size `U`.**  If a set of keys is larger than
`b ^ p`, then *every* `p`-probe plan gives two of its keys the same digest: no `p`-probe plan
separates more than `b ^ p` keys.  With `b ^ p < U ≤ b ^ (p + 1)` this is the contract's ceiling —
`p + 1 = ⌈log_b U⌉` probes are needed — and with `U = b ^ d` it reads `d ≤ p`.  No hypothesis on
`b` is needed here. -/
theorem exists_code_collision {d b p : ℕ} (S : Finset (Key d b)) (P : KeyProc d b p)
    (h : b ^ p < S.card) : ∃ k ∈ S, ∃ k' ∈ S, k ≠ k' ∧ P.codeOf k = P.codeOf k' := by
  by_contra hcon
  push Not at hcon
  have hfib : ∀ k₁ ∈ S, ∀ k₂ ∈ S, (∀ q, (P.trace k₁ q).2 = (P.trace k₂ q).2) → k₁ = k₂ := by
    intro k₁ h₁ k₂ h₂ hval
    by_contra hne
    exact hcon k₁ h₁ k₂ h₂ hne (congrArg P.code (funext hval))
  exact absurd (card_le_pow_probes d b p P.trace S hfib) (by omega)

/-- **No `b`-ary procedure sorts `b ^ d` keys in `p < d` probes.**

A sorting plan separates every pair of its `b ^ d` keys (`SortsAllKeys.code_injective`), which
`no_injective_code_of_lt` rules out when `p < d`.  The witness case `b ≤ 1` is where the conclusion
fails, see `passes_lower_needs_two`. -/
theorem passes_lower {d b p : ℕ} (hb : 2 ≤ b) (hp : p < d) :
    ¬ ∃ P : KeyProc d b p, SortsAllKeys P := by
  rintro ⟨P, hP⟩
  exact no_injective_code_of_lt hb hp P hP.code_injective

/-- **`log_b U` probes are necessary**, in digits. -/
theorem probes_lower {d b p : ℕ} (hb : 2 ≤ b) {P : KeyProc d b p} (h : SortsAllKeys P) : d ≤ p := by
  by_contra hcon
  exact passes_lower (p := p) hb (Nat.not_le.mp hcon) ⟨P, h⟩

/-- **`log_b U` probes are necessary**, in the units of the contract: a plan that sorts all
`b ^ d` keys reads at least `log_b (b ^ d) = d` digits per key. -/
theorem probes_lower_logb {d b p : ℕ} (hb : 2 ≤ b) {P : KeyProc d b p} (h : SortsAllKeys P) :
    Real.logb b (Fintype.card (Key d b)) ≤ (p : ℝ) := by
  rw [logb_card_Key (by omega : 1 < b)]
  exact_mod_cast probes_lower hb h

/-! ### The operational reason: an unread digit -/

/-- A digit of `Fin b` other than `x`, available as soon as `b ≥ 2`. -/
def otherDigit {b : ℕ} (hb : 2 ≤ b) (x : Fin b) : Fin b :=
  if x.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

theorem otherDigit_ne {b : ℕ} (hb : 2 ≤ b) (x : Fin b) : otherDigit hb x ≠ x := by
  have hx := x.isLt
  unfold otherDigit
  split_ifs with h
  · intro he
    have := congrArg Fin.val he
    simp at this
    omega
  · intro he
    have := congrArg Fin.val he
    simp at this
    omega

/-- **Two keys that agree on everything a run reads give the same observation.**  `J` contains every
position the plan reads on its run against `k`, and `k'` agrees with `k` there; then the runs against
`k` and `k'` read the same positions and see the same values. -/
theorem obs_congr {d b p : ℕ} (P : KeyProc d b p) (k k' : Key d b) (J : Finset (Fin d))
    (hread : ∀ (q : ℕ) (hq : q < p),
      P.next q hq (fun s => P.obs k s.val (Nat.lt_trans s.isLt hq)) ∈ J)
    (heq : ∀ j ∈ J, k' j = k j) : P.valsAt k' = P.valsAt k := by
  have key : ∀ (q : ℕ) (hq : q < p), P.obs k' q hq = P.obs k q hq := by
    intro q
    induction q using Nat.strong_induction_on with
    | _ q ih =>
      intro hq
      rw [KeyProc.obs_eq, KeyProc.obs_eq]
      have hprefix : (fun s : Fin q => P.obs k' s.val (Nat.lt_trans s.isLt hq))
          = fun s : Fin q => P.obs k s.val (Nat.lt_trans s.isLt hq) := by
        funext s
        exact ih s.val s.isLt _
      rw [hprefix]
      exact heq _ (hread q hq)
  exact funext fun q => key q.val q.isLt

/-- The positions a run of `P` against `k` reads. -/
def readSet {d b p : ℕ} (P : KeyProc d b p) (k : Key d b) : Finset (Fin d) :=
  univ.image fun q : Fin p => P.next q.val q.isLt fun s => P.obs k s.val (Nat.lt_trans s.isLt q.isLt)

theorem mem_readSet {d b p : ℕ} (P : KeyProc d b p) (k : Key d b) (q : Fin p) :
    P.next q.val q.isLt (fun s => P.obs k s.val (Nat.lt_trans s.isLt q.isLt)) ∈ readSet P k :=
  Finset.mem_image_of_mem _ (Finset.mem_univ q)

/-- **Fewer than `d` probes leave two keys indistinguishable.**  A run of a `p`-probe plan on `k`
looks at most `p` of the `d` digit positions (`readSet`); with `p < d` some position `j` is never
looked at, and changing digit `j` of `k` changes no observation the plan makes (`b ≥ 2` supplies the
other digit).  So the plan's digest cannot separate `k` from `k'`, which is exactly what
`passes_lower` forbids. -/
theorem exists_obs_eq_of_lt {d b p : ℕ} (hb : 2 ≤ b) (hp : p < d) (P : KeyProc d b p)
    (k : Key d b) : ∃ k' : Key d b, k' ≠ k ∧ P.valsAt k' = P.valsAt k := by
  classical
  have hcard : (readSet P k).card ≤ p :=
    calc (readSet P k).card ≤ (univ : Finset (Fin p)).card :=
          Finset.card_image_le
      _ = p := by simp
  have hlt : (readSet P k).card < Fintype.card (Fin d) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := readSet P k) (t := univ) hlt
  refine ⟨Function.update k j₀ (otherDigit hb (k j₀)), ?_, ?_⟩
  · intro h
    have h1 : otherDigit hb (k j₀) = k j₀ := by
      have := congrFun h j₀
      simpa using this
    exact otherDigit_ne hb (k j₀) h1
  · refine obs_congr P k _ (readSet P k) (fun q hq => ?_) (fun j hj => ?_)
    · exact mem_readSet P k ⟨q, hq⟩
    · have hne : j ≠ j₀ := fun h => hj₀ (h ▸ hj)
      exact Function.update_of_ne hne _ _

/-- **The bound is about a whole digit domain, not about thin sets of keys.**  `⌈log_b U⌉` is *not*
the right answer for an arbitrary `U`-element set of keys: in `Key d 2`, the `d + 1` keys
`{0, e_1, …, e_d}` (the zero key together with the `d` keys carrying a single `1`) have
`⌈log_2(d + 1)⌉` well below `d`, yet `p < d` probes cannot separate them — whatever `p` positions the
plan reads on the zero key, some unit key `e_j` sits on an unread position and gets the same
observation.  This is why `probes_tight` is stated for the full domain `U = b ^ d`, which is the
case the contract asks for; there the digest can be the base-`b` value of the key itself. -/
theorem unit_key_collision {d p : ℕ} (hp : p < d) (P : KeyProc d 2 p) :
    ∃ j : Fin d,
      P.valsAt (Function.update (fun _ => 0) j ⟨1, by omega⟩) = P.valsAt (fun _ => 0) := by
  classical
  have hcard : (readSet P (fun _ => 0 : Key d 2)).card ≤ p :=
    calc (readSet P (fun _ => 0 : Key d 2)).card ≤ (univ : Finset (Fin p)).card :=
          Finset.card_image_le
      _ = p := by simp
  have hlt : (readSet P (fun _ => 0 : Key d 2)).card < Fintype.card (Fin d) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨j₀, -, hj₀⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := readSet P (fun _ => 0 : Key d 2)) (t := univ) hlt
  refine ⟨j₀, obs_congr P (fun _ => 0) _ (readSet P (fun _ => 0 : Key d 2)) (fun q hq => ?_)
    (fun j hj => ?_)⟩
  · exact mem_readSet P _ ⟨q, hq⟩
  · have hne : j ≠ j₀ := fun h => hj₀ (h ▸ hj)
    rw [Function.update_of_ne hne]

end SortBounds.Projects.Domain
