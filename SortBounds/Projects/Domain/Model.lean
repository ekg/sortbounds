/-
SortBounds/Projects/Domain/Model.lean

**The domain model: what a `b`-ary probe buys.**

The comparison bound `log₂(n!)` (`SortBounds.Comparison.LowerBound`) counts *binary* answers to
"is `a < b`?".  A procedure that is allowed to *read the key* instead gets a `b`-way answer per
probe, and the relevant information is then the size `U = b ^ d` of the key domain rather than
`n!`.  This file sets up that model and proves the counting half of it.

The objects:

* `Key d b = Fin d → Fin b`, a key written as `d` base-`b` digits (`card_Key`: `b ^ d` keys);
* `Probe d b p`, the transcript of a `p`-probe run: which digit was read at each step, and what it
  held;
* `KeyProc d b p`, a *probe plan*: at each step it picks a digit position from the values it has
  seen so far (so it is adaptive), and after `p` probes it outputs a natural-number *code*, its
  sorting digest, computed from the values read.

`card_le_pow_probes` is the engine: a set of keys that a probe transcript pries apart has at most
`b ^ p` members, which is `Core.card_le_pow_prefixFree` (Kraft) applied to the value sequences.

**Why a comparison sort is not a probe procedure — the separation, stated.**  The two models
differ in *what one step reveals*, and neither contains the other:

* a probe step reveals one digit of one key — one of `b` values, from a domain of `d` digits — and
  the plan may choose *which* digit next only from the digits seen so far.  Nothing else about the
  input is visible: not the position of the item in the input list, not which other items exist.
  Consequently two items with equal keys produce identical probe values (digit equality is implied
  by key equality), so probes *never* distinguish equal-keyed items, and a probe procedure that
  must be right for every input has to break such ties by something it cannot see;
* a comparison step reveals the order relation between *two positions* of the input — one of `2`
  (or `3`) values — and it distinguishes the `n!` arrangements of `n` pairwise distinct keys, at
  a cost of `log₂(n!) = Θ(n log n)` per list.

The counting bound of this file therefore applies to the *probe* currency only: it bounds how many
*distinct keys* a `p`-probe plan can tell apart, and `d` digit reads per key suffice to tell apart
all `b ^ d` of them (`SortBounds/Projects/Domain/Radix.lean`).  Applied to a comparison sort the
same counting would be vacuous — a comparison sort never has to tell two *keys* apart, only two
arrangements — and that is exactly why the comparison bound is not contradicted: the two models
charge different currencies (`Instances.Radix.radixComparisons` is literally `0` while the probe
count is `d`).
-/
import SortBounds.Core.Branching
import SortBounds.Instances.Radix

namespace SortBounds.Projects.Domain

open Finset

/-! ### Keys as digit vectors -/

/-- Keys as `d` digits in base `b`: the key domain has `b ^ d` elements.  (An `abbrev` so that the
`Fintype`/`DecidableEq` instances of `Fin d → Fin b` apply to it without transport.) -/
abbrev Key (d b : ℕ) := Fin d → Fin b

/-- **The key domain has `b ^ d` elements.**  `U = b ^ d` is the `U` of the contract. -/
theorem card_Key (d b : ℕ) : Fintype.card (Key d b) = b ^ d := by
  simp [Key]

/-- A `b`-way `p`-probe transcript: at each step, which digit was read, and what it held. -/
def Probe (d b p : ℕ) := Fin p → Fin d × Fin b

/-! ### Counting: `p` probes distinguish at most `b ^ p` keys -/

/-- **A `p`-probe transcript separates at most `b ^ p` keys.**

The hypothesis `hfiber` is the meaning of "separates": a transcript that reads the same *values*
off two keys cannot tell them apart, so a procedure that must be right on both must find them
equal.  The observed values are `p` answers from a `b`-element alphabet, hence `b ^ p`
possibilities — the prefix-free set of observations has all words of length exactly `p`, so
`Core.card_le_pow_of_prefixFree` (Kraft) applies directly.

The degenerate base `b = 0` is included: a `0`-ary probe carries no information, and then
`Key d 0` is empty unless `d = 0`. -/
theorem card_le_pow_probes (d b p : ℕ) (t : Key d b → Probe d b p) (S : Finset (Key d b))
    (hfiber : ∀ k₁ ∈ S, ∀ k₂ ∈ S, (∀ q, (t k₁ q).2 = (t k₂ q).2) → k₁ = k₂) :
    S.card ≤ b ^ p := by
  classical
  rcases Nat.eq_zero_or_pos b with hb | hb
  · -- a `0`-ary alphabet: no information, and the key domain is empty unless `d = 0`
    subst hb
    have hS : S.card ≤ 1 :=
      calc S.card ≤ Fintype.card (Key d 0) := Finset.card_le_univ S
        _ = 0 ^ d := card_Key d 0
        _ ≤ 1 := by cases d <;> simp
    rcases Nat.eq_zero_or_pos p with hp | hp
    · simpa [hp] using hS
    · have hS' : S.card = 0 := by
        rw [Finset.card_eq_zero]
        rcases Finset.eq_empty_or_nonempty S with h | ⟨k, hk⟩
        · exact h
        · exact absurd ((t k ⟨0, hp⟩).1) Fin.elim0
      rw [hS', Nat.zero_pow hp.ne']
  · haveI : NeZero b := ⟨hb.ne'⟩
    set v : Key d b → List (Fin b) := fun k => List.ofFn (fun q : Fin p => (t k q).2) with hv
    have hlen : ∀ k ∈ S, (v k).length ≤ p := by
      intro k _
      simp [hv]
    have hinj : ∀ k₁ ∈ S, ∀ k₂ ∈ S, v k₁ = v k₂ → k₁ = k₂ := by
      intro k₁ h₁ k₂ h₂ he
      refine hfiber k₁ h₁ k₂ h₂ fun q => ?_
      have hq := congrArg (fun l => l[q.val]'(by simp [hv])) he
      simpa [hv] using hq
    have hpre : ∀ x ∈ S.image v, ∀ y ∈ S.image v, x <+: y → x = y := by
      intro x hx y hy hxy
      obtain ⟨k₁, h₁, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k₂, h₂, rfl⟩ := Finset.mem_image.mp hy
      exact hxy.eq_of_length (by rw [hlen k₁ h₁, hlen k₂ h₂])
    have hmain : (S.image v).card ≤ b ^ p :=
      card_le_pow_of_prefixFree (P := S.image v) (c := p) hpre fun x hx => by
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        exact hlen k hk
    rwa [Finset.card_image_of_injOn hinj] at hmain

/-! ### Probe plans -/

/-- A `p`-probe plan — the model of a "digit-reading procedure".  `next` chooses the digit to read
at each step from the values observed so far (this is what makes the model *adaptive*, and it is
the only thing the procedure ever learns), and `code` is the natural-number digest the procedure
outputs after `p` probes, again a function of the observed values only. -/
structure KeyProc (d b p : ℕ) where
  /-- The digit read at step `q`, given the values observed at steps `0, …, q-1`. -/
  next : (q : ℕ) → q < p → (Fin q → Fin b) → Fin d
  /-- The digest the procedure outputs after the `p` probes. -/
  code : (Fin p → Fin b) → ℕ

namespace KeyProc

variable {d b p : ℕ}

/-- The digit values observed by the plan on the key `k`, step by step.  `vals P k q` is the
prefix of length `q` of the observation. -/
def vals (P : KeyProc d b p) (k : Key d b) : (q : ℕ) → q ≤ p → (Fin q → Fin b)
  | 0, _ => Fin.elim0
  | (q + 1), h =>
      Fin.snoc (P.vals k q (Nat.le_of_succ_le h))
        (k (P.next q (Nat.lt_of_succ_le h) (P.vals k q (Nat.le_of_succ_le h))))

/-- The complete observation of a `p`-probe run on the key `k`. -/
def valsAt (P : KeyProc d b p) (k : Key d b) : Fin p → Fin b :=
  P.vals k p le_rfl

/-- The first `q` values of a complete observation are the prefix `vals P k q`. -/
theorem valsAt_castSucc (P : KeyProc d b p) (k : Key d b) :
    ∀ (q : ℕ) (h : q ≤ p) (s : Fin q), P.valsAt k ⟨s.val, Nat.lt_of_lt_of_le s.isLt h⟩
      = P.vals k q h s
  | 0, _, s => s.elim0
  | (q + 1), h, s => by
      rcases Fin.eq_castSucc_or_eq_last s with ⟨i, rfl⟩ | rfl
      · rw [valsAt, vals, Fin.snoc_castSucc]
        exact valsAt_castSucc P k q (Nat.le_of_succ_le h) i
      · have hq : ¬ (q + 1 ≤ q) := Nat.not_succ_le_self q
        rw [valsAt, vals, Fin.snoc_last]
        exact absurd h (by omega)

/-- The value observed at step `q`: the last entry of the prefix of length `q + 1` is the digit
just read, and — the content of `next` — it is the digit of `k` at the position `next` chose. -/
theorem vals_succ_last (P : KeyProc d b p) (k : Key d b) (q : ℕ) (h : q < p) :
    P.vals k (q + 1) (Nat.succ_le_of_lt h) ⟨q, Nat.lt_succ_self q⟩
      = k (P.next q h (P.vals k q (Nat.le_of_lt h))) := by
  rw [vals, Fin.snoc_last]

/-- The full transcript of a run: at every step, the position read and the value found. -/
def trace (P : KeyProc d b p) (k : Key d b) : Probe d b p :=
  fun q => (P.next q.val q.isLt (P.vals k q.val (Nat.le_of_lt q.isLt)),
    P.valsAt k q)

/-- The value component of the transcript is the complete observation. -/
theorem trace_val (P : KeyProc d b p) (k : Key d b) (q : Fin p) : (P.trace k q).2 = P.valsAt k q :=
  rfl

/-- The digest that the procedure assigns to the key `k`. -/
def codeOf (P : KeyProc d b p) (k : Key d b) : ℕ := P.code (P.valsAt k)

end KeyProc

/-! ### The information content of the key domain -/

/-- **`log_b U` for `U = b ^ d`**: the domain `Key d b` carries exactly `d` base-`b` digits of
information. -/
theorem logb_card_Key {d b : ℕ} (hb : 1 < b) :
    Real.logb b (Fintype.card (Key d b)) = (d : ℝ) := by
  rw [card_Key, Nat.cast_pow, Real.logb_pow, Real.logb_self_eq_one hb, mul_one]

end SortBounds.Projects.Domain
