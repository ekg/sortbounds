/-
SortBounds/Projects/Domain/Model.lean

**The domain model: what a `b`-ary probe buys.**

The comparison bound `log₂(n!)` (`SortBounds.Comparison.LowerBound`) counts *binary* answers to
"is `a < b`?".  A procedure that may *read the key* instead gets a `b`-way answer per probe, and
the information that matters is then the size `U = b ^ d` of the key domain, not `n!`.  This file
sets up that model and proves its counting half.

The objects:

* `Key d b = Fin d → Fin b`, a key written as `d` base-`b` digits (`card_Key`: `b ^ d` keys);
* `Probe d b p`, the transcript of a `p`-probe run: which digit was read at each step, and what it
  held;
* `KeyProc d b p`, a *probe plan*: at each step it picks a digit position from the values it has
  seen so far (so it is adaptive), and after `p` probes it outputs a natural-number *code* — its
  sorting digest — computed from the values it observed.  Nothing else about the input is
  visible to it.

`card_le_pow_probes` is the engine: a set of keys that probe transcripts pry apart has at most
`b ^ p` members, which is `Core.card_le_pow_of_prefixFree` (Kraft) applied to the observed value
sequences.

**Why a comparison sort is not a probe procedure — the separation, stated.**  The two models
differ in *what one step reveals*, and neither contains the other:

* a probe step reveals one digit of one key — one of `b` values, out of `d` digits — and the plan
  may choose *which* digit to read next only from the digits read so far; it sees neither the
  position of the item in the input list nor which other items exist.  Equal keys have equal
  digits, so probe values can never distinguish two items with the same key;
* a comparison step reveals the order relation between *two positions* of the input — one of `2`
  values — and thereby distinguishes the `n!` arrangements of `n` pairwise distinct keys, at a
  cost of `log₂(n!) = Θ(n log n)` comparisons per list.

So the bound below counts *distinct keys*, and it applies to the probe currency only: `d` digit
reads per key separate all `b ^ d` keys (`SortBounds/Projects/Domain/Radix.lean` proves that, and
`Instances.Radix.radixSort` sorts with exactly `d` passes).  Reading the same count as a statement
about comparison sorts would be a category error — a comparison sort never has to tell two *keys*
apart, only two arrangements, and it does so using positional access that the probe model does not
have — and that is why the comparison bound is not contradicted here: the models charge different
currencies (`Instances.Radix.radixComparisons` is literally `0` while the probe count is `d`).

**Only the values are counted, not the positions.**  A transcript *names* a position at every step,
so `#(Probe d b p) = (b * d) ^ p`; but the position is the plan's own choice, made from the values
already read, so the information available after `p` probes is a *function of the value sequence*,
of which there are only `b ^ p`.  Counting `(b * d) ^ p` would be counting the algorithm's own
choices as if they were knowledge.  Hence the exponent below is `p`, and `card_le_pow_probes`
states its hypothesis in terms of the values.
-/
import SortBounds.Core.Branching
import SortBounds.Instances.Radix

namespace SortBounds.Projects.Domain

open Finset

/-! ### Keys as digit vectors -/

/-- Keys as `d` digits in base `b`: the key domain has `b ^ d` elements.  (An `abbrev`, so that
the `Fintype` and `DecidableEq` instances of `Fin d → Fin b` apply to it directly.) -/
abbrev Key (d b : ℕ) := Fin d → Fin b

/-- **The key domain has `b ^ d` elements.**  This `b ^ d` is the `U` of the contract. -/
theorem card_Key (d b : ℕ) : Fintype.card (Key d b) = b ^ d := by
  simp [Key]

/-- A `b`-way `p`-probe transcript: at each step, which digit was read, and what it held. -/
def Probe (d b p : ℕ) := Fin p → Fin d × Fin b

/-! ### Counting: `p` probes distinguish at most `b ^ p` keys -/

/-- The *values* a transcript reads, as a word over the `b`-element alphabet.  These — not the
positions, which the plan chose itself — are the information a run yields. -/
def valsWord {d b p : ℕ} (t : Key d b → Probe d b p) (k : Key d b) : List (Fin b) :=
  List.ofFn fun q : Fin p => (t k q).2

theorem valsWord_length {d b p : ℕ} (t : Key d b → Probe d b p) (k : Key d b) :
    (valsWord t k).length = p :=
  List.length_ofFn

/-- Equal value words are what it means for a transcript to read the same thing off two keys. -/
theorem valsWord_inj {d b p : ℕ} {t : Key d b → Probe d b p} {k₁ k₂ : Key d b}
    (h : valsWord t k₁ = valsWord t k₂) : ∀ q : Fin p, (t k₁ q).2 = (t k₂ q).2 :=
  fun q => congrFun (List.ofFn_inj.mp h) q

/-- **A `p`-probe transcript separates at most `b ^ p` keys.**

The hypothesis `hfiber` is what "separates" means: if the transcript reads the same *values* off
two keys then it cannot tell them apart, so a procedure that must be right on both has to see them
as equal.  The observed values are `p` answers from a `b`-element alphabet, i.e. a set of words of
length exactly `p` over `Fin b`, and `Core.card_le_pow_of_prefixFree` (Kraft) bounds such a set by
`b ^ p`; prefix-freeness is automatic because all words have the same length.

The degenerate base `b = 0` is included: a `0`-ary probe carries no information, and `Key d 0` is
empty unless `d = 0`. -/
theorem card_le_pow_probes (d b p : ℕ) (t : Key d b → Probe d b p) (S : Finset (Key d b))
    (hfiber : ∀ k₁ ∈ S, ∀ k₂ ∈ S, (∀ q, (t k₁ q).2 = (t k₂ q).2) → k₁ = k₂) :
    S.card ≤ b ^ p := by
  classical
  rcases Nat.eq_zero_or_pos b with hb | hb
  · -- a `0`-ary alphabet: no information at all
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
        · exact Fin.elim0 ((t k ⟨0, hp⟩).2)
      rw [hS', Nat.zero_pow hp]
  · have : NeZero b := ⟨hb.ne'⟩
    have hpre : ∀ x ∈ S.image (valsWord t), ∀ y ∈ S.image (valsWord t), x <+: y → x = y := by
      intro x hx y hy hxy
      obtain ⟨k₁, h₁, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k₂, h₂, rfl⟩ := Finset.mem_image.mp hy
      exact hxy.eq_of_length (by rw [valsWord_length, valsWord_length])
    have hlen : ∀ k ∈ S, (valsWord t k).length ≤ p := fun k _ => by rw [valsWord_length]
    have hinj : Set.InjOn (valsWord t) ↑S := fun k₁ h₁ k₂ h₂ he =>
      hfiber k₁ h₁ k₂ h₂ (valsWord_inj he)
    have hmain : (S.image (valsWord t)).card ≤ b ^ p :=
      card_le_pow_of_prefixFree (P := S.image (valsWord t)) (c := p) hpre fun x hx => by
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        exact hlen k hk
    rwa [Finset.card_image_of_injOn hinj] at hmain

/-! ### Probe plans -/

/-- A `p`-probe plan — the model of a "digit-reading procedure".  `next` chooses the digit to read
at each step from the values observed so far (this is what makes the model adaptive, and the
values are the only thing the procedure ever learns); `code` is the natural-number digest the
procedure outputs after `p` probes, again a function of the observed values only. -/
structure KeyProc (d b p : ℕ) where
  /-- The digit read at step `q`, given the values observed at steps `0, …, q-1`. -/
  next : (q : ℕ) → q < p → (Fin q → Fin b) → Fin d
  /-- The digest the procedure outputs after its `p` probes. -/
  code : (Fin p → Fin b) → ℕ

namespace KeyProc

variable {d b p : ℕ}

/-- The digit observed at step `q` of a run of the plan `P` on the key `k`: the plan picks the
position from the values it saw at the earlier steps. -/
def obs (P : KeyProc d b p) (k : Key d b) (q : ℕ) (hq : q < p) : Fin b :=
  k (P.next q hq fun s => obs P k s.val (Nat.lt_trans s.isLt hq))
termination_by q
decreasing_by exact s.isLt

/-- One step of a run: the value observed at step `q` is the digit of `k` at the position that the
plan picks from the earlier observations. -/
theorem obs_eq (P : KeyProc d b p) (k : Key d b) (q : ℕ) (hq : q < p) :
    P.obs k q hq = k (P.next q hq fun s => P.obs k s.val (Nat.lt_trans s.isLt hq)) := by
  rw [obs]

/-- The complete observation of a `p`-probe run on the key `k`. -/
def valsAt (P : KeyProc d b p) (k : Key d b) : Fin p → Fin b :=
  fun q => P.obs k q.val q.isLt

/-- The full transcript of a run: at every step, the position read and the value found. -/
def trace (P : KeyProc d b p) (k : Key d b) : Probe d b p :=
  fun q => (P.next q.val q.isLt fun s => P.obs k s.val (Nat.lt_trans s.isLt q.isLt), P.valsAt k q)

/-- The value component of the transcript is the complete observation. -/
theorem trace_val (P : KeyProc d b p) (k : Key d b) (q : Fin p) : (P.trace k q).2 = P.valsAt k q :=
  rfl

/-- The step-`q` position of the transcript is the position the plan picks from the observations it
has made before step `q`. -/
theorem trace_fst (P : KeyProc d b p) (k : Key d b) (q : Fin p) :
    (P.trace k q).1 = P.next q.val q.isLt fun s => P.obs k s.val (Nat.lt_trans s.isLt q.isLt) :=
  rfl

/-- The digest that the procedure assigns to the key `k`. -/
def codeOf (P : KeyProc d b p) (k : Key d b) : ℕ := P.code (P.valsAt k)

end KeyProc

/-! ### The information content of a key -/

/-- **`log_b U = d` for `U = b ^ d`**: the domain `Key d b` carries exactly `d` base-`b` digits of
information. -/
theorem logb_card_Key {d b : ℕ} (hb : 1 < b) :
    Real.logb b (Fintype.card (Key d b)) = (d : ℝ) := by
  rw [card_Key, Nat.cast_pow, Real.logb_pow, Real.logb_self_eq_one (by exact_mod_cast hb), mul_one]

end SortBounds.Projects.Domain
