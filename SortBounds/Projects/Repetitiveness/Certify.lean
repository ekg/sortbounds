/-
SortBounds/Projects/Repetitiveness/Certify.lean

**M3, part 2: the certification system — a certified attractor and the verifier that
produces it.**

An index's space guarantee comes from *some* measure, and the two measures of this lane are
not equally computable (`Measures.lean`, `docs/research/space.md`:114): `γ` (smallest
attractor) is NP-hard to compute, while `δ` (substring complexity) has a linear-time
algorithm.  So a system built on `γ` cannot *find* the optimum; what it can do is

* carry an attractor **together with a proof** that it is one — `AttractorCertificate`, whose
  size is a certified upper bound on `γ` and hence (by `delta_le_gamma`) on `δ`; and
* **verify** a candidate position set with a decision procedure — `checkAttractor`, a
  computable `Bool`-valued scan (`checkAttractor_eq_true_iff`).

Together those two give a proved interval `[δ, c]` on the smallest attractor (`c` the
certified size), which is exactly what the NP-hardness of `γ` leaves available: `δ` is
computable exactly and `c` is certified, and `γ = Ω(δ log(n/δ))` (KNP Thm III.3) says the
interval can be genuinely wide.

**What the verifier is.**  `checkAttractor s Γ` inspects every factor *occurrence* `(i, k)`
of `s`, every attractor position `p ∈ Γ`, and every offset `d < k`, and asks whether the
length-`k` window starting at `p - d` equals the window starting at `i`; it returns `true`
iff every occurrence has such a covering copy.  It is `List.range`/`List.finRange`/
`List.any`/`List.all` recursion, and `decide` appears only on decidable equality (`k = 0`),
`ℕ` comparisons (`d ≤ p`, `p - d + k ≤ s.length`), decidable `Finset` membership (`p ∈ Γ`)
and `==` on windows — never on a `Prop`-valued classical definition, and nowhere does it
search unboundedly.  It therefore *runs* (`#eval checkAttractor ababa ababaAttractor`
returns `true`), which is the whole point of it.  It is *not* the `O(n)` verifier of
Kempa–Prezza (that needs suffix-array/LCE machinery this lane does not have); the scan is
`n² · |Γ| · k` window comparisons of length `k` in the worst case.

**The propositional reading.**  `CoversAllFactors s Γ` is the `Prop` the scan decides —
"every nonempty factor occurrence is covered by a position of `Γ`" — and
`isAttractor_iff_coversAllFactors` shows it is exactly `IsAttractor s Γ`.  Splitting the iff
this way keeps the arithmetic of windows (`coversPos_iff`) apart from the combinatorics of
the scan (`checkAttractor_iff_coversAllFactors`).
-/
import Mathlib
import SortBounds.Projects.Repetitiveness.Basic
import SortBounds.Projects.Repetitiveness.Attractor
import SortBounds.Projects.Repetitiveness.Measures

namespace SortBounds.Projects.Repetitiveness

variable {α : Type*} [DecidableEq α]

/-! ### The scan -/

/-- **Is the length-`k` factor occurrence at `i` covered by position `p`?**  Yes iff for some
offset `d < k` with `d ≤ p`, the window of length `k` starting at `p - d` (inside `s`) equals
the window starting at `i`.  `p - d` is the start of the covering occurrence, and `p` lies
inside it because `d < k`.  Computable: `List.range`, `Bool.and`, `decide` on `ℕ`
comparisons and `==` on windows. -/
def coversPos (s : List α) (i k p : ℕ) : Bool :=
  (List.range k).any fun d =>
    (decide (d ≤ p) && decide ((p - d) + k ≤ s.length)) &&
      ((s.drop (p - d)).take k == (s.drop i).take k)

/-- The unfoldings of `coversPos`: a `true` scan is a witness `(d, p - d)` of the shape
`IsAttractor` asks for. -/
theorem coversPos_iff (s : List α) (i k p : ℕ) :
    coversPos s i k p = true ↔
      ∃ d, d < k ∧ d ≤ p ∧ (p - d) + k ≤ s.length ∧
        (s.drop (p - d)).take k = (s.drop i).take k := by
  simp only [coversPos, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, and_assoc]

/-- A factor occurrence is covered by *its own* positions: an occurrence starting at `i` covers
every `p ∈ [i, i+k)` (nothing at all when `k = 0`).  This is what makes the greedy
construction in `Greedy.lean` add positions. -/
theorem coversPos_of_le_of_lt {s : List α} {i k p : ℕ} (hik : i + k ≤ s.length)
    (h1 : i ≤ p) (h2 : p < i + k) : coversPos s i k p = true := by
  refine (coversPos_iff s i k p).mpr ⟨p - i, by omega, by omega, by omega, ?_⟩
  rw [show p - (p - i) = i by omega]

/-- **Does some position of `Γ` cover the length-`k` factor occurrence at `i`?**  A scan over
all positions, keeping only those in `Γ`. -/
def coversFactor (s : List α) (Γ : Finset (Fin s.length)) (i k : ℕ) : Bool :=
  (List.finRange s.length).any fun p => decide (p ∈ Γ) && coversPos s i k (p : ℕ)

theorem coversFactor_iff (s : List α) (Γ : Finset (Fin s.length)) (i k : ℕ) :
    coversFactor s Γ i k = true ↔ ∃ p ∈ Γ, coversPos s i k (p : ℕ) = true := by
  simp only [coversFactor, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨x, -, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨p, hp, hcov⟩
    exact ⟨p, List.mem_finRange p, hp, hcov⟩

/-- **The verifier: a program, not a proposition.**  Scan all starts `i` and all
lengths `k`; skip the empty factor (`k = 0`) and the lengths that do not fit (`i + k >
s.length`); require the remaining occurrences to be covered by `Γ`.  Every piece is a
`List`/`Bool` recursion, so this evaluates (see the `by decide` examples at the end of the
file) — unlike `decide` on `IsAttractor` itself. -/
def checkAttractor (s : List α) (Γ : Finset (Fin s.length)) : Bool :=
  (List.range (s.length + 1)).all fun i =>
    (List.range (s.length + 1)).all fun k =>
      (decide (k = 0) || decide (s.length < i + k)) || coversFactor s Γ i k

/-- The `Prop` that `checkAttractor` decides: every nonempty factor occurrence is covered by a
position of `Γ`. -/
def CoversAllFactors (s : List α) (Γ : Finset (Fin s.length)) : Prop :=
  ∀ i k : ℕ, 1 ≤ k → i + k ≤ s.length → ∃ p ∈ Γ, coversPos s i k (p : ℕ) = true

/-- The scan is faithful to its propositional reading. -/
theorem checkAttractor_iff_coversAllFactors (s : List α) (Γ : Finset (Fin s.length)) :
    checkAttractor s Γ = true ↔ CoversAllFactors s Γ := by
  simp only [checkAttractor, CoversAllFactors, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, coversFactor_iff]
  constructor
  · intro h i k hk hik
    have hi : i < s.length + 1 := by omega
    have hk' : k < s.length + 1 := by omega
    rcases h i hi k hk' with (h0 | hlt) | hcov
    · omega
    · omega
    · exact hcov
  · intro h i hi k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact Or.inl (Or.inl rfl)
    · by_cases hlt : s.length < i + k
      · exact Or.inl (Or.inr hlt)
      · exact Or.inr (h i k hkpos (by omega))

/-! ### The propositional reading is `IsAttractor` -/

/-- **Covering occurrences are exactly attractor witnesses.**  For an occurrence `s[i..i+k)`,
a position `p` covering it sits at offset `d < k` inside a copy of the factor starting at
`p - d`, so the copy is `s[p-d .. p-d+k)` — an occurrence of the factor containing `p`, which
is what `IsAttractor` requires (and conversely). -/
theorem isAttractor_iff_coversAllFactors (s : List α) (Γ : Finset (Fin s.length)) :
    IsAttractor s Γ ↔ CoversAllFactors s Γ := by
  constructor
  · -- a factor occurrence covering an attractor position is a covered occurrence
    intro hΓ i k hk hik
    obtain ⟨i', j', -, hj', heq, p, hp, h1, h2⟩ := hΓ i (i + k) (by omega) hik
    have hlen1 : (factorOcc s i' j').length = j' - i' := factorOcc_length hj'
    have hlen2 : (factorOcc s i (i + k)).length = k := by
      rw [factorOcc_self, List.length_take, List.length_drop]
      omega
    rw [heq, hlen2] at hlen1
    have hj'k : j' = i' + k := by omega
    refine ⟨p, hp, (coversPos_iff s i k (p : ℕ)).mpr ⟨(p : ℕ) - i', by omega, by omega, by omega, ?_⟩⟩
    have hstart : (p : ℕ) - ((p : ℕ) - i') = i' := by omega
    have hleft : (s.drop i').take k = factorOcc s i' j' := by
      rw [factorOcc, ← hlen1]
    rw [hstart, hleft, heq, factorOcc_self]
  · -- a covered occurrence is an attractor witness for its own factor
    intro h i j hij hj
    obtain ⟨p, hp, hcov⟩ := h i (j - i) (by omega) (by omega)
    obtain ⟨d, hd, hdp, hbk, heq⟩ := (coversPos_iff s i (j - i) (p : ℕ)).mp hcov
    refine ⟨(p : ℕ) - d, (p : ℕ) - d + (j - i), by omega, by omega, ?_, p, hp, by omega, by omega⟩
    rw [factorOcc, factorOcc,
      show (p : ℕ) - d + (j - i) - ((p : ℕ) - d) = j - i by omega]
    exact heq

/-- **The verifier: `checkAttractor s Γ = true` iff `Γ` is an attractor of `s`.**  The
verification task is the one Kempa–Prezza solve in linear time (`docs/research/space.md`, and
the lane README's M3 note that *finding* `γ` is NP-hard while *verifying* a candidate is
cheap); here it is carried out by a `Bool`-valued program, so a passing run is a proof and
`AttractorCertificate.ofCheck` below turns it into one.  (Contrast `isAttractor_iff_check`,
which is a statement *about* `Prop`s; nothing here is decided classically.  This
implementation scans plainly — `n² · |Γ| · k` window comparisons of length `k` in the worst
case — rather than with the suffix-array/LCE machinery a linear-time verifier needs, which
this lane does not have.  It is polynomial and, unlike the propositions, it *runs*.) -/
theorem checkAttractor_eq_true_iff {s : List α} {Γ : Finset (Fin s.length)} :
    checkAttractor s Γ = true ↔ IsAttractor s Γ :=
  (checkAttractor_iff_coversAllFactors s Γ).trans (isAttractor_iff_coversAllFactors s Γ).symm

/-! ### Certified attractors -/

/-- **A certified attractor**: a position set together with a proof that it is an attractor.
`pos.card` is a certified upper bound on `γ` (hence on `δ`), obtained without solving the
NP-hard problem of minimising. -/
structure AttractorCertificate (s : List α) where
  /-- The positions of the certified attractor. -/
  pos : Finset (Fin s.length)
  /-- The proof that they really do hit every factor. -/
  isAtt : IsAttractor s pos

namespace AttractorCertificate

variable {s : List α}

/-- **The certified upper bound on `delta` (lower end of the interval)**: any valid attractor of size `c` gives
`δ ≤ c`. -/
theorem delta_le (c : AttractorCertificate s) : delta s ≤ c.pos.card :=
  delta_le_card_attractor c.isAtt

omit [DecidableEq α] in
/-- The certified upper bound: `γ ≤ c`.  With `delta_le` this is the interval `[δ, γ] ⊆ [δ, c]`
that the certified attractor pins down. -/
theorem gamma_le (c : AttractorCertificate s) : gamma s ≤ c.pos.card :=
  gamma_le_card_attractor c.isAtt

omit [DecidableEq α] in
/-- A certificate is never larger than the string. -/
theorem card_le_length (c : AttractorCertificate s) : c.pos.card ≤ s.length := by
  have := Finset.card_le_univ c.pos
  simpa using this

/-- **A passing verification run is a certificate**: the decision procedure feeds the
structure, so a program can produce certified bounds. -/
def ofCheck (Γ : Finset (Fin s.length)) (h : checkAttractor s Γ = true) :
    AttractorCertificate s :=
  ⟨Γ, checkAttractor_eq_true_iff.mp h⟩

@[simp]
theorem ofCheck_pos (Γ : Finset (Fin s.length)) (h : checkAttractor s Γ = true) :
    (ofCheck Γ h).pos = Γ := rfl

end AttractorCertificate

/-! ### The running example, certified -/

/-- `{0, 1}` is a certified attractor of `"ababa"`. -/
def ababaCertificate : AttractorCertificate ababa :=
  ⟨ababaAttractor, ababa_isAttractor⟩

theorem ababaCertificate_card : ababaCertificate.pos.card = 2 :=
  ababaAttractor_card

/-- On `"ababa"` the certified interval is a point: `δ = 2 ≤ 2 = |Γ|`. -/
example : delta ababa ≤ ababaCertificate.pos.card :=
  ababaCertificate.delta_le

/-- The verifier accepts `{0, 1}` for `"ababa"` — by computation, not by `decide` on a
`Prop`-valued classical definition: this evaluates the `Bool`-valued scan. -/
example : checkAttractor ababa ababaAttractor = true := by decide

/-- The verifier rejects `{0}` for `"ababa"`: the factor `b` at position `1` is covered by no
occurrence containing position `0`. -/
example : checkAttractor ababa ({(⟨0, by decide⟩ : Fin ababa.length)} : Finset (Fin ababa.length))
    = false := by decide

/-- A second accepted instance, on a set that is not a prefix: `{1, 2}` hits every factor of
`"abab"` (`a` at `2`, `b` at `1`, and every longer factor occurs at `0` or `1`). -/
example : checkAttractor (['a', 'b', 'a', 'b'] : List Char)
    ({(⟨1, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 4)} : Finset (Fin 4)) = true := by decide

/-- A rejected instance where two positions are still not enough: `"abc"` has three distinct
characters, and a length-`1` factor is only covered *at* an attractor position. -/
example : checkAttractor (['a', 'b', 'c'] : List Char)
    ({(⟨0, by decide⟩ : Fin 3), (⟨1, by decide⟩ : Fin 3)} : Finset (Fin 3)) = false := by decide

/-- The empty string has the empty certified attractor. -/
def nilCertificate : AttractorCertificate ([] : List Char) :=
  ⟨∅, isAttractor_mono (isAttractor_univ ([] : List Char)) (Finset.empty_subset _)⟩

/-- The verifier accepts the empty position set for the empty string. -/
example : checkAttractor ([] : List Char) ∅ = true := by decide

end SortBounds.Projects.Repetitiveness
