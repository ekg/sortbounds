/-
SortBounds/Projects/Repetitiveness/Attractor.lean

**M0: the counting core of `δ ≤ γ`** (Kempa–Kociumaka–Prezza, Lemma II.4, verbatim in
`docs/research/space.md`):

> "Every length-`k` substring has an occurrence covering an attractor position, so there
> can be at most `kγ` distinct substrings of length `k`, that is, `d_k(S)/k ≤ γ` for all
> `k ≤ n`."

The formal content is `distinctFactors_card_le_mul_attractor`: a length-`k` factor `f` has
an occurrence *covering* some attractor position `p`, and the pair
`(p, offset of f's start within the window ending at p)` determines `f`.  There are
`|Γ|` choices of `p` and at most `k` offsets, so `d_k ≤ k·|Γ|`.

The injection is packaged as an inclusion into an explicit image
(`Γ × {0,…,k-1} → words`, `(p, d) ↦ s[p-d .. p-d+k)`) rather than as a function defined by
choice, so no `Classical.choose` and no injectivity proof about a choice function is
needed.

**Side condition.**  The lemma is stated for `1 ≤ k`.  It is *false* at `k = 0`: the empty
word is a factor of every string, occurring at the empty interval `[i, i)`, which contains
no position at all, so no attractor can cover it and `d_0 = 1 > 0·|Γ|`.  KNP's "for all
`k ≤ n`" silently means `1 ≤ k ≤ n` for the same reason.  No upper bound `k ≤ s.length` is
needed: for `k > s.length` the set of factors is empty (`distinctFactors` only counts
starts with `i + k ≤ s.length`), and the inequality holds trivially.

From this we get the maximization form `δ ≤ γ` used by KNP: for *every* attractor `Γ`,
`max_k d_k / k ≤ |Γ|` (`substringComplexity_le_card_attractor`), i.e. the substring
complexity `δ` is a lower bound for the attractor size.  With `minAttractorSize` this reads
`substringComplexity s ≤ minAttractorSize s`, i.e. `δ ≤ γ`.

**M2 (the characterization) is only half true, and the false half is not attempted.**  The
lane contract proposed "`min attractor size = max_k d_k / k`".  The `≤` half is exactly the
counting lemma above.  The `≥` half — "some attractor is no larger than `δ`" — is *false in
general*: Kempa–Kociumaka–Prezza (IEEE TIT 2023) Thm III.3 proves that for every `n` and
`δ ∈ [2..n]` there is a string with `γ = Ω(δ log(n/δ))`, i.e. attractors can exceed the
substring complexity by a logarithmic factor (`docs/research/space.md` §1 separates
`γ = Ω(δ log(n/δ))` against `δ ≤ γ`).  So there is no `min attractor = max d_k/k` to prove;
what is true — and what is proved here — is `δ ≤ γ`, i.e. `substringComplexity` is a lower
bound for every attractor size.
-/
import Mathlib
import SortBounds.Projects.Repetitiveness.Basic

namespace SortBounds.Projects.Repetitiveness

variable {α : Type*} [DecidableEq α]

/-- **A factor has a covering occurrence.**  Every length-`k` factor (`k ≥ 1`) of `s` has
an occurrence starting `d < k` positions before some attractor position `p`. -/
theorem exists_cover_of_isAttractor {s : List α} {Γ : Finset (Fin s.length)}
    (hΓ : IsAttractor s Γ) {k : ℕ} (hk : 1 ≤ k) {f : List α}
    (hf : f ∈ distinctFactors s k) :
    ∃ (p : Fin s.length) (d : ℕ), p ∈ Γ ∧ d < k ∧ (s.drop ((p : ℕ) - d)).take k = f := by
  obtain ⟨i, hik, hf'⟩ := mem_distinctFactors.mp hf
  -- an occurrence of this factor which covers an attractor position
  obtain ⟨i', j', -, hj', heq, p, hp, h1, h2⟩ := hΓ i (i + k) (by omega) hik
  -- both occurrences have length `k`, so the covering occurrence starts exactly `k` before `j'`
  have hlen1 : (factorOcc s i' j').length = j' - i' := factorOcc_length hj'
  have hlen2 : (factorOcc s i (i + k)).length = k := by
    rw [factorOcc_self, List.length_take, List.length_drop]
    omega
  rw [heq, hlen2] at hlen1
  have hj'k : j' = i' + k := by omega
  refine ⟨p, (p : ℕ) - i', hp, by omega, ?_⟩
  have hstart : (p : ℕ) - ((p : ℕ) - i') = i' := by omega
  rw [hstart]
  have hleft : (s.drop i').take k = factorOcc s i' j' := by
    rw [factorOcc, ← hlen1]
  rw [hleft, heq, ← hf', factorOcc_self]

/-- **The counting lemma (KNP Lemma II.4).**  A length-`k` factor occurrence covering an
attractor position is determined by that position and the offset, so there are at most
`k · |Γ|` distinct length-`k` factors. -/
theorem distinctFactors_card_le_mul_attractor {s : List α} {Γ : Finset (Fin s.length)}
    (hΓ : IsAttractor s Γ) (k : ℕ) (hk : 1 ≤ k) :
    (distinctFactors s k).card ≤ k * Γ.card := by
  classical
  -- the candidates: an attractor position and an offset
  set D : Finset (Fin s.length × ℕ) := Γ.product (Finset.range k) with hD
  have hDcard : D.card = Γ.card * k := by simp [hD]
  have hsub : distinctFactors s k ⊆
      D.image (fun x : Fin s.length × ℕ => (s.drop ((x.1 : ℕ) - x.2)).take k) := by
    intro f hf
    obtain ⟨p, d, hp, hdk, hfd⟩ := exists_cover_of_isAttractor hΓ hk hf
    exact Finset.mem_image.mpr
      ⟨(p, d), Finset.mem_product.mpr ⟨hp, Finset.mem_range.mpr hdk⟩, hfd⟩
  calc (distinctFactors s k).card
      ≤ (D.image (fun x : Fin s.length × ℕ => (s.drop ((x.1 : ℕ) - x.2)).take k)).card :=
        Finset.card_le_card hsub
    _ ≤ D.card := Finset.card_image_le
    _ = Γ.card * k := hDcard
    _ = k * Γ.card := Nat.mul_comm _ _

/-- `d_k / k ≤ γ`, the literal form of KNP's conclusion. -/
theorem dk_div_le_attractor {s : List α} {Γ : Finset (Fin s.length)} (hΓ : IsAttractor s Γ)
    {k : ℕ} (hk : 1 ≤ k) : (distinctFactors s k).card / k ≤ Γ.card :=
  Nat.div_le_of_le_mul (distinctFactors_card_le_mul_attractor hΓ k hk)

/-- The substring complexity `δ = max {d_k / k : 1 ≤ k ≤ n}` of KNP (Def. II.1). -/
noncomputable def substringComplexity (s : List α) : ℕ :=
  (Finset.Icc 1 s.length).sup (fun k => (distinctFactors s k).card / k)

/-- **`δ ≤ γ`**: the substring complexity of `s` is at most the size of any attractor. -/
theorem substringComplexity_le_card_attractor {s : List α} {Γ : Finset (Fin s.length)}
    (hΓ : IsAttractor s Γ) : substringComplexity s ≤ Γ.card := by
  refine Finset.sup_le ?_
  intro k hk
  obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hk
  exact dk_div_le_attractor hΓ h1

omit [DecidableEq α] in
/-- If `Γ` is an attractor then so is any superset: `≥ γ` positions always suffice
(`isAttractor_univ` is the extreme case). -/
theorem isAttractor_mono {s : List α} {Γ Γ' : Finset (Fin s.length)} (hΓ : IsAttractor s Γ)
    (hsub : Γ ⊆ Γ') : IsAttractor s Γ' := by
  intro i j hij hj
  obtain ⟨i', j', h1, h2, h3, p, hp, h4, h5⟩ := hΓ i j hij hj
  exact ⟨i', j', h1, h2, h3, p, hsub hp, h4, h5⟩

/-! ### `δ ≤ γ`: the substring complexity against the *minimal* attractor size -/

/-- The attractors of `s`, as a finite set of position sets. -/
noncomputable def attractors (s : List α) : Finset (Finset (Fin s.length)) := by
  classical
  exact Finset.univ.filter (fun Γ => IsAttractor s Γ)

omit [DecidableEq α] in
theorem mem_attractors {s : List α} {Γ : Finset (Fin s.length)} :
    Γ ∈ attractors s ↔ IsAttractor s Γ := by
  classical
  simp [attractors]

omit [DecidableEq α] in
theorem attractors_nonempty (s : List α) : (attractors s).Nonempty := by
  classical
  exact ⟨Finset.univ, by simp [mem_attractors, isAttractor_univ]⟩

/-- The sizes of the attractors of `s`. -/
noncomputable def attractorSizes (s : List α) : Finset ℕ :=
  (attractors s).image Finset.card

omit [DecidableEq α] in
theorem attractorSizes_nonempty (s : List α) : (attractorSizes s).Nonempty := by
  obtain ⟨Γ, hΓ⟩ := attractors_nonempty s
  exact ⟨Γ.card, Finset.mem_image.mpr ⟨Γ, hΓ, rfl⟩⟩

/-- The smallest size of an attractor of `s`, KNP's `γ`.  Well defined because the full
position set is always an attractor (`isAttractor_univ`). -/
noncomputable def minAttractorSize (s : List α) : ℕ :=
  (attractorSizes s).min' (attractorSizes_nonempty s)

omit [DecidableEq α] in
/-- A minimal attractor: some attractor realises `minAttractorSize`. -/
theorem exists_attractor_card_eq_minAttractorSize (s : List α) :
    ∃ Γ : Finset (Fin s.length), IsAttractor s Γ ∧ Γ.card = minAttractorSize s := by
  classical
  obtain ⟨Γ, hΓ, hcard⟩ := Finset.mem_image.mp (Finset.min'_mem (attractorSizes s) _)
  exact ⟨Γ, mem_attractors.mp hΓ, hcard⟩

omit [DecidableEq α] in
/-- `minAttractorSize` is a lower bound for the size of every attractor. -/
theorem minAttractorSize_le {s : List α} {Γ : Finset (Fin s.length)} (hΓ : IsAttractor s Γ) :
    minAttractorSize s ≤ Γ.card := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨Γ, mem_attractors.mpr hΓ, rfl⟩)

/-- **`δ ≤ γ`**: the substring complexity of `s` is at most the size of its smallest
attractor (`γ` = minimum attractor size, Kempa–Prezza's notation).  This is the `≤` half
of the characterization `min attractor size = max_k d_k / k`; the other half is **false**
in general — KNP Lemma III.2 / Thm III.3 give strings with `δ ≤ 2` and `γ ≥ ½⌊log n⌋`
(`docs/research/space.md` :153-157). -/
theorem substringComplexity_le_minAttractorSize (s : List α) :
    substringComplexity s ≤ minAttractorSize s := by
  obtain ⟨Γ, hΓ, hcard⟩ := exists_attractor_card_eq_minAttractorSize s
  rw [← hcard]
  exact substringComplexity_le_card_attractor hΓ

/-! ### The bound on the running example -/

/-- **Every attractor of `"ababa"` needs two positions**: a length-1 factor is covered only
by an occurrence *at* the attractor position (`isAttractor_take_one`), and `"ababa"` has two
distinct characters `a` (at position `0`) and `b` (at position `1`). -/
theorem two_le_card_of_isAttractor_ababa {Γ : Finset (Fin ababa.length)}
    (h : IsAttractor ababa Γ) :
    2 ≤ Γ.card := by
  obtain ⟨p, hp, hp'⟩ := isAttractor_take_one (s := ababa) h (i := 0) (by decide)
  obtain ⟨q, hq, hq'⟩ := isAttractor_take_one (s := ababa) h (i := 1) (by decide)
  have hpq : p ≠ q := by
    intro hpq
    rw [← hpq, hp'] at hq'
    exact absurd hq' (by decide)
  have hsub : ({p, q} : Finset (Fin ababa.length)) ⊆ Γ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hq
  calc 2 = ({p, q} : Finset (Fin ababa.length)).card := by simp [hpq]
    _ ≤ Γ.card := Finset.card_le_card hsub

/-- For `"ababa"` the counting bound is tight: `Γ = {0, 1}` has size `2` and the substring
complexity is also `2` (`d_1 = d_2 = 2`, `d_3 = d_4 = 2`, and `2/1 = 2` is the maximum), so
`δ = γ = 2` for this word — the *equality* of the proposed characterization does hold here,
even though it fails for the strings of KNP Thm III.3 in general. -/
theorem ababa_substringComplexity : substringComplexity ababa = 2 := by decide

theorem ababa_minAttractorSize : minAttractorSize ababa = 2 := by
  refine le_antisymm ?_ ?_
  · calc minAttractorSize ababa ≤ ababaAttractor.card := minAttractorSize_le ababa_isAttractor
      _ = 2 := ababaAttractor_card
  · obtain ⟨Γ, hΓ, hcard⟩ := exists_attractor_card_eq_minAttractorSize ababa
    rw [← hcard]
    exact two_le_card_of_isAttractor_ababa hΓ

example : (distinctFactors ababa 3).card ≤ 3 * ababaAttractor.card :=
  distinctFactors_card_le_mul_attractor ababa_isAttractor 3 (by norm_num)

/-- The side condition `1 ≤ k` cannot be dropped: at `k = 0` the empty word is a factor of
`"ababa"` but `0 · |Γ| = 0`. -/
example : ¬ ((distinctFactors ababa 0).card ≤ 0 * ababaAttractor.card) := by
  decide

end SortBounds.Projects.Repetitiveness
