/-
SortBounds/Projects/DeBruijn/AttractorK.lean

**The `k`-attractor hierarchy is unbounded at every level**: for a binary de Bruijn word `B_m` of
order `m ≥ 2` and every `1 ≤ k ≤ m`,

  `2^m / (m · 2^k) ≤ γ(B_m) / γ_k(B_m)`

so no fixed-length attractor approximates `γ` within any constant factor
(`docs/research/gamma-vs-gamma2.md`, "Corollary: every fixed `k` fails").  Lane 1 left the
`k = 2` case at the point where `γ₂ ≤ 4` was a *prose* remark; this file defines `γ_k`, proves
the general statement, and discharges that remark as the `k = 2` instance
(`minAttractorKSize_two_le_four`).

The definitions mirror `Repetitiveness/Attractor.lean` line for line: `IsAttractorK` is
`IsAttractor` with the factor length bounded by `k`, and `minAttractorKSize` is the minimum of
the sizes of the `k`-attractors, taken with `Finset.min'` over the sizes of the filtered
universe (`attractorsK` / `attractorKSizes`), not with a search.

**Two facts place `γ_k` in the hierarchy.**

* `minAttractorKSize_le_minAttractorSize` — `γ_k ≤ γ`: a `k`-attractor has *fewer* obligations
  than an attractor, so every attractor is a `k`-attractor and the minimum over the larger
  family is the smaller one.  (The `README2.md` prose had this direction backwards; the
  inequality it states, `minAttractorKSize s k ≤ minAttractorSize s` for `k ≥ |s|`, is the one
  proved here — in fact for *every* `k`.)
* `minAttractorKSize_le_card_of_extends` — `γ_k ≤ d_k`, **provided** every factor of length
  `≤ k` occurs at a position that still leaves room for a `k`-window.  Mark the *first* position
  of one occurrence of each distinct `k`-gram: a factor `w` of length `ℓ ≤ k` occurs at such a
  `p`, hence is a *prefix* of the `k`-gram of the window at `p`, hence of the chosen occurrence
  of that `k`-gram, whose first position is marked and lies inside the occurrence of `w`.

**Why the side condition, and why the start position.**  Marking "one position inside an
occurrence" is not enough: the factor has to sit at the *left* end of the chosen occurrence for
the mark to lie inside it.  Without the extension hypothesis the bound `γ_k ≤ d_k` is false —
`"ab"` at `k = 2` has `d_2 = 1` but `γ_2 = 2` (`ab_minAttractorKSize_two` below), since no
single position lies in occurrences of both characters.  De Bruijn words satisfy the side
condition for free: pad a factor of length `ℓ ≤ k ≤ m` on the right to an `m`-gram; an
occurrence of that `m`-gram starts at `p` with `p + m ≤ |s|`, so `p + k ≤ p + m ≤ |s|`.  Hence
`γ_k(B_m) ≤ d_k(B_m) = 2^k` (`minAttractorKSize_le_two_pow`), and with lane 1's
`γ(B_m) ≥ 2^m/m` (`gamma_ge_of_isDeBruijn`) that is the separation
(`gamma_ratio_ge_isDeBruijn`).

The side condition `1 ≤ k` in the separation is not removable: `γ_0 = 0` because no factor has
length `≤ 0`, so the right-hand ratio would have denominator `0`
(`minAttractorKSize_zero`).
-/
import Mathlib
import SortBounds.Projects.DeBruijn.DeBruijn

namespace SortBounds.Projects.DeBruijn

open SortBounds.Projects.Repetitiveness

variable {α : Type*} [DecidableEq α]

/-! ### M0: the `k`-attractor and its minimum size -/

/-- `Γ` is a **`k`-attractor** for `s`: every nonempty factor of `s` of length at most `k` has an
occurrence covering a position of `Γ`.  At `k = s.length` the length bound is vacuous and this is
`IsAttractor` (`isAttractorK_self_iff`); at `k = 1` it asks that every occurring character be an
occurring character *at* a position of `Γ` (`isAttractorK_take_one`). -/
def IsAttractorK (s : List α) (k : ℕ) (Γ : Finset (Fin s.length)) : Prop :=
  ∀ i j : ℕ, i < j → j ≤ s.length → j - i ≤ k →
    ∃ i' j' : ℕ, i' ≤ j' ∧ j' ≤ s.length ∧ factorOcc s i' j' = factorOcc s i j ∧
      ∃ p ∈ Γ, i' ≤ (p : ℕ) ∧ (p : ℕ) < j'

omit [DecidableEq α] in
/-- The `k`-attractor condition relaxes as `k` *shrinks*: the same `Γ` covers fewer factors. -/
theorem isAttractorK_of_le {s : List α} {k k' : ℕ} {Γ : Finset (Fin s.length)}
    (h : IsAttractorK s k Γ) (hkk : k' ≤ k) : IsAttractorK s k' Γ :=
  fun i j hij hj hlen => h i j hij hj (Nat.le_trans hlen hkk)

omit [DecidableEq α] in
/-- **Every attractor is a `k`-attractor**: the bounded condition covers only some of the factors
an attractor must cover.  Hence `γ_k ≤ γ`. -/
theorem isAttractorK_of_isAttractor {s : List α} {Γ : Finset (Fin s.length)}
    (h : IsAttractor s Γ) (k : ℕ) : IsAttractorK s k Γ :=
  fun i j hij hj _ => h i j hij hj

omit [DecidableEq α] in
/-- The full position set is always a `k`-attractor, so `γ_k` is always defined. -/
theorem isAttractorK_univ (s : List α) (k : ℕ) : IsAttractorK s k Finset.univ :=
  fun i j hij hj _ =>
    ⟨i, j, le_of_lt hij, hj, rfl, ⟨⟨i, by omega⟩, Finset.mem_univ _, le_rfl, hij⟩⟩

omit [DecidableEq α] in
/-- **`IsAttractorK` is a finite check**, exactly as `isAttractor_iff_check` is: rewriting the
quantifiers over factors and over the covering occurrence as `Fin (s.length + 1)`, a concrete
instance can be certified by `decide`. -/
theorem isAttractorK_iff_check {s : List α} (k : ℕ) (Γ : Finset (Fin s.length)) :
    IsAttractorK s k Γ ↔
      ∀ (ii jj : Fin (s.length + 1)), (ii : ℕ) < (jj : ℕ) → (jj : ℕ) ≤ s.length →
        (jj : ℕ) - (ii : ℕ) ≤ k →
        ∃ i' j' : Fin (s.length + 1), (i' : ℕ) ≤ (j' : ℕ) ∧ (j' : ℕ) ≤ s.length ∧
          factorOcc s (i' : ℕ) (j' : ℕ) = factorOcc s (ii : ℕ) (jj : ℕ) ∧
          ∃ p ∈ Γ, (i' : ℕ) ≤ (p : ℕ) ∧ (p : ℕ) < (j' : ℕ) := by
  constructor
  · intro h ii jj hij hj hlen
    obtain ⟨i', j', h1, h2, h3, p, hp, h4, h5⟩ := h ii.val jj.val hij hj hlen
    exact ⟨⟨i', by omega⟩, ⟨j', by omega⟩, h1, h2, h3, p, hp, h4, h5⟩
  · intro h i j hij hj hlen
    obtain ⟨i', j', h1, h2, h3, p, hp, h4, h5⟩ :=
      h ⟨i, by omega⟩ ⟨j, by omega⟩ (by simpa using hij) hj (by simpa using hlen)
    exact ⟨i'.val, j'.val, h1, h2, h3, p, hp, h4, h5⟩

omit [DecidableEq α] in
/-- **A length-1 factor is covered at its own position**: the covering occurrence has length `1`,
so the attractor position inside it *is* the factor's position.  Hence a `k`-attractor with
`k ≥ 1` contains a position carrying every occurring character — the bounded condition is still
not the trivial "every factor occurs somewhere".  (The `IsAttractor` version is
`isAttractor_take_one`.) -/
theorem isAttractorK_take_one {s : List α} {k : ℕ} {Γ : Finset (Fin s.length)}
    (hΓ : IsAttractorK s k Γ) (hk : 1 ≤ k) {i : ℕ} (hi : i < s.length) :
    ∃ p ∈ Γ, (s.drop (p : ℕ)).take 1 = (s.drop i).take 1 := by
  obtain ⟨i', j', -, hj', heq, p, hp, h1, h2⟩ := hΓ i (i + 1) (by omega) (by omega) (by omega)
  have hlen1 : (factorOcc s i' j').length = j' - i' := factorOcc_length hj'
  have hlen2 : (factorOcc s i (i + 1)).length = 1 := by
    rw [factorOcc_self, List.length_take, List.length_drop]
    omega
  rw [heq, hlen2] at hlen1
  have hpi : (p : ℕ) = i' := by omega
  have hleft : (s.drop i').take 1 = factorOcc s i' j' := by rw [factorOcc, ← hlen1]
  have hright : (s.drop i).take 1 = factorOcc s i (i + 1) := by rw [factorOcc_self]
  exact ⟨p, hp, by rw [hpi, hleft, hright, heq]⟩

/-- The `k`-attractors of `s`, as a finite set of position sets. -/
noncomputable def attractorsK (s : List α) (k : ℕ) : Finset (Finset (Fin s.length)) := by
  classical
  exact Finset.univ.filter (fun Γ => IsAttractorK s k Γ)

omit [DecidableEq α] in
theorem mem_attractorsK {s : List α} {k : ℕ} {Γ : Finset (Fin s.length)} :
    Γ ∈ attractorsK s k ↔ IsAttractorK s k Γ := by
  classical
  simp [attractorsK]

omit [DecidableEq α] in
theorem attractorsK_nonempty (s : List α) (k : ℕ) : (attractorsK s k).Nonempty := by
  classical
  exact ⟨Finset.univ, by simp [mem_attractorsK, isAttractorK_univ]⟩

omit [DecidableEq α] in
/-- The sizes of the `k`-attractors of `s`. -/
noncomputable def attractorKSizes (s : List α) (k : ℕ) : Finset ℕ :=
  (attractorsK s k).image Finset.card

omit [DecidableEq α] in
theorem attractorKSizes_nonempty (s : List α) (k : ℕ) : (attractorKSizes s k).Nonempty := by
  obtain ⟨Γ, hΓ⟩ := attractorsK_nonempty s k
  exact ⟨Γ.card, Finset.mem_image.mpr ⟨Γ, hΓ, rfl⟩⟩

omit [DecidableEq α] in
/-- The smallest size of a `k`-attractor of `s`, the `γ_k` of the `k`-attractor hierarchy.
Well defined because the full position set is a `k`-attractor (`isAttractorK_univ`). -/
noncomputable def minAttractorKSize (s : List α) (k : ℕ) : ℕ :=
  (attractorKSizes s k).min' (attractorKSizes_nonempty s k)

omit [DecidableEq α] in
/-- A minimal `k`-attractor: some `k`-attractor realises `minAttractorKSize`. -/
theorem exists_attractorK_card_eq_minAttractorKSize (s : List α) (k : ℕ) :
    ∃ Γ : Finset (Fin s.length), IsAttractorK s k Γ ∧ Γ.card = minAttractorKSize s k := by
  classical
  obtain ⟨Γ, hΓ, hcard⟩ := Finset.mem_image.mp (Finset.min'_mem (attractorKSizes s k) _)
  exact ⟨Γ, mem_attractorsK.mp hΓ, hcard⟩

omit [DecidableEq α] in
/-- `minAttractorKSize s k` is a lower bound for the size of every `k`-attractor. -/
theorem minAttractorKSize_le {s : List α} {k : ℕ} {Γ : Finset (Fin s.length)}
    (hΓ : IsAttractorK s k Γ) : minAttractorKSize s k ≤ Γ.card := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨Γ, mem_attractorsK.mpr hΓ, rfl⟩)

/-! ### M1: the bounded hierarchy starts at the full one -/

omit [DecidableEq α] in
/-- **Sanity**: at `k = s.length` the length bound is vacuous, so a `k`-attractor is exactly an
attractor — `γ_{|s|} = γ`, and the definition of `γ_k` extends `γ` rather than replacing it. -/
theorem isAttractorK_self_iff (s : List α) (Γ : Finset (Fin s.length)) :
    IsAttractorK s s.length Γ ↔ IsAttractor s Γ := by
  constructor
  · intro h i j hij hj
    exact h i j hij hj (by omega)
  · intro h i j hij hj _
    exact h i j hij hj

omit [DecidableEq α] in
/-- **`γ_k ≤ γ`** — and not merely for `k ≥ s.length`: the `k`-attractor condition is implied by
the attractor condition for every `k`, so the `k`-attractor family is the larger one. -/
theorem minAttractorKSize_le_minAttractorSize (s : List α) (k : ℕ) :
    minAttractorKSize s k ≤ minAttractorSize s := by
  obtain ⟨Γ, hΓ, hcard⟩ := exists_attractor_card_eq_minAttractorSize s
  rw [← hcard]
  exact minAttractorKSize_le (isAttractorK_of_isAttractor hΓ k)

omit [DecidableEq α] in
/-- **`γ_k` is nonincreasing in `k`**: a smaller length bound is a weaker requirement, so the
minimum is at most that for a larger bound — with `minAttractorKSize_le_minAttractorSize` this
gives `γ_{|s|} = γ ≤ γ_k` for every `k`. -/
theorem minAttractorKSize_anti {s : List α} {k k' : ℕ} (hkk : k' ≤ k) :
    minAttractorKSize s k' ≤ minAttractorKSize s k := by
  obtain ⟨Γ, hΓ, hcard⟩ := exists_attractorK_card_eq_minAttractorKSize s k
  rw [← hcard]
  exact minAttractorKSize_le (isAttractorK_of_le hΓ hkk)

omit [DecidableEq α] in
/-- At `k = 0` there is no factor of length `≤ 0`, so the empty set is a `0`-attractor and
`γ_0 = 0`.  This is why the separation needs the side condition `1 ≤ k`: its right-hand side
would have denominator `0`. -/
theorem minAttractorKSize_zero (s : List α) : minAttractorKSize s 0 = 0 := by
  have hempty : IsAttractorK s 0 (∅ : Finset (Fin s.length)) := by
    intro i j hij _ hlen
    omega
  refine le_antisymm ?_ (Nat.zero_le _)
  calc minAttractorKSize s 0 ≤ (∅ : Finset (Fin s.length)).card := minAttractorKSize_le hempty
    _ = 0 := Finset.card_empty

omit [DecidableEq α] in
/-- `γ_k ≥ 1` whenever there is a position to cover: the empty position set is not a
`k`-attractor for `k ≥ 1` on a nonempty word, because the character at position `0` needs a
covering occurrence and every occurrence is nonempty.  (Needed to divide by `γ_k`.) -/
theorem one_le_minAttractorKSize {s : List α} {k : ℕ} (hs : 1 ≤ s.length) (hk : 1 ≤ k) :
    1 ≤ minAttractorKSize s k := by
  obtain ⟨Γ, hΓ, hcard⟩ := exists_attractorK_card_eq_minAttractorKSize s k
  rw [← hcard]
  rcases Finset.eq_empty_or_nonempty Γ with hemp | ⟨p, hp⟩
  · exfalso
    obtain ⟨-, -, -, -, -, q, hq, -⟩ := hΓ 0 1 (by omega) hs (by omega)
    rw [hemp] at hq
    exact absurd hq (by simp)
  · have hpos : 0 < Γ.card := Finset.card_pos.mpr ⟨p, hp⟩
    omega

/-! ### M2: the counting bound `γ_k ≤ d_k`

The load-bearing construction of the file: mark the first position of one occurrence of each
distinct `k`-gram.  It is the formal form of the research note's "choose one position inside an
occurrence of each distinct `k`-gram", and it needs the factor to be a *prefix* of an occurring
`k`-gram, which is the hypothesis `hext`. -/

/-- **`γ_k ≤ d_k` when every factor of length `≤ k` occurs at a position that leaves room for a
`k`-window.**  For each distinct `k`-gram `f` choose one occurrence and mark its first position
(`start f`); there are at most `d_k` marks.  A factor `w` of length `j - i ≤ k` occurs at a
position `p` with `p + k ≤ s.length` (hypothesis), so `w` is a prefix of the `k`-gram `f` of the
window at `p`; the chosen occurrence of `f` starts at `start f`, so `w` occurs there as a prefix
too and its occurrence contains the mark `start f`. -/
theorem minAttractorKSize_le_card_of_extends {s : List α} {k : ℕ} (hk : 1 ≤ k)
    (hext : ∀ ℓ, ℓ ≤ k → ∀ f : List α, f ∈ distinctFactors s ℓ →
      ∃ p : ℕ, p + k ≤ s.length ∧ (s.drop p).take ℓ = f) :
    minAttractorKSize s k ≤ (distinctFactors s k).card := by
  classical
  -- the chosen occurrence of a `k`-gram
  let start : List α → ℕ := fun f =>
    if h : ∃ p : ℕ, p + k ≤ s.length ∧ (s.drop p).take k = f then Classical.choose h else 0
  have hstart_spec : ∀ f ∈ distinctFactors s k,
      start f + k ≤ s.length ∧ (s.drop (start f)).take k = f := by
    intro f hf
    have hex : ∃ p : ℕ, p + k ≤ s.length ∧ (s.drop p).take k = f :=
      mem_distinctFactors.mp hf
    have hval : start f = Classical.choose hex := by
      dsimp only [start]
      exact dite_eq_left hex
    rw [hval]
    exact Classical.choose_spec hex
  -- one marked position per distinct `k`-gram
  let Γ : Finset (Fin s.length) := (distinctFactors s k).attach.image (fun f =>
    (⟨start f.1, by have h := (hstart_spec f.1 f.2).1; omega⟩ : Fin s.length))
  have hΓcard : Γ.card ≤ (distinctFactors s k).card := by
    calc Γ.card ≤ (distinctFactors s k).attach.card := Finset.card_image_le
      _ = (distinctFactors s k).card := Finset.card_attach
  refine le_trans (minAttractorKSize_le (Γ := Γ) ?_) hΓcard
  intro i j hij hj hlen
  -- the factor under consideration
  have hmem : factorOcc s i j ∈ distinctFactors s (j - i) := by
    refine mem_distinctFactors.mpr ⟨i, by omega, ?_⟩
    rw [← factorOcc_self, show i + (j - i) = j by omega]
  obtain ⟨p, hpk, hp⟩ := hext (j - i) hlen (factorOcc s i j) hmem
  -- the `k`-gram of the window at `p`, and the chosen occurrence of it
  set f : List α := (s.drop p).take k with hf
  have hfw : f ∈ distinctFactors s k := mem_distinctFactors.mpr ⟨p, hpk, rfl⟩
  obtain ⟨hfk, hff⟩ := hstart_spec f hfw
  have hmark : (⟨start f, by omega⟩ : Fin s.length) ∈ Γ := by
    refine Finset.mem_image.mpr ⟨⟨f, hfw⟩, Finset.mem_attach _ _, ?_⟩
    rfl
  -- `w` is a prefix of the chosen occurrence of `f`, which starts at the mark
  have htake : (s.drop (start f)).take (j - i) = factorOcc s i j := by
    have h2 : (s.drop (start f)).take (j - i) = f.take (j - i) := by
      conv_rhs => rw [← hff]
      rw [List.take_take, min_eq_left hlen]
    have h3 : f.take (j - i) = factorOcc s i j := by
      rw [hf, List.take_take, min_eq_left hlen, hp]
    rw [h2, h3]
  have hocc : factorOcc s (start f) (start f + (j - i)) = factorOcc s i j := by
    rw [factorOcc_self]
    exact htake
  refine ⟨start f, start f + (j - i), by omega, by omega, hocc, ?_⟩
  refine ⟨⟨start f, by omega⟩, hmark, le_rfl, ?_⟩
  show start f < start f + (j - i)
  omega

/-! ### The extension hypothesis of M2 cannot be dropped: `γ_2("ab") = 2 > d_2 = 1` -/

/-- The counterexample word `"ab"`. -/
def ab : List Char := ['a', 'b']

/-- The two positions of `"ab"` are a `2`-attractor (it has no factor of length `> 2`). -/
theorem ab_isAttractorK_two : IsAttractorK ab 2 {⟨0, by decide⟩, ⟨1, by decide⟩} := by
  rw [isAttractorK_iff_check]
  decide

/-- `d_2("ab") = 1`: there is a single distinct `2`-gram. -/
theorem ab_card_distinctFactors_two : (distinctFactors ab 2).card = 1 := by
  decide

/-- **`γ_k ≤ d_k` fails without the extension hypothesis of `minAttractorKSize_le_card_of_extends`**:
each of the two characters of `"ab"` forces its own position (`isAttractorK_take_one`), so
`γ_2("ab") = 2`, while `d_2("ab") = 1`.  The marks must sit at the *start* of a `k`-gram
occurrence — for `"ab"` the only `2`-gram is `"ab"`, whose start `0` is not inside the occurrence
`[1, 2)` of `"b"`. -/
theorem ab_minAttractorKSize_two : minAttractorKSize ab 2 = 2 := by
  refine le_antisymm ?_ ?_
  · calc minAttractorKSize ab 2 ≤ ({⟨0, by decide⟩, ⟨1, by decide⟩} : Finset (Fin ab.length)).card :=
          minAttractorKSize_le ab_isAttractorK_two
      _ = 2 := by decide
  · obtain ⟨Γ, hΓ, hcard⟩ := exists_attractorK_card_eq_minAttractorKSize ab 2
    rw [← hcard]
    obtain ⟨p, hp, hp'⟩ := isAttractorK_take_one hΓ (by norm_num : 1 ≤ 2) (i := 0) (by decide)
    obtain ⟨q, hq, hq'⟩ := isAttractorK_take_one hΓ (by norm_num : 1 ≤ 2) (i := 1) (by decide)
    have hpq : p ≠ q := by
      intro hpq
      rw [← hpq, hp'] at hq'
      exact absurd hq' (by decide)
    have hsub : ({p, q} : Finset (Fin ab.length)) ⊆ Γ := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact hq
    calc 2 = ({p, q} : Finset (Fin ab.length)).card := by simp [hpq]
      _ ≤ Γ.card := Finset.card_le_card hsub

/-! ### M2 for de Bruijn words: `γ_k ≤ 2^k` -/

/-- **`γ_k(B_m) ≤ d_k(B_m) = 2^k`** for a binary de Bruijn word of order `m ≥ k ≥ 1`.  The side
condition of `minAttractorKSize_le_card_of_extends` holds here: pad a factor of length `ℓ ≤ k` on
the right to an `m`-gram; an occurrence of that `m`-gram starts at `p` with `p + m ≤ s.length`,
and `k ≤ m` gives `p + k ≤ s.length`.  This is the `γ_k ≤ d_k` step of the research note, made
precise. -/
theorem minAttractorKSize_le_two_pow {s : List Bool} {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (h : IsDeBruijn s m) : minAttractorKSize s k ≤ 2 ^ k := by
  obtain ⟨hlen, hcov⟩ := h
  have hext : ∀ ℓ, ℓ ≤ k → ∀ f : List Bool, f ∈ distinctFactors s ℓ →
      ∃ p : ℕ, p + k ≤ s.length ∧ (s.drop p).take ℓ = f := by
    intro ℓ hℓk f hf
    obtain ⟨i, hi, hif⟩ := mem_distinctFactors.mp hf
    have hflen : f.length = ℓ := by
      rw [← hif, List.length_take, List.length_drop]
      omega
    -- pad the factor on the right to an `m`-gram
    set g : List Bool := f ++ List.replicate (m - ℓ) false with hg
    have hglen : g.length = m := by
      simp only [hg, List.length_append, List.length_replicate, hflen]
      omega
    obtain ⟨p, hpm, hpg⟩ := mem_distinctFactors.mp (hcov g hglen)
    refine ⟨p, by omega, ?_⟩
    calc (s.drop p).take ℓ = ((s.drop p).take m).take ℓ := by
          rw [List.take_take, min_eq_left (by omega)]
      _ = g.take ℓ := by rw [hpg]
      _ = f := by rw [hg, ← hflen, List.take_left]
  calc minAttractorKSize s k ≤ (distinctFactors s k).card :=
        minAttractorKSize_le_card_of_extends hk hext
    _ = 2 ^ k := card_distinctFactors_of_coversAllWords (coversAllWords_mono hcov hkm)

/-- Lane 1's prose remark `γ₂(B_m) ≤ 4` is the `k = 2` instance of
`minAttractorKSize_le_two_pow`; with `gamma_ge_of_isDeBruijn` it is the `k = 2` case of the
separation. -/
theorem minAttractorKSize_two_le_four {s : List Bool} {m : ℕ} (hm : 2 ≤ m) (h : IsDeBruijn s m) :
    minAttractorKSize s 2 ≤ 4 := by
  have h2 := minAttractorKSize_le_two_pow (s := s) (m := m) (k := 2) (by norm_num) hm h
  simpa using h2

/-! ### M3: the separation `2^m/(m·2^k) ≤ γ/γ_k` -/

/-! ### The lower bound `d_k / k ≤ γ_k`, dual to `γ_k ≤ d_k` -/

/-- A `k`-attractor covers every factor of length `k`, so the cover argument of
`Repetitiveness.exists_cover_of_isAttractor` applies verbatim: main content of the lower bound. -/
theorem exists_cover_of_isAttractorK {s : List α} {Γ : Finset (Fin s.length)} {k : ℕ}
    (hΓ : IsAttractorK s k Γ) (hk : 1 ≤ k) {f : List α} (hf : f ∈ distinctFactors s k) :
    ∃ (p : Fin s.length) (d : ℕ), p ∈ Γ ∧ d < k ∧ (s.drop ((p : ℕ) - d)).take k = f := by
  obtain ⟨i, hik, hf'⟩ := mem_distinctFactors.mp hf
  obtain ⟨i', j', -, hj', heq, p, hp, h1, h2⟩ :=
    hΓ i (i + k) (by omega) hik (by omega)
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

/-- **`d_k ≤ k · γ_k`**: a position of a `k`-attractor lies in at most `k` windows of length
`k`, hence covers at most `k` distinct `k`-grams. -/
theorem distinctFactors_card_le_mul_attractorK {s : List α} {Γ : Finset (Fin s.length)} {k : ℕ}
    (hΓ : IsAttractorK s k Γ) (hk : 1 ≤ k) :
    (distinctFactors s k).card ≤ k * Γ.card := by
  classical
  set D : Finset (Fin s.length × ℕ) := Γ.product (Finset.range k) with hD
  have hDcard : D.card = Γ.card * k := by simp [hD]
  have hsub : distinctFactors s k ⊆
      D.image (fun x : Fin s.length × ℕ => (s.drop ((x.1 : ℕ) - x.2)).take k) := by
    intro f hf
    obtain ⟨p, d, hp, hdk, hfd⟩ := exists_cover_of_isAttractorK hΓ hk hf
    exact Finset.mem_image.mpr
      ⟨(p, d), Finset.mem_product.mpr ⟨hp, Finset.mem_range.mpr hdk⟩, hfd⟩
  calc (distinctFactors s k).card
      ≤ (D.image (fun x : Fin s.length × ℕ => (s.drop ((x.1 : ℕ) - x.2)).take k)).card :=
        Finset.card_le_card hsub
    _ ≤ D.card := Finset.card_image_le
    _ = Γ.card * k := hDcard
    _ = k * Γ.card := Nat.mul_comm _ _

/-- **`d_k / k ≤ γ_k`**: the `k`-truncated form of KNP's `δ ≤ γ`, against the minimum. -/
theorem dk_div_le_minAttractorKSize {s : List α} {k : ℕ} (hk : 1 ≤ k) :
    (distinctFactors s k).card / k ≤ minAttractorKSize s k := by
  obtain ⟨Γ, hΓ, hcard⟩ := exists_attractorK_card_eq_minAttractorKSize s k
  rw [← hcard]
  exact Nat.div_le_of_le_mul (distinctFactors_card_le_mul_attractorK hΓ hk)

/-- **On de Bruijn words `γ_k = Θ(2^k / k)`**: `2^k/k ≤ γ_k(B_m) ≤ 2^k` for `1 ≤ k ≤ m`.  With
lane 1 this pins all three levels at once — `γ ≥ 2^m/m`, `γ_k ≥ 2^k/k`, `γ_k ≤ 2^k` — so the
hierarchy is exponential at every level while its ratios are unbounded (`gamma_ratio_ge_isDeBruijn`). -/
theorem minAttractorKSize_bracket_isDeBruijn {s : List Bool} {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (h : IsDeBruijn s m) :
    (distinctFactors s k).card / k ≤ minAttractorKSize s k ∧
      minAttractorKSize s k ≤ 2 ^ k :=
  ⟨dk_div_le_minAttractorKSize hk, minAttractorKSize_le_two_pow hk hkm h⟩

/-- **The general separation for binary de Bruijn words.**  `γ(B_m) ≥ 2^m/m` is lane 1's
`gamma_ge_of_isDeBruijn` (`δ ≤ γ` at `δ(B_m) = 2^m/m`) and `γ_k(B_m) ≤ 2^k` is
`minAttractorKSize_le_two_pow`, so dividing gives `γ/γ_k ≥ 2^m/(m·2^k)`.  For fixed `k` the
lower bound `2^m/(m·2^k)` is unbounded in `m`, hence so is `γ/γ_k`: no bounded-length attractor
`γ_k` is a constant-factor approximation of `γ`. -/
theorem gamma_ratio_ge_isDeBruijn {s : List Bool} {k m : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hkm : k ≤ m) (h : IsDeBruijn s m) :
    (2 ^ m : ℚ) / (m * 2 ^ k) ≤ (minAttractorSize s : ℚ) / (minAttractorKSize s k : ℚ) := by
  obtain ⟨hlen, hcov⟩ := h
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hγ : (2 ^ m : ℚ) / m ≤ (minAttractorSize s : ℚ) :=
    gamma_ge_of_isDeBruijn hm ⟨hlen, hcov⟩
  have hγk : (minAttractorKSize s k : ℚ) ≤ (2 : ℚ) ^ k := by
    have h' : minAttractorKSize s k ≤ 2 ^ k := minAttractorKSize_le_two_pow hk hkm ⟨hlen, hcov⟩
    exact_mod_cast h'
  have hγkpos : (0 : ℚ) < (minAttractorKSize s k : ℚ) := by
    have h1 : (1 : ℚ) ≤ (minAttractorKSize s k : ℚ) := by
      have hs : 1 ≤ s.length := by
        rw [hlen]
        have := Nat.one_le_two_pow (n := m)
        omega
      exact_mod_cast one_le_minAttractorKSize hs hk
    linarith
  have hden : (0 : ℚ) < (m : ℚ) * (2 : ℚ) ^ k := mul_pos hmpos (by positivity)
  rw [div_le_div_iff₀ hden hγkpos]
  have hγ' : (2 : ℚ) ^ m ≤ (minAttractorSize s : ℚ) * m := by
    rw [div_le_iff₀ hmpos] at hγ
    exact hγ
  calc (2 : ℚ) ^ m * (minAttractorKSize s k : ℚ)
      ≤ ((minAttractorSize s : ℚ) * m) * (2 : ℚ) ^ k :=
        mul_le_mul hγ' hγk (le_of_lt hγkpos) (by positivity)
    _ = (minAttractorSize s : ℚ) * (m * 2 ^ k) := by ring

/-! ### M4: the bound at the lane-1 witnesses -/

/-- The order-`3` de Bruijn witness of lane 1 (`0001011100`), named for the checks below. -/
def dB3 : List Bool := [false, false, false, true, false, true, true, true, false, false]

theorem isDeBruijn_dB3 : IsDeBruijn dB3 3 := isDeBruijn_three

/-- Positions `0`, `3`, `5` of `0001011100` are a `2`-attractor: `0` covers `0` and `00`, `3`
covers `1`, `01` and `10`, `5` covers `11`.  Three positions, and `2^2 = 4`. -/
def dB3AttractorK2 : Finset (Fin dB3.length) :=
  {⟨0, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩}

theorem dB3AttractorK2_card : dB3AttractorK2.card = 3 := by decide

theorem isAttractorK_dB3_two : IsAttractorK dB3 2 dB3AttractorK2 := by
  rw [isAttractorK_iff_check]
  decide

/-- `γ_2(0001011100) ≤ 3 ≤ 4 = 2^2`: the explicit `2`-attractor meets the counting bound. -/
theorem minAttractorKSize_dB3_two : minAttractorKSize dB3 2 ≤ 2 ^ 2 := by
  calc minAttractorKSize dB3 2 ≤ dB3AttractorK2.card := minAttractorKSize_le isAttractorK_dB3_two
    _ = 3 := dB3AttractorK2_card
    _ ≤ 2 ^ 2 := by norm_num

/-- The separation at `m = 3`, `k = 2`: `2^3/(3·2^2) = 2/3 ≤ γ/γ_2` for `0001011100`. -/
theorem gamma_ratio_isDeBruijn_three_two :
    (2 ^ 3 : ℚ) / (3 * 2 ^ 2) ≤ (minAttractorSize dB3 : ℚ) / (minAttractorKSize dB3 2 : ℚ) :=
  gamma_ratio_ge_isDeBruijn (by norm_num) (by norm_num) (by norm_num) isDeBruijn_dB3

example : (2 ^ 3 : ℚ) / (3 * 2 ^ 2) = 2 / 3 := by norm_num

/-- A single position is not a `2`-attractor of `0001011100`: position `0` misses the factor
`1`, which only occurs at positions `3`, `5`, `6`, `7`. -/
example : ¬ IsAttractorK dB3 2 {⟨0, by decide⟩} := by
  rw [isAttractorK_iff_check]
  decide

/-- The `k = |s|` instance of the hierarchy on the witness, from `isAttractorK_self_iff`. -/
example : IsAttractorK dB3 dB3.length dB3AttractorK2 ↔ IsAttractor dB3 dB3AttractorK2 :=
  isAttractorK_self_iff dB3 dB3AttractorK2

/-- `γ_0 = 0`: the side condition `1 ≤ k` of the separation is not removable. -/
example : minAttractorKSize dB3 0 = 0 := minAttractorKSize_zero dB3

end SortBounds.Projects.DeBruijn
