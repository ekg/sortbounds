/-
SortBounds/Projects/Repetitiveness/Basic.lean

**String attractors and the distinct-factor count `d_k`, the two definitions the
counting core of the attractor hierarchy is built from** (Kempa–Prezza, STOC'18,
doi:10.1145/3188745.3188814; Kempa–Kociumaka–Prezza, Lemma II.4).

* `factorOcc s i j` is the window `s[i..j)`, the factor delimited by the positions `i ≤ j`;
* `distinctFactors s k` is the *set* of distinct length-`k` factors of `s` — a `Finset`,
  so occurrences are quotiented away and `d_k` is a number of distinct words, not of
  positions;
* `IsAttractor s Γ` says: every nonempty factor of `s` has an occurrence whose interval
  meets `Γ` (the condition of Kempa–Prezza, verbatim "every substring `T[i..j]` has an
  occurrence `T[i'..j'] = T[i..j]` with `j_k ∈ [i', j']` for some `j_k ∈ Γ`).

Two sanity checks on the definitions live here, because a definition that is
unsatisfiable, or one that makes the counting lemma trivial, is the failure mode of a
lane like this one:

* `isAttractor_univ` — *every* string has an attractor (the full position set), so `γ` is
  always defined; and `ababa_isAttractor` — `"ababa"` has an attractor of size `2`, so the
  interesting case is not vacuous;
* `isAttractor_take_one` — the condition is genuinely strong: a length-1 factor can only
  be covered by an occurrence *at* an attractor position, so `{0}` is **not** an attractor
  of `"ababa"` (`not_isAttractor_singleton`). The trivial "every factor occurs somewhere"
  reading of attractor would accept `{0}`.  `card_distinctFactors_pos` keeps `d_k` from
  being degenerate: `k ≤ n` means some length-`k` factor exists.
-/
import Mathlib

namespace SortBounds.Projects.Repetitiveness

variable {α : Type*}

/-- The factor `s[i..j)` of `s`: the window of length `j - i` starting at `i`.  For
`j ≤ s.length` this is literally the substring `s[i..j]` of the literature. -/
def factorOcc (s : List α) (i j : ℕ) : List α := (s.drop i).take (j - i)

@[simp]
theorem factorOcc_self (s : List α) (i k : ℕ) : factorOcc s i (i + k) = (s.drop i).take k := by
  simp [factorOcc]

theorem factorOcc_length {s : List α} {i j : ℕ} (hj : j ≤ s.length) :
    (factorOcc s i j).length = j - i := by
  have : j - i ≤ s.length - i := by omega
  simp [factorOcc, this]

variable [DecidableEq α]

/-- The number of distinct length-`k` factors of `s`, as a `Finset` of words: only starts
`i` with `i + k ≤ s.length` contribute, so `distinctFactors s k` is empty when `k >
s.length` and `distinctFactors s 0 = {[]}`.  This is KNP's `d_k`. -/
noncomputable def distinctFactors (s : List α) (k : ℕ) : Finset (List α) :=
  ((Finset.range (s.length + 1)).filter (fun i => i + k ≤ s.length)).image
    (fun i => (s.drop i).take k)

theorem mem_distinctFactors {s : List α} {k : ℕ} {f : List α} :
    f ∈ distinctFactors s k ↔ ∃ i, i + k ≤ s.length ∧ (s.drop i).take k = f := by
  simp only [distinctFactors, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨i, ⟨-, hik⟩, hf⟩
    exact ⟨i, hik, hf⟩
  · rintro ⟨i, hik, hf⟩
    exact ⟨i, ⟨by omega, hik⟩, hf⟩

/-- `d_k ≥ 1` whenever `k ≤ s.length`: the window at position `0` is a length-`k` factor. -/
theorem card_distinctFactors_pos {s : List α} {k : ℕ} (hk : k ≤ s.length) :
    0 < (distinctFactors s k).card := by
  have h : (s.drop 0).take k ∈ distinctFactors s k := by
    rw [mem_distinctFactors]
    exact ⟨0, by simpa using hk, by simp⟩
  exact Finset.card_pos.mpr ⟨_, h⟩

/-- `Γ` is a **string attractor** for `s`: every nonempty factor `s[i..j)` occurs again at
some `s[i'..j')` with the same content and with an attractor position inside `[i', j')`. -/
def IsAttractor (s : List α) (Γ : Finset (Fin s.length)) : Prop :=
  ∀ i j : ℕ, i < j → j ≤ s.length →
    ∃ i' j' : ℕ, i' ≤ j' ∧ j' ≤ s.length ∧ factorOcc s i' j' = factorOcc s i j ∧
      ∃ p ∈ Γ, i' ≤ (p : ℕ) ∧ (p : ℕ) < j'

omit [DecidableEq α] in
/-- The full position set is always an attractor, so every string has one. -/
theorem isAttractor_univ (s : List α) : IsAttractor s Finset.univ := by
  intro i j hij hj
  exact ⟨i, j, le_of_lt hij, hj, rfl, ⟨⟨i, by omega⟩, Finset.mem_univ _, le_rfl, hij⟩⟩

omit [DecidableEq α] in
/-- **A length-1 factor is only covered by an occurrence at the attractor position**: the
window `[i', j')` containing `p` is a single position, so `p = i'`.  Hence every distinct
character of `s` appears at some position of `Γ` — the condition is not the trivial
"every factor occurs somewhere". -/
theorem isAttractor_take_one {s : List α} {Γ : Finset (Fin s.length)} (hΓ : IsAttractor s Γ)
    {i : ℕ} (hi : i < s.length) :
    ∃ p ∈ Γ, (s.drop (p : ℕ)).take 1 = (s.drop i).take 1 := by
  obtain ⟨i', j', hi', hj', heq, p, hp, h1, h2⟩ := hΓ i (i + 1) (by omega) (by omega)
  have hlen1 : (factorOcc s i' j').length = j' - i' := factorOcc_length hj'
  have hlen2 : (factorOcc s i (i + 1)).length = 1 := by
    rw [factorOcc_self, List.length_take, List.length_drop]
    omega
  rw [heq, hlen2] at hlen1
  have hpi : (p : ℕ) = i' := by omega
  have hleft : (s.drop i').take 1 = factorOcc s i' j' := by
    rw [factorOcc, ← hlen1]
  have hright : (s.drop i).take 1 = factorOcc s i (i + 1) := by
    rw [factorOcc_self]
  refine ⟨p, hp, ?_⟩
  rw [hpi, hleft, hright, heq]

omit [DecidableEq α] in
/-- **`IsAttractor` is a finite check.**  Rewriting the quantifiers over factors and over
the covering occurrence as `Fin (s.length + 1)`, a concrete instance can be certified by
`decide`.  (Used for the sanity checks below; it is also the reason the definition is not
hiding an infinite search.) -/
theorem isAttractor_iff_check {s : List α} (Γ : Finset (Fin s.length)) :
    IsAttractor s Γ ↔
      ∀ (ii jj : Fin (s.length + 1)), (ii : ℕ) < (jj : ℕ) → (jj : ℕ) ≤ s.length →
        ∃ i' j' : Fin (s.length + 1), (i' : ℕ) ≤ (j' : ℕ) ∧ (j' : ℕ) ≤ s.length ∧
          factorOcc s (i' : ℕ) (j' : ℕ) = factorOcc s (ii : ℕ) (jj : ℕ) ∧
          ∃ p ∈ Γ, (i' : ℕ) ≤ (p : ℕ) ∧ (p : ℕ) < (j' : ℕ) := by
  constructor
  · intro h ii jj hij hj
    obtain ⟨i', j', h1, h2, h3, p, hp, h4, h5⟩ := h ii.val jj.val hij hj
    exact ⟨⟨i', by omega⟩, ⟨j', by omega⟩, h1, h2, h3, p, hp, h4, h5⟩
  · intro h i j hij hj
    obtain ⟨i', j', h1, h2, h3, p, hp, h4, h5⟩ :=
      h ⟨i, by omega⟩ ⟨j, by omega⟩ (by simpa using hij) hj
    exact ⟨i'.val, j'.val, h1, h2, h3, p, hp, h4, h5⟩

/-! ### Sanity checks on the definitions -/

/-- The running example of the lane: `ababa`. -/
def ababa : List Char := ['a', 'b', 'a', 'b', 'a']

/-- `d_k` is a count of *distinct* words: `"ababa"` has two distinct characters and two
distinct factors of every length `1 ≤ k ≤ 4` (it is a prefix of the infinite `ababab…`),
and the whole word once. -/
example : (distinctFactors ababa 0).card = 1 := by decide
example : (distinctFactors ababa 1).card = 2 := by decide
example : (distinctFactors ababa 2).card = 2 := by decide
example : (distinctFactors ababa 4).card = 2 := by decide
example : (distinctFactors ababa 5).card = 1 := by decide
example : (distinctFactors ababa 6).card = 0 := by decide

/-- The empty string has the empty attractor (there is no nonempty factor to cover). -/
example : IsAttractor ([] : List Char) (∅ : Finset (Fin 0)) := by
  rw [isAttractor_iff_check]
  decide

/-- The two positions `0` and `1` of `"ababa"`, as candidate attractor positions. -/
def ababaAttractor : Finset (Fin ababa.length) := {⟨0, by decide⟩, ⟨1, by decide⟩}

theorem ababaAttractor_card : ababaAttractor.card = 2 := by decide

/-- **A nontrivial attractor**: positions `0` and `1` hit every factor of `"ababa"`
(`a` is at `0`, `b` at `1`, and every longer factor of this word starts at `0` or `1`). -/
theorem ababa_isAttractor : IsAttractor ababa ababaAttractor := by
  rw [isAttractor_iff_check]
  decide

/-- **`{0}` is not an attractor of `"ababa"`**: the factor `b` at position `1` occurs
nowhere covering position `0`.  This is what rules out reading `IsAttractor` as the
trivial "every factor occurs somewhere". -/
theorem not_isAttractor_singleton :
    ¬ IsAttractor ababa ({(⟨0, by decide⟩ : Fin ababa.length)} : Finset (Fin ababa.length)) := by
  rw [isAttractor_iff_check]
  decide

/-- A single position *is* enough when the word is unary: `γ = 1` for `"aaa"`. -/
example : IsAttractor (['a', 'a', 'a'] : List Char)
    ({(⟨1, by decide⟩ : Fin 3)} : Finset (Fin 3)) := by
  rw [isAttractor_iff_check]
  decide

end SortBounds.Projects.Repetitiveness
