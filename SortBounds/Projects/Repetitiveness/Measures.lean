/-
SortBounds/Projects/Repetitiveness/Measures.lean

**M3, part 1: the two measures, named once.**

Everything in this lane, in `docs/research/`, and in the repository at large should say
`δ` and `γ` for the same two numbers, so they are named here and nowhere else:

* `delta s = substringComplexity s` — KNP's **substring complexity**
  `δ = max { d_k(s)/k : 1 ≤ k ≤ n }` (Kociumaka–Navarro–Prezza, Def. II.1; `d_k` is
  `distinctFactors s k`).
* `gamma s = minAttractorSize s` — Kempa–Prezza's **attractor size** `γ`, the size of the
  smallest string attractor of `s`.

The whole point of the pair is that they are *not* the same number and are not equally
computable (`docs/research/space.md` §1, :114, :153-157):

* **`γ` is NP-hard to compute** — `docs/research/space.md`:114: "(γ is NP-hard to compute
  and non-monotone.)" Its definition here, `minAttractorSize`, is a minimum over the
  (exponentially many) position sets, so it is `noncomputable` for a reason and there is no
  algorithm to write down.  Nothing in this lane claims to compute it.
* **`δ` is computable in linear time** — KNP give an `O(n)`-time algorithm for
  `δ = max_k d_k/k` (recorded in the lane README, M3; implemented publicly as
  `regindex/substring-complexity`).  In this file `δ` inherits the `noncomputable` marker of
  `substringComplexity`, so it cannot be run by `#eval`; its *value* is nevertheless a finite
  maximum of decidable quotients `d_k/k`, and concrete values are proved by kernel
  computation (`ababa_delta` below is `by decide`).  Contrast `gamma`/`minAttractorSize`, on
  which `decide` gets stuck: there the minimum really does range over exponentially many
  candidates.

So the pair is a genuine interval: `δ ≤ γ` (`delta_le_gamma`, KNP Lemma II.4 — proved in
`Attractor.lean` as `substringComplexity_le_minAttractorSize`), and `γ` can exceed `δ` by a
log factor (`γ = Ω(δ log(n/δ))`, KNP Thm III.3), which is why a *certified* upper bound on
`γ` (an explicit attractor) is worth carrying around — see `Certify.lean`.
-/
import Mathlib
import SortBounds.Projects.Repetitiveness.Basic
import SortBounds.Projects.Repetitiveness.Attractor
import SortBounds.Projects.Repetitiveness.Count

namespace SortBounds.Projects.Repetitiveness

variable {α : Type*} [DecidableEq α]

/-- **KNP's `δ`**: the substring complexity `max { d_k(s)/k : 1 ≤ k ≤ n }`.  This is the
lane's single spelling of `δ`; `substringComplexity` is the definition behind it. -/
noncomputable abbrev delta (s : List α) : ℕ := substringComplexity s

/-- **Kempa–Prezza's `γ`**: the size of the smallest string attractor of `s`.  This is the
lane's single spelling of `γ`; `minAttractorSize` is the definition behind it.  `γ` is
NP-hard to compute (`docs/research/space.md`:114), unlike `δ`. -/
noncomputable abbrev gamma (s : List α) : ℕ := minAttractorSize s

/-- **`δ ≤ γ`** (KNP Lemma II.4), as the named anchor of the vocabulary: the substring
complexity is at most the size of the smallest attractor.  The other direction is false in
general (`γ = Ω(δ log(n/δ))`, KNP Thm III.3). -/
theorem delta_le_gamma (s : List α) : delta s ≤ gamma s :=
  substringComplexity_le_minAttractorSize s

omit [DecidableEq α] in
/-- `γ ≤ |Γ|` for *every* attractor `Γ`: the smallest attractor is no larger than any
certified one.  Together with `delta_le_card_attractor` this is the sandwich an index works
with — a lower bound it can compute and an upper bound it can certify. -/
theorem gamma_le_card_attractor {s : List α} {Γ : Finset (Fin s.length)}
    (hΓ : IsAttractor s Γ) : gamma s ≤ Γ.card :=
  minAttractorSize_le hΓ

/-- `δ ≤ |Γ|` for every attractor `Γ` (`delta_le_gamma` composed with
`gamma_le_card_attractor`, kept separate because it is the step the certification system
uses directly). -/
theorem delta_le_card_attractor {s : List α} {Γ : Finset (Fin s.length)}
    (hΓ : IsAttractor s Γ) : delta s ≤ Γ.card :=
  substringComplexity_le_card_attractor hΓ

omit [DecidableEq α] in
/-- `γ ≤ n`: the full position set is an attractor. -/
theorem gamma_le_length (s : List α) : gamma s ≤ s.length := by
  have h := minAttractorSize_le (s := s) (Γ := Finset.univ) (isAttractor_univ s)
  simpa using h

/-- `δ ≤ n`, likewise. -/
theorem delta_le_length (s : List α) : delta s ≤ s.length :=
  (delta_le_gamma s).trans (gamma_le_length s)

/-! ### The running example, in the new vocabulary -/

theorem ababa_delta : delta ababa = 2 :=
  ababa_substringComplexity

theorem ababa_gamma : gamma ababa = 2 :=
  ababa_minAttractorSize

/-- On `"ababa"` the interval `[δ, γ]` is a point: `δ = γ = 2`.  (KNP Thm III.3 shows this
is not the general case.) -/
example : delta ababa ≤ gamma ababa ∧ gamma ababa ≤ (ababaAttractor).card :=
  ⟨delta_le_gamma ababa, gamma_le_card_attractor ababa_isAttractor⟩

end SortBounds.Projects.Repetitiveness
