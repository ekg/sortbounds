/-
SortBounds/Projects/Repetitiveness/Greedy.lean

**M3, part 3: a computable attractor construction, and the certified sandwich.**

Finding a *smallest* attractor is NP-hard (`docs/research/space.md`:114 on `γ`), so no
algorithm here can return `γ`.  What an index can do instead is construct *some* attractor —
computably — and use its size as a certified upper bound on `γ` and (via `delta_le_gamma`) on
`δ`.  This file provides that construction and proves it valid.  **The theorem is about
validity, not about size**: `greedyAttractor_isAttractor` says the set is an attractor;
nothing here says it is small.

**The algorithm.**  Scan the positions left to right, keeping a position `p` exactly when it
covers some factor occurrence that the positions kept so far do not cover
(`addsNew`, decided by `coversPos`).  Equivalently: a maximal irredundant cover grown in
scan order.  Termination is built into the scan (`greedyIter`), and the invariant is

> after the first `p` steps, every factor occurrence lying inside `[0, p)` is covered

(`exists_cover_greedyIter`).  Since every occurrence of a nonempty factor lies inside
`[0, n)`, the final set is an attractor.  The construction is *not* the maximum-coverage
greedy and it is *not* `univ`; on a nonempty string it is nonempty
(`greedyAttractor_nonempty`) and on `"ababa"` it is `{0, 1}` of size `2` — the optimum
`γ = 2` for that word.

**The sandwich.**  `delta s ≤ (greedyAttractor s).card` is `δ ≤ |Γ|` for the constructed `Γ`,
so (`greedyCertificate`) computes a certified interval `[δ, |Γ_greedy|]` around the smallest
attractor without solving the NP-hard problem.
-/
import Mathlib
import SortBounds.Projects.Repetitiveness.Basic
import SortBounds.Projects.Repetitiveness.Attractor
import SortBounds.Projects.Repetitiveness.Measures
import SortBounds.Projects.Repetitiveness.Certify

namespace SortBounds.Projects.Repetitiveness

variable {α : Type*} [DecidableEq α]

/-! ### The greedy criterion -/

/-- **Does position `p` add anything new?**  It does iff some nonempty factor occurrence is
covered by `p` (`coversPos s i k p = true`) and by no position of `Γ`.  Stated with bounded
quantifiers (`Fin (s.length + 1)`) and `abbrev`d, so that instance search unfolds it and the
`if` below is a *computable* decision. -/
abbrev addsNew (s : List α) (Γ : Finset (Fin s.length)) (p : ℕ) : Prop :=
  ∃ i k : Fin (s.length + 1), 1 ≤ (k : ℕ) ∧ (i : ℕ) + (k : ℕ) ≤ s.length ∧
    coversPos s (i : ℕ) (k : ℕ) p = true ∧
      ∀ q ∈ Γ, coversPos s (i : ℕ) (k : ℕ) (q : ℕ) = false

/-! ### The scan -/

/-- One step of the scan at position `p`: keep `p` iff it adds something new.  (Positions
outside the string are skipped; they arise only in `greedyIter` for `p ≥ s.length`, which
`greedyAttractor` never reaches.) -/
def greedyStep (s : List α) (Γ : Finset (Fin s.length)) (p : ℕ) : Finset (Fin s.length) :=
  if h : p < s.length then
    (if addsNew s Γ p then insert ⟨p, h⟩ Γ else Γ)
  else Γ

/-- The set kept after scanning the positions `0, …, p-1`. -/
def greedyIter (s : List α) : ℕ → Finset (Fin s.length)
  | 0 => ∅
  | p + 1 => greedyStep s (greedyIter s p) p

/-- **The computable attractor construction**: scan all `n` positions. -/
def greedyAttractor (s : List α) : Finset (Fin s.length) := greedyIter s s.length

/-! ### Correctness of the scan -/

theorem greedyIter_succ (s : List α) (p : ℕ) (hp : p < s.length) :
    greedyIter s (p + 1) =
      if addsNew s (greedyIter s p) p then insert ⟨p, hp⟩ (greedyIter s p) else greedyIter s p := by
  simp [greedyIter, greedyStep, hp]

/-- The scan only adds positions: step `p` keeps everything kept before. -/
theorem greedyIter_subset_succ (s : List α) (p : ℕ) : greedyIter s p ⊆ greedyIter s (p + 1) := by
  rcases Nat.lt_or_ge p s.length with hp | hp
  · rw [greedyIter_succ s p hp]
    by_cases h : addsNew s (greedyIter s p) p
    · rw [ite_eq_left h]
      exact Finset.subset_insert _ _
    · rw [ite_eq_right h]
  · simp [greedyIter, greedyStep, Nat.not_lt.mpr hp]

/-- **A position that adds nothing is redundant**: every occurrence it covers is already
covered by `Γ`.  This is where `¬ addsNew` is used, and it is what makes the invariant below
survive a step that keeps nothing. -/
theorem exists_mem_of_not_addsNew {s : List α} {Γ : Finset (Fin s.length)} {p : ℕ}
    (h : ¬ addsNew s Γ p) {i k : ℕ} (hk : 1 ≤ k) (hik : i + k ≤ s.length)
    (hcov : coversPos s i k p = true) : ∃ q ∈ Γ, coversPos s i k (q : ℕ) = true := by
  have step1 : ¬ (1 ≤ k ∧ i + k ≤ s.length ∧ coversPos s i k p = true ∧
      ∀ q ∈ Γ, coversPos s i k (q : ℕ) = false) :=
    fun hc => h ⟨⟨i, by omega⟩, ⟨k, by omega⟩, hc⟩
  by_contra hc
  apply step1
  refine ⟨hk, hik, hcov, ?_⟩
  intro q hq
  by_cases hqc : coversPos s i k (q : ℕ) = true
  · exact absurd ⟨q, hq, hqc⟩ hc
  · cases hb : coversPos s i k (q : ℕ) <;> simp_all

/-- **The invariant of the scan.**  After `p` steps every factor occurrence contained in
`[0, p)` is covered by a kept position: a new occurrence either was already covered, or
contains the current position `p` (which therefore covers it and which is kept unless it
adds nothing, in which case the occurrence was covered after all). -/
theorem exists_cover_greedyIter (s : List α) :
    ∀ p : ℕ, p ≤ s.length → ∀ i k : ℕ, 1 ≤ k → i + k ≤ p →
      ∃ q ∈ greedyIter s p, coversPos s i k (q : ℕ) = true := by
  intro p
  induction p with
  | zero => intro _ i k hk hik; omega
  | succ p ih =>
    intro hp i k hk hik
    rcases Nat.lt_or_ge (i + k) (p + 1) with hlt | hge
    · obtain ⟨q, hq, hqc⟩ := ih (by omega) i k hk (by omega)
      exact ⟨q, greedyIter_subset_succ s p hq, hqc⟩
    · have hik' : i + k = p + 1 := by omega
      have hp' : p < s.length := by omega
      have hcov : coversPos s i k p = true :=
        coversPos_of_le_of_lt (by omega) (by omega) (by omega)
      rw [greedyIter_succ s p hp']
      by_cases hnew : addsNew s (greedyIter s p) p
      · rw [ite_eq_left hnew]
        exact ⟨⟨p, hp'⟩, Finset.mem_insert_self _ _, by simpa using hcov⟩
      · rw [ite_eq_right hnew]
        obtain ⟨q, hq, hqc⟩ := exists_mem_of_not_addsNew hnew hk (by omega) hcov
        exact ⟨q, hq, hqc⟩

/-- **The construction is valid**: the greedy scan returns a string attractor of `s`.
(Validity, not size — the smallest attractor is NP-hard to find.) -/
theorem greedyAttractor_isAttractor (s : List α) : IsAttractor s (greedyAttractor s) := by
  refine (isAttractor_iff_coversAllFactors s (greedyAttractor s)).mpr ?_
  intro i k hk hik
  exact exists_cover_greedyIter s s.length le_rfl i k hk hik

/-- **The construction is not vacuous**: a nonempty string gets a nonempty attractor.  (The
scan keeps position `0` or keeps nothing only because everything position `0` covers was
already kept — and at `p = 0` nothing was.) -/
theorem greedyAttractor_nonempty {s : List α} (hs : s ≠ []) : (greedyAttractor s).Nonempty := by
  have hlen : 0 < s.length := by
    cases s with
    | nil => exact absurd rfl hs
    | cons _ _ => simp
  obtain ⟨q, hq, -⟩ := exists_cover_greedyIter s s.length le_rfl 0 1 (by omega) (by omega)
  exact ⟨q, hq⟩

/-- The constructed attractor is never larger than the string. -/
theorem greedyAttractor_card_le_length (s : List α) : (greedyAttractor s).card ≤ s.length := by
  have := Finset.card_le_univ (greedyAttractor s)
  simpa using this

/-- **The certified sandwich**: `δ ≤ |Γ_greedy|`, so `|Γ_greedy|` is a *computable* certified
upper bound on the smallest attractor (`γ ≤ |Γ_greedy|` by `delta_le_gamma`'s companion,
`minAttractorSize_le`) and `|Γ_greedy| / δ` a computable approximation ratio. -/
theorem delta_le_greedyAttractor_card (s : List α) :
    delta s ≤ (greedyAttractor s).card :=
  delta_le_card_attractor (greedyAttractor_isAttractor s)

/-! ### The system, closed: the construction feeds the certificate and passes the verifier -/

/-- **The greedy construction as a certificate**: a program, not a proof obligation, produces
a certified upper bound on `γ` — `(greedyCertificate s).pos.card`. -/
def greedyCertificate (s : List α) : AttractorCertificate s :=
  ⟨greedyAttractor s, greedyAttractor_isAttractor s⟩

/-- The verifier accepts what the construction produces: `checkAttractor` and
`greedyAttractor` agree, so the certification system is closed under its own decision
procedure. -/
theorem checkAttractor_greedyAttractor (s : List α) :
    checkAttractor s (greedyAttractor s) = true :=
  checkAttractor_eq_true_iff.mpr (greedyAttractor_isAttractor s)

/-- The certified interval for the constructed attractor: `[δ, |Γ_greedy|]`. -/
theorem delta_le_greedyCertificate_card (s : List α) :
    delta s ≤ (greedyCertificate s).pos.card :=
  (greedyCertificate s).delta_le

/-- **The certified sandwich in one statement**: `δ ≤ γ ≤ |Γ_greedy|`.  The lower end `δ` is
computable exactly (KNP), the upper end is the computed size of the constructed attractor, and
the middle is the NP-hard quantity the two bracket. -/
theorem delta_le_gamma_le_greedyAttractor_card (s : List α) :
    delta s ≤ gamma s ∧ gamma s ≤ (greedyAttractor s).card :=
  ⟨delta_le_gamma s, gamma_le_card_attractor (greedyAttractor_isAttractor s)⟩

/-! ### The running example -/

/-- On `"ababa"` the construction returns exactly the two-position attractor `{0, 1}`: it
keeps `0` (`a`), keeps `1` (`b`), and every later position covers only factors already
covered by those two.  Computed, not asserted: `decide` evaluates the scan. -/
theorem greedyAttractor_ababa : greedyAttractor ababa = ababaAttractor := by decide

/-- The worked-example numbers: `δ = 2` and `|Γ_greedy| = 2`, so on `"ababa"` the certified
interval is the point `δ = γ = |Γ_greedy| = 2`. -/
theorem greedyAttractor_ababa_card : (greedyAttractor ababa).card = 2 := by decide

example : delta ababa ≤ (greedyAttractor ababa).card :=
  delta_le_greedyAttractor_card ababa

/-- End to end: the construction runs, the verifier accepts its output, and `δ` is bounded —
all on `"ababa"`. -/
example : checkAttractor ababa (greedyAttractor ababa) = true := by decide

/-- The construction is not `univ`: for `"ababa"` it is strictly smaller than all positions. -/
example : (greedyAttractor ababa).card < ababa.length := by decide

/-! ### A second worked example: the construction is a cover, not the smallest one -/

/-- `{1, 2}` is an attractor of `"aab"`: `a` at `1`, `b` at `2`, and `aa`, `ab`, `aab` all occur
crossing position `1`. -/
theorem aab_isAttractor :
    IsAttractor (['a', 'a', 'b'] : List Char)
      ({(⟨1, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3)} : Finset (Fin 3)) := by
  rw [isAttractor_iff_check]
  decide

/-- The greedy scan keeps all three positions of `"aab"`: at `p = 1` the factor `ab` is
covered by `1` and by no occurrence containing `0`. -/
theorem greedyAttractor_aab_card : (greedyAttractor (['a', 'a', 'b'] : List Char)).card = 3 := by
  decide

theorem aab_delta : delta (['a', 'a', 'b'] : List Char) = 2 := by decide

/-- `γ = 2` for `"aab"`: `γ ≤ 2` from the explicit attractor `{1, 2}` and `γ ≥ δ = 2`. -/
theorem aab_gamma : gamma (['a', 'a', 'b'] : List Char) = 2 := by
  refine le_antisymm ?_ ((aab_delta ▸ delta_le_gamma (['a', 'a', 'b'] : List Char)))
  have h := gamma_le_card_attractor aab_isAttractor
  simpa using h

/-- **The construction is provably not optimal, so the certified interval is genuinely
strict.**  On `"aab"` one has `δ = 2 = γ < 3 = |Γ_greedy|`: the greedy scan is a cover and not
the smallest one.  This is the honest shape of the system — `|Γ_greedy|` is a computable
*upper* bound, not a computation of `γ` (which is NP-hard). -/
theorem aab_delta_lt_greedy :
    delta (['a', 'a', 'b'] : List Char) < (greedyAttractor (['a', 'a', 'b'] : List Char)).card := by
  rw [aab_delta, greedyAttractor_aab_card]
  norm_num

end SortBounds.Projects.Repetitiveness
