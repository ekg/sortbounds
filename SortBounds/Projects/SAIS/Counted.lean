/-
SortBounds/Projects/SAIS/Counted.lean

`Verify.lean` proves that the *model* charges `sa.length - 1` inspections to check a
candidate suffix array against its LCP array, but `checkSa` returns only a `Bool`: the
accounting was a specification, not the work of a program.  This file closes that gap
with a **counted checker** — one pass that accumulates both the verdict and the
inspection count — and theorems identifying its components with `checkSa` and with the
model's sum.  So "one inspection per neighbouring pair" is the measured work of an
executable walk, not a separate definition.
-/
import SortBounds.Projects.SAIS.Verify

namespace SortBounds.Projects.SAIS

variable {α : Type*} [LinearOrder α]

/-- The walk behind the counted checker: `p` counts down the neighbouring pairs that
remain, `b` is the verdict so far, `k` the inspection count so far. -/
def checkSaGo (s : List α) (sa : List ℕ) : ℕ → Bool → ℕ → Bool × ℕ
  | 0, b, k => (b, k)
  | p + 1, b, k =>
      checkSaGo s sa p (b && decide (verifyStep s sa p = Ordering.lt))
        (k + inspectCount s (saLcp s sa p) (sa.getD p 0) (sa.getD (p + 1) 0))

/-- The check as a counted program. -/
def checkSaCounted (s : List α) (sa : List ℕ) : Bool × ℕ :=
  checkSaGo s sa (sa.length - 1) true 0

/-- The counted checker accepts exactly what `checkSa` accepts. -/
theorem checkSaCounted_fst (s : List α) (sa : List ℕ) :
    (checkSaCounted s sa).1 = checkSa s sa := by
  have key : ∀ n b k, (checkSaGo s sa n b k).1
      = (b && (List.range n).all (fun p => decide (verifyStep s sa p = Ordering.lt))) := by
    intro n
    induction n with
    | zero => intro b k; simp [checkSaGo]
    | succ n ih =>
      intro b k
      simp only [checkSaGo, ih, List.range_succ, List.all_append]
      simp [Bool.and_assoc, Bool.and_comm]
  simp only [checkSaCounted, checkSa, key, Bool.true_and]

/-- **The counted checker's counter is the model's sum**: the per-pair accounting is the
work of this walk. -/
theorem checkSaCounted_snd (s : List α) (sa : List ℕ) :
    (checkSaCounted s sa).2
      = ∑ p ∈ Finset.range (sa.length - 1),
          inspectCount s (saLcp s sa p) (sa.getD p 0) (sa.getD (p + 1) 0) := by
  have key : ∀ n b k, (checkSaGo s sa n b k).2
      = k + ∑ p ∈ Finset.range n,
          inspectCount s (saLcp s sa p) (sa.getD p 0) (sa.getD (p + 1) 0) := by
    intro n
    induction n with
    | zero => intro b k; simp [checkSaGo]
    | succ n ih =>
      intro b k
      rw [checkSaGo, ih, Finset.sum_range_succ]
      ring
  simp only [checkSaCounted, key, Nat.zero_add]

/-- The counted checker inspects exactly `sa.length - 1` positions. -/
theorem checkSaCounted_cost (s : List α) (sa : List ℕ) :
    (checkSaCounted s sa).2 = sa.length - 1 := by
  rw [checkSaCounted_snd, sum_inspectCount_verify]

/-- It accepts exactly the candidates that pass the check, so the counted program is a
real verifier and not just an accounting device. -/
theorem checkSaCounted_accepts (s : List α) (sa : List ℕ) :
    (checkSaCounted s sa).1 = true ↔ Verified s sa := by
  rw [checkSaCounted_fst, checkSa_eq_true_iff]

end SortBounds.Projects.SAIS
