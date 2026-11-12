/-
SortBounds/Projects/BenOr/Bound.lean

The two statements the lane exists for, and the step between them that *is*
proved.

* `componentBound d` — Ben-Or's topological lower bound at fixed degree:
  height `Ω(log #components)`.
* `BenOrBound` — the same, for every fixed degree; this is "the statement of
  Ben-Or's bound", recorded as a `Prop` and deliberately not proved.
* `elementDistinctComponents` (`SortBounds.Projects.BenOr.Components`) — the
  component count `n!` that feeds the bound; proved in
  `SortBounds.Projects.BenOr.Sectors` (`numComponents_distinctSet`).
* `BenOrDistinctness d` — what one actually wants: `Ω(log n!)` for element
  distinctness at fixed degree.
* `ElementDistinctHeightBound d` — the same bound as usually quoted,
  `Ω(n log n)`.
* `componentBound_distinctness`, `elementDistinctHeightBound_of_distinctness`,
  `elementDistinctHeightBound_of_benOrBound` — the *proved* steps
  `componentBound d + (n! components) ⇒ Ω(log n!) ⇒ Ω(n log n)`.

So the only unproved input left is Ben-Or's own bound; the model, the counting,
the component count (`Sectors.lean`), the Stirling arithmetic and the reductions
are all checked.  Nothing here is a `sorry`.
-/
import Mathlib
import SortBounds.Comparison.Stirling
import SortBounds.Projects.BenOr.Components

namespace SortBounds.Projects.BenOr

/-- **Ben-Or's bound, fixed degree.**  There is `c > 0` such that every tree of
degree at most `d` deciding a set `S` of real points has height at least
`c · log (#connected components of S)`.

With `d = 1` the tests are affine, the cells of a leaf are convex, and the bound
is the comparison bound in disguise.  For `d ≥ 2` cells stop being connected —
`x ↦ x² - 1` is positive on a disconnected set — and Ben-Or's method has to
recover connectivity from the *components of the decided set* instead.  The
constant depends on `d`; that dependence (`1 / log d` in Ben-Or's and
Steele–Yao's versions) is absorbed into `c` because `d` is fixed. -/
def componentBound (d : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (t : ADT n) (S : Set (Fin n → ℝ)),
    t.degreeLe d → t.decidesReal S → c * Real.log (numComponents S) ≤ (t.height : ℝ)

/-- **The statement of Ben-Or's bound** (Ben-Or, *Lower bounds for algebraic
computation trees*, STOC 1983): the topological lower bound holds at every fixed
degree.  Recorded, not proved — the proof is real semialgebraic geometry
(Milnor–Thom component bounds). -/
def BenOrBound : Prop := ∀ d : ℕ, componentBound d

/-- The `Ω(log n!)` height bound for element distinctness at fixed degree `d`.
This is the form in which the bound is compared with the comparison model, where
`b = 2` gives the same `log₂ n!` directly. -/
def BenOrDistinctness (d : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (t : ADT n),
    t.degreeLe d →
      t.decidesReal (distinctSet n) → c * Real.log (n.factorial : ℝ) ≤ (t.height : ℝ)

/-- **Ben-Or's reduction, checked.**  Feed the topological bound the component
count of element distinctness and out comes the height bound:

`componentBound d` + (`n!` components for every `n`) ⇒ `Ω(log n!)` for
distinctness at degree `d`.

The first hypothesis is Ben-Or's own unproved input; the second is a *theorem*
since `SortBounds.Projects.BenOr.Sectors` (`forall_elementDistinctComponents`),
so `Sectors.lean` restates this reduction with only `componentBound d` assumed.  The
step that turns components into a height bound is this theorem. -/
theorem componentBound_distinctness (d : ℕ) (hb : componentBound d)
    (hcomp : ∀ n : ℕ, elementDistinctComponents n) : BenOrDistinctness d := by
  obtain ⟨c, hc, hbound⟩ := hb
  refine ⟨c, hc, fun n t hdeg hdec => ?_⟩
  have h := hbound n t (distinctSet n) hdeg hdec
  rwa [hcomp n] at h

/-- **The form the bound is quoted in.**  `Ω(n log n)` tests are needed to decide
element distinctness at fixed degree, for `n` real inputs. -/
def ElementDistinctHeightBound (d : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (t : ADT n),
    t.degreeLe d →
      t.decidesReal (distinctSet n) → c * (n : ℝ) * Real.log n ≤ (t.height : ℝ)

/-- Elementary Stirling bound in natural log, `n log n / 16 ≤ log n!`, proved
from `SortBounds.half_pow_le_factorial`.  (`SortBounds.Comparison.Stirling` has
the base-2 version `logb_factorial_ge_quarter` for `n ≥ 64`; this one holds for
every `n`, which is what the unconditional-looking range below needs.) -/
theorem log_factorial_ge_sixteenth (n : ℕ) :
    (n : ℝ) * Real.log n / 16 ≤ Real.log (n.factorial : ℝ) := by
  rcases le_or_gt n 16 with hn | hn
  · -- `n ≤ 16`: `n / 16 ≤ 1`, so `n log n / 16 ≤ log n ≤ log n!`
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hfac : (n : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast Nat.self_le_factorial n
    have hn16 : (n : ℝ) / 16 ≤ 1 := by
      have : (n : ℝ) ≤ 16 := by exact_mod_cast hn
      linarith
    have h1 : (n : ℝ) * Real.log n / 16 ≤ Real.log n := by
      have := mul_le_mul_of_nonneg_right hn16 hlog
      linarith
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      simp
    · have h2 : Real.log n ≤ Real.log (n.factorial : ℝ) :=
        Real.log_le_log (by exact_mod_cast h0) hfac
      linarith
  · -- `n ≥ 17`: `n! ≥ (n/2)^(n/2)` with `⌊n/2⌋ ≥ n/4`, and `4 log 4 ≤ 3 log n`
    set m : ℕ := n / 2 with hm
    have hfac : (m : ℝ) ^ m ≤ (n.factorial : ℝ) := by
      have h := half_pow_le_factorial n
      rw [← hm] at h
      exact_mod_cast h
    have hm1 : 1 ≤ m := by omega
    have hlogfac : (m : ℝ) * Real.log m ≤ Real.log (n.factorial : ℝ) := by
      have h := Real.log_le_log (by positivity) hfac
      rwa [Real.log_pow] at h
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (16 : ℝ) < n := by exact_mod_cast hn
      linarith
    have hmn : (n : ℝ) / 4 ≤ (m : ℝ) := by
      have h : n ≤ 4 * m := by omega
      have h' : (n : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast h
      linarith
    have hlogm : Real.log ((n : ℝ) / 4) ≤ Real.log m :=
      Real.log_le_log (by linarith) hmn
    have hlog4 : 0 ≤ Real.log ((n : ℝ) / 4) := by
      apply Real.log_nonneg
      have : (16 : ℝ) < n := by exact_mod_cast hn
      linarith
    have hstep : ((n : ℝ) / 4) * Real.log ((n : ℝ) / 4) ≤ (m : ℝ) * Real.log m :=
      mul_le_mul hmn hlogm hlog4 (by positivity)
    have hlogdiv : Real.log ((n : ℝ) / 4) = Real.log n - Real.log 4 := by
      rw [Real.log_div hnpos.ne' (by norm_num)]
    have h3 : 4 * Real.log 4 ≤ 3 * Real.log n := by
      have hmono : Real.log (256 : ℝ) ≤ Real.log ((n : ℝ) ^ 3) := by
        apply Real.log_le_log (by norm_num)
        have h256 : (256 : ℕ) ≤ n ^ 3 := by
          calc 256 ≤ 17 ^ 3 := by norm_num
            _ ≤ n ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have : (256 : ℝ) ≤ (n : ℝ) ^ 3 := by exact_mod_cast h256
        exact this
      have h256 : Real.log (256 : ℝ) = 4 * Real.log 4 := by
        have : (256 : ℝ) = 4 ^ 4 := by norm_num
        rw [this, Real.log_pow]
        norm_num
      rw [h256, Real.log_pow] at hmono
      push_cast at hmono
      linarith
    nlinarith [hstep, hlogfac, hlogdiv, h3, hnpos]

/-- **Log arithmetic, checked.**  `Ω(log n!)` implies `Ω(n log n)`. -/
theorem elementDistinctHeightBound_of_distinctness (d : ℕ) (h : BenOrDistinctness d) :
    ElementDistinctHeightBound d := by
  obtain ⟨c, hc, hbound⟩ := h
  refine ⟨c / 16, by linarith, fun n t hdeg hdec => ?_⟩
  have h1 := hbound n t hdeg hdec
  have h2 := log_factorial_ge_sixteenth n
  have h3 : c * ((n : ℝ) * Real.log n / 16) ≤ c * Real.log (n.factorial : ℝ) :=
    mul_le_mul_of_nonneg_left h2 hc.le
  nlinarith [h1, h3]

/-- `BenOrBound` at every fixed degree gives `BenOrDistinctness` at every fixed
degree. -/
theorem benOrBound_distinctness (h : BenOrBound)
    (hcomp : ∀ n : ℕ, elementDistinctComponents n) : ∀ d : ℕ, BenOrDistinctness d :=
  fun d => componentBound_distinctness d (h d) hcomp

/-- `BenOrBound`, i.e. the bound at every fixed degree, gives the element
distinctness height bound at every fixed degree.

**Everything except Ben-Or's topological bound itself is checked**: from
`BenOrBound` (the topological method) and the component count `n!` of
`elementDistinctComponents` follows `Ω(n log n)` tests for element distinctness
at every fixed degree — the same conclusion the comparison model gives with
`b = 2`, recovered from components rather than from branching.  The component
count is now a theorem, so `Sectors.lean`
(`benOrBound_elementDistinctHeightBound`) states this with `BenOrBound` as the
only hypothesis. -/
theorem elementDistinctHeightBound_of_benOrBound (d : ℕ) (h : BenOrBound)
    (hcomp : ∀ n : ℕ, elementDistinctComponents n) : ElementDistinctHeightBound d :=
  elementDistinctHeightBound_of_distinctness d (componentBound_distinctness d (h d) hcomp)

end SortBounds.Projects.BenOr
