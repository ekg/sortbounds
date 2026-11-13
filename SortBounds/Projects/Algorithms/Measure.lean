/-
SortBounds/Projects/Algorithms/Measure.lean

**Job 3 of this lane: the pipeline, end to end.**

One entry point, `measure s`, returning the three numbers the research briefs say decide which
index family suits a corpus (`docs/research/space.md`, `docs/research/time-1-query-times.md`):

* `δ` — KNP's substring complexity, computed exactly by `deltaCompute` (`O(n³ log n)` character
  work: this is the definition, not the linear-time algorithm of KNP);
* `|Γ_greedy|` — the size of the greedy attractor: an **upper** bound on `γ`, not `γ` itself
  (finding `γ` is NP-hard, `Measures.lean`:114);
* `r` — the number of runs in the BWT, from `numRuns`.

`measure_spec` certifies the three components, and the certified bracket of the repository
(`delta_le_gamma_le_greedyAttractor_card`) turns them into `δ ≤ γ ≤ |Γ_greedy|`.  What `measure`
does *not* do is compute `γ`: nothing here does, and nothing here claims to.

Everything is `#eval`able — that is the point of the lane.  The three numbers are *computed*;
`measure_spec` says they are the numbers the definitions name, `measure_delta_le` gives the bracket
`δ ≤ |Γ_greedy|`, and the two worked examples (`measure_ababa`, `measure_mississippi`) pin the
actual numbers on texts rather than promising them.  No complexity claim beyond the docstrings is
made.
-/
import Mathlib
import SortBounds.Projects.Repetitiveness.Measures
import SortBounds.Projects.Repetitiveness.Greedy
import SortBounds.Projects.Algorithms.Texts
import SortBounds.Projects.Algorithms.Compute
import SortBounds.Projects.Algorithms.SuffixArray

namespace SortBounds.Projects.Algorithms

open SortBounds.Projects.Repetitiveness

variable {α : Type*} [LinearOrder α]

/-- **The measures of a text**: `(δ, |Γ_greedy|, r)`.  Linear-order structure on the alphabet is
what the BWT needs; it also supplies `DecidableEq α`, which `δ` and the greedy scan need. -/
def measure (s : List α) : ℕ × ℕ × ℕ :=
  (deltaCompute s, greedyAttractorSize s, numRuns s)

/-- **The three components are the named measures**: the first is `delta s` (`δ`, KNP's substring
complexity), the second is the size of the greedy attractor — a certified upper bound on `γ` — and
the third is `numRuns s` (`r`, the BWT run count).  Proved by unfolding `measure` and the
equalities `deltaCompute_eq`, `greedyAttractorSize_eq`. -/
theorem measure_spec (s : List α) :
    (measure s).1 = delta s ∧ (measure s).2.1 = (greedyAttractor s).card ∧
      (measure s).2.2 = numRuns s :=
  ⟨deltaCompute_eq s, greedyAttractorSize_eq s, rfl⟩

/-- The computable bracket the pipeline reports: `δ ≤ |Γ_greedy|`, and `γ` sits between them
(`delta_le_gamma_le_greedyAttractor_card`). -/
theorem measure_delta_le (s : List α) : (measure s).1 ≤ (measure s).2.1 := by
  obtain ⟨h1, h2, -⟩ := measure_spec s
  rw [h1, h2]
  exact delta_le_greedyAttractor_card s

/-- The empty text measures `(0, 0, 0)` — proved, not just `#eval`ed: no factors, no positions
to keep, no runs.  (The `#eval` below prints the same.) -/
theorem measure_nil : measure ([] : List α) = (0, 0, 0) := by
  have hg : greedyAttractor ([] : List α) = ∅ := rfl
  have hn : numRuns ([] : List α) = 0 := numRuns_nil α
  simp [measure, deltaCompute, greedyAttractorSize, hg, hn]

/-! ### Running the pipeline -/

#eval measure mississippi
#eval measure ababa
#eval measure (fibWord 6)
#eval measure (['a', 'a', 'a'] : List Char)
#eval measure ([] : List Char)

/-! ### The running example `"ababa"`, end to end and proved

`"ababa"` is the Repetitiveness lane's running example, so its numbers are proved here in full:
`δ = 2`, `|Γ_greedy| = 2`, `r = 2`.  The BWT values are proved the same way as in
`SuffixArray.lean`: characterize the suffix array by `suffixArray_unique` (permutation of
`range 5`, pairwise increasing) and let the definitions reduce. -/

/-- The suffix array of `"ababa"`: `a`(4), `aba`(2), `ababa`(0), `ba`(3), `baba`(1). -/
theorem suffixArray_ababa : suffixArray ababa = [4, 2, 0, 3, 1] := by
  refine (suffixArray_unique (s := ababa) ?_ ?_).symm
  · decide
  · decide

/-- The last column of `"ababa"`: `b` (before 4), `b` (before 2), `a` (wrap at 0), `a` (before 3),
`a` (before 1) — i.e. `bbaaa`. -/
theorem bwt_ababa : bwt ababa = ['b', 'b', 'a', 'a', 'a'] := by
  rw [bwt, suffixArray_ababa]
  decide

theorem numRuns_ababa : numRuns ababa = 2 := by
  rw [numRuns, bwt_ababa]
  decide

/-- **On `"ababa"` the pipeline returns `(2, 2, 2)`**, proved: `δ = 2` (`ababa_delta`), the greedy
attractor keeps `ababaAttractor`'s `2` positions — the optimum `γ = 2` for this word — and the last
column `bbaaa` has `2` runs. -/
theorem measure_ababa : measure ababa = (2, 2, 2) := by
  have h2 : greedyAttractorSize ababa = 2 := by
    rw [greedyAttractorSize_eq, greedyAttractor_ababa_card]
  simp [measure, deltaCompute_ababa, h2, numRuns_ababa]

/-- **On `"mississippi"` the pipeline returns `(4, 10, 8)`**, proved: `δ = 4`, the greedy attractor
keeps `10` of the `11` positions, and the last column `pssmipissii` has `8` runs.  The gap between
the two certified ends (`4` and `10`) is the honest picture: `|Γ_greedy|` is an upper bound on `γ`,
and on a repetitive text a maximal-irredundant-cover scan is far from minimal. -/
theorem measure_mississippi : measure mississippi = (4, 10, 8) := by
  simp [measure, deltaCompute_mississippi, greedyAttractorSize_mississippi, numRuns_mississippi]

end SortBounds.Projects.Algorithms
