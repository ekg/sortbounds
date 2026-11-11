/-
SortBounds/Comparison/Randomized.lean

**Randomisation buys nothing** on the comparison model, and this file is the
one-line reason: a randomised comparison sort is a probability distribution over
*deterministic* comparison trees (fix the coin tosses), and every correct tree
individually has depth at least `log₂(n!)`.  So no mixture of them can have a
smaller expected worst case.

This closes a caveat the README used to carry ("argued, not formalised").  It is
also the honest form of the statement: the bound is on the *depth* of each tree in
the support, so it holds for the expected worst case.  A bound on the expected
*number of comparisons on a random input* is the separate average-case theorem
(`Average.avg_cost_ge_log2_factorial`).
-/
import SortBounds.Comparison.LowerBound

namespace SortBounds

/-- **Randomised lower bound.**  For any finite family of correct comparison trees
and any probability distribution on it, the expected worst-case depth is at least
`log₂(n!)`. -/
theorem expected_depth_ge_log2_factorial {n : ℕ} {T : Finset (Tree n)}
    (hT : ∀ t ∈ T, Correct (α := ℕ) t) (w : Tree n → ℝ)
    (hw : ∀ t ∈ T, 0 ≤ w t) (hsum : ∑ t ∈ T, w t = 1) :
    Real.logb 2 (Nat.factorial n) ≤ ∑ t ∈ T, w t * (depth t : ℝ) := by
  have hbound : ∀ t ∈ T, Real.logb 2 (Nat.factorial n) ≤ (depth t : ℝ) :=
    fun t ht => depth_ge_log2_factorial (hT t ht)
  calc Real.logb 2 (Nat.factorial n) = ∑ t ∈ T, w t * Real.logb 2 (Nat.factorial n) := by
        rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ t ∈ T, w t * (depth t : ℝ) :=
        Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (hbound t ht) (hw t ht)

/-- The same statement with the depth of the *chosen* tree, i.e. of the randomised
algorithm's worst case on a fixed instantiation: no distribution over correct
comparison trees has expected worst case below `log₂(n!)`. -/
theorem expected_worstCase_ge_log2_factorial {n : ℕ} {T : Finset (Tree n)}
    (hT : ∀ t ∈ T, Correct (α := ℕ) t) (w : Tree n → ℝ)
    (hw : ∀ t ∈ T, 0 ≤ w t) (hsum : ∑ t ∈ T, w t = 1) :
    Real.logb 2 (Nat.factorial n) ≤ ∑ t ∈ T, w t * (worstCase t : ℝ) := by
  have hbound : ∀ t ∈ T, Real.logb 2 (Nat.factorial n) ≤ (worstCase t : ℝ) :=
    fun t ht => logb_factorial_le_worstCase (hT t ht)
  calc Real.logb 2 (Nat.factorial n) = ∑ t ∈ T, w t * Real.logb 2 (Nat.factorial n) := by
        rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ t ∈ T, w t * (worstCase t : ℝ) :=
        Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (hbound t ht) (hw t ht)

end SortBounds
