/-
SortBounds/Core/Entropy.lean

The **average-case** half of the frame, for an arbitrary branching factor.

`Branching.lean` gives the worst case: a prefix-free transcript set with costs
`c_i ≤ c` has `#outcomes ≤ b ^ c`.  The weights of the same transcripts carry the
expectation: if `∑ b ^ (-c_i) ≤ 1` (Kraft), then the *mean* cost is at least
`log_b` of the number of outcomes.  The engine is Gibbs' inequality in its
elementary form `log y ≤ y - 1`, applied at `y = N · b ^ (-c_i)`:

  `N log N - (log b) ∑ c_i = ∑ log(N · b ^ (-c_i)) ≤ N ∑ b ^ (-c_i) - N ≤ 0`.

The comparison-sorting instance (`b = 2`, transcripts = root-to-leaf paths) is
`SortBounds.Comparison.Average.avg_cost_ge_log2_factorial`; this file states the
general version once, so that a radix/word-RAM/algebraic decision procedure gets
its average case by supplying `b` and the Kraft sum, with no new analysis.
-/
import SortBounds.Core.Branching

namespace SortBounds

/-- `log (1 / b) = -log b`, the identity that turns `b ^ (-c)` into `-(log b) · c`. -/
theorem log_inv_of_pos {b : ℝ} (hb : 0 < b) : Real.log (1 / b) = -Real.log b := by
  rw [one_div, Real.log_inv]

/-- **Average case for a `b`-ary decision procedure.**  If the Kraft sum of the cost
weights is at most `1`, the mean cost over the `N` distinguishable outcomes is at
least `log_b N`. -/
theorem mean_cost_ge_logb {ι : Type*} [Fintype ι] [DecidableEq ι] {b : ℕ} (hb : 1 < b)
    (hι : 0 < Fintype.card ι) (c : ι → ℕ)
    (hK : ∑ i, (1 / (b : ℝ)) ^ c i ≤ 1) :
    Real.logb b (Fintype.card ι) ≤ (∑ i, (c i : ℝ)) / Fintype.card ι := by
  classical
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  set S : ℝ := ∑ i, (c i : ℝ) with hS
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hb.le
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.le
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast hι
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  -- Gibbs at `y = N · b ^ (-c i)`
  have hlogsum : (∑ i, Real.log (N * (1 / (b : ℝ)) ^ c i)) ≤ 0 := by
    have hterm : ∀ i, Real.log (N * (1 / (b : ℝ)) ^ c i)
        ≤ N * (1 / (b : ℝ)) ^ c i - 1 := fun i =>
      Real.log_le_sub_one_of_pos (mul_pos hNpos (pow_pos (by positivity) _))
    calc (∑ i, Real.log (N * (1 / (b : ℝ)) ^ c i))
        ≤ ∑ i, (N * (1 / (b : ℝ)) ^ c i - 1) := Finset.sum_le_sum fun i _ => hterm i
      _ = N * (∑ i, (1 / (b : ℝ)) ^ c i) - N := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
            Finset.card_univ]
          have : ((Fintype.card ι : ℕ) : ℝ) = N := by rw [hN]
          rw [this]; ring
      _ ≤ N * 1 - N := by
          have := mul_le_mul_of_nonneg_left hK hNpos.le
          linarith
      _ = 0 := by ring
  -- expand each logarithm
  have hsplit : (∑ i, Real.log (N * (1 / (b : ℝ)) ^ c i)) = N * Real.log N - Real.log b * S := by
    have hterm : ∀ i, Real.log (N * (1 / (b : ℝ)) ^ c i)
        = Real.log N + (c i : ℝ) * Real.log (1 / (b : ℝ)) := by
      intro i
      rw [Real.log_mul hNpos.ne' (pow_ne_zero _ (by positivity)), Real.log_pow]
    have hconst : (∑ _i : ι, Real.log N) = N * Real.log N := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hN, mul_comm]
    have hcost : (∑ i, (c i : ℝ) * Real.log (1 / (b : ℝ))) = S * (-Real.log b) := by
      rw [← Finset.sum_mul, ← hS, log_inv_of_pos hbR]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, hconst, hcost]
    ring
  have hkey : N * Real.log N ≤ Real.log b * S := by
    have h := hlogsum
    rw [hsplit] at h
    linarith
  have hdiv : Real.log N / Real.log b ≤ S / N := by
    rw [div_le_div_iff₀ hlogb hNpos]
    linarith
  have hgoal : Real.logb b (Fintype.card ι) = Real.log N / Real.log b := by
    rw [Real.log_div_log, ← hN]
  rw [hgoal]
  exact hdiv

end SortBounds
