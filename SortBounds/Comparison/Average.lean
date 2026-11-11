/-
SortBounds/Average.lean

Average-case and worst-case lower bounds, both derived from the weight bound of
`SortBounds/Aggregate.lean`.  A correct comparison tree separates the canonical
inputs `xOfPerm p` (`p` ranging over the `Nat.factorial n` permutations of
`Fin n`), so the weights `(1/2) ^ (number of comparisons)` of those inputs sum
to at most `1`.  Writing `c p` for the number of comparisons made on input `p`,
this file deduces

* `avg_cost_ge_log2_factorial`: the *expected* number of comparisons over a
  uniformly random ordering is at least `log₂(n!)`;
* `max_cost_ge_log2_factorial`: the *worst case* is at least `log₂(n!)`;
* `avg_le_max_cost`: the average never exceeds the worst case.

The analytic content is a single line: `log y ≤ y - 1` for `y > 0`, applied to
`y = n! · (1/2) ^ (c p)` and summed over the `n!` inputs.  This gives
`n! · log(n!) - log 2 · ∑ c p ≤ 0`, i.e. `∑ c p ≥ n! · log₂(n!)`.
-/
import SortBounds.Comparison.Aggregate

namespace SortBounds

open Finset

variable {n : ℕ}

/-- There are `Nat.factorial n` canonical inputs of size `n`. -/
theorem card_univ_perm (n : ℕ) :
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).card : ℝ) = (Nat.factorial n : ℝ) := by
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- **Weight bound over all canonical inputs.**  A correct comparison tree
separates all `n!` canonical inputs, so their weights sum to at most `1`. -/
theorem sum_pow_cost_univ_le_one {t : Tree n} (h : Correct (α := ℕ) t) :
    ∑ p : Equiv.Perm (Fin n), (1 / 2 : ℝ) ^ cost t (xOfPerm p) ≤ 1 := by
  simpa using sum_pow_cost_le_one t Finset.univ (separated_of_correct h)

/-- `log (1/2) = -log 2`, the identity that turns the weights `(1/2) ^ c` into
a bound involving `log 2`. -/
theorem log_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]

/-- **Average-case lower bound.**  Over the `n!` orderings of `n` distinct keys,
a correct comparison sort makes at least `log₂(n!)` comparisons on average. -/
theorem avg_cost_ge_log2_factorial {n : ℕ} {t : Tree n} (h : Correct (α := ℕ) t) :
    Real.logb 2 (Nat.factorial n)
      ≤ (∑ p : Equiv.Perm (Fin n), (cost t (xOfPerm p) : ℝ)) / (Nat.factorial n) := by
  classical
  set N : ℝ := (Nat.factorial n : ℝ) with hN
  set S : ℝ := ∑ p : Equiv.Perm (Fin n), (cost t (xOfPerm p) : ℝ) with hS
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast Nat.factorial_pos n
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `log y ≤ y - 1` at `y = N * (1/2) ^ c p`, summed over all inputs.
  have hlogsum : (∑ p : Equiv.Perm (Fin n), Real.log (N * (1 / 2 : ℝ) ^ cost t (xOfPerm p)))
      ≤ 0 := by
    have hterm : ∀ p : Equiv.Perm (Fin n),
        Real.log (N * (1 / 2 : ℝ) ^ cost t (xOfPerm p))
          ≤ N * (1 / 2 : ℝ) ^ cost t (xOfPerm p) - 1 := fun p =>
      Real.log_le_sub_one_of_pos (mul_pos hNpos (pow_pos (by norm_num) _))
    calc (∑ p : Equiv.Perm (Fin n), Real.log (N * (1 / 2 : ℝ) ^ cost t (xOfPerm p)))
        ≤ ∑ p : Equiv.Perm (Fin n), (N * (1 / 2 : ℝ) ^ cost t (xOfPerm p) - 1) :=
          Finset.sum_le_sum fun p _ => hterm p
      _ = N * (∑ p : Equiv.Perm (Fin n), (1 / 2 : ℝ) ^ cost t (xOfPerm p)) - N := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
            card_univ_perm, ← hN]
          ring
      _ ≤ N * 1 - N := by
          have := mul_le_mul_of_nonneg_left (sum_pow_cost_univ_le_one h) hNpos.le
          linarith
      _ = 0 := by ring
  -- expand the logarithms of the individual weights
  have hsplit : (∑ p : Equiv.Perm (Fin n), Real.log (N * (1 / 2 : ℝ) ^ cost t (xOfPerm p)))
      = N * Real.log N - Real.log 2 * S := by
    have hterm : ∀ p : Equiv.Perm (Fin n),
        Real.log (N * (1 / 2 : ℝ) ^ cost t (xOfPerm p))
          = Real.log N + (cost t (xOfPerm p) : ℝ) * Real.log (1 / 2) := by
      intro p
      rw [Real.log_mul hNpos.ne' (pow_ne_zero _ (by norm_num)), Real.log_pow]
    have hconst : (∑ _p : Equiv.Perm (Fin n), Real.log N) = N * Real.log N := by
      rw [Finset.sum_const, nsmul_eq_mul, card_univ_perm, ← hN, mul_comm]
    have hcost : (∑ p : Equiv.Perm (Fin n), (cost t (xOfPerm p) : ℝ) * Real.log (1 / 2))
        = S * (-Real.log 2) := by
      rw [← Finset.sum_mul, ← hS, log_half]
    rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_add_distrib, hconst, hcost]
    ring
  -- hence `n! · log₂(n!) ≤ ∑ c p`
  have hkey : N * Real.log N ≤ Real.log 2 * S := by
    have h := hlogsum
    rw [hsplit] at h
    linarith
  have hdiv : Real.log N / Real.log 2 ≤ S / N := by
    rw [div_le_div_iff₀ hlog2 hNpos]
    linarith
  have hgoal : Real.logb 2 (Nat.factorial n) = Real.log N / Real.log 2 := by
    rw [← Real.log_div_log, hN]
  rw [hgoal]
  exact hdiv

/-- **Worst-case lower bound.**  Every `(1/2) ^ c p` is at least `(1/2) ^ M`, where
`M` is the maximum number of comparisons; since the weights sum to at most `1`,
`n! · (1/2) ^ M ≤ 1`, i.e. `M ≥ log₂(n!)`. -/
theorem max_cost_ge_log2_factorial {n : ℕ} {t : Tree n} (h : Correct (α := ℕ) t) :
    Real.logb 2 (Nat.factorial n)
      ≤ ((Finset.univ.sup (fun p : Equiv.Perm (Fin n) => cost t (xOfPerm p)) : ℕ) : ℝ) := by
  classical
  set M : ℕ := Finset.univ.sup (fun p : Equiv.Perm (Fin n) => cost t (xOfPerm p)) with hM
  set N : ℝ := (Nat.factorial n : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast Nat.factorial_pos n
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcouple : N * (1 / 2 : ℝ) ^ M ≤ 1 := by
    have hterm : ∀ p : Equiv.Perm (Fin n),
        (1 / 2 : ℝ) ^ M ≤ (1 / 2 : ℝ) ^ cost t (xOfPerm p) := by
      intro p
      refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
      exact Finset.le_sup (f := fun p : Equiv.Perm (Fin n) => cost t (xOfPerm p))
        (Finset.mem_univ p)
    calc N * (1 / 2 : ℝ) ^ M
        = ∑ _p : Equiv.Perm (Fin n), (1 / 2 : ℝ) ^ M := by
          rw [Finset.sum_const, nsmul_eq_mul, card_univ_perm, ← hN, mul_comm]
      _ ≤ ∑ p : Equiv.Perm (Fin n), (1 / 2 : ℝ) ^ cost t (xOfPerm p) :=
          Finset.sum_le_sum fun p _ => hterm p
      _ ≤ 1 := sum_pow_cost_univ_le_one h
  have hstep : Real.log N ≤ (M : ℝ) * Real.log 2 := by
    have hpos : 0 < N * (1 / 2 : ℝ) ^ M := mul_pos hNpos (pow_pos (by norm_num) M)
    have hlog := Real.log_le_log hpos hcouple
    rw [Real.log_mul hNpos.ne' (pow_ne_zero M (by norm_num)), Real.log_pow, Real.log_one,
      log_half] at hlog
    nlinarith
  have hgoal : Real.logb 2 (Nat.factorial n) = Real.log N / Real.log 2 := by
    rw [← Real.log_div_log, hN]
  rw [hgoal, div_le_iff₀ hlog2]
  exact hstep

/-- The average number of comparisons never exceeds the worst case. -/
theorem avg_le_max_cost (t : Tree n) :
    (∑ p : Equiv.Perm (Fin n), (cost t (xOfPerm p) : ℝ)) / (Nat.factorial n)
      ≤ ((Finset.univ.sup (fun p : Equiv.Perm (Fin n) => cost t (xOfPerm p)) : ℕ) : ℝ) := by
  classical
  set M : ℕ := Finset.univ.sup (fun p : Equiv.Perm (Fin n) => cost t (xOfPerm p)) with hM
  have hNpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hsum : (∑ p : Equiv.Perm (Fin n), (cost t (xOfPerm p) : ℝ))
      ≤ (Nat.factorial n : ℝ) * (M : ℝ) := by
    have hterm : ∀ p : Equiv.Perm (Fin n), (cost t (xOfPerm p) : ℝ) ≤ (M : ℝ) := by
      intro p
      have hle := Finset.le_sup (f := fun p : Equiv.Perm (Fin n) => cost t (xOfPerm p))
        (Finset.mem_univ p)
      exact_mod_cast hle
    calc (∑ p : Equiv.Perm (Fin n), (cost t (xOfPerm p) : ℝ))
        ≤ ∑ _p : Equiv.Perm (Fin n), (M : ℝ) := Finset.sum_le_sum fun p _ => hterm p
      _ = (Nat.factorial n : ℝ) * (M : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, card_univ_perm]
  rw [div_le_iff₀ hNpos]
  calc (∑ p : Equiv.Perm (Fin n), (cost t (xOfPerm p) : ℝ))
      ≤ (Nat.factorial n : ℝ) * (M : ℝ) := hsum
    _ = (M : ℝ) * (Nat.factorial n : ℝ) := by ring

end SortBounds
