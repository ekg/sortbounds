import Mathlib

/-!
# Elementary Stirling-type bounds

This file records two elementary (fully proved) lower bounds for `Nat.factorial`:

* `half_pow_le_factorial` : `(n / 2) ^ (n / 2) ≤ n!`, obtained from the Mathlib fact
  `Nat.factorial_mul_pow_sub_le_factorial` (*n! · n^(m-n) ≤ m!*).
* `logb_factorial_ge_quarter` : `n * logb 2 n / 4 ≤ logb 2 n!` for `n ≥ 64`, obtained by taking
  base-2 logarithms of the first bound and comparing `n / 2` with `n / 4`.
-/

namespace SortBounds

/-- The elementary half-factorial bound: `n! ≥ (n/2)^(n/2)`. -/
theorem half_pow_le_factorial (n : ℕ) : (n / 2) ^ (n / 2) ≤ Nat.factorial n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> decide
  -- `m = n / 2` is positive and `n - n / 2 ≥ n / 2`
  have hm : 1 ≤ n / 2 := by omega
  have hsub : n / 2 ≤ n - n / 2 := by omega
  -- `Nat.factorial_mul_pow_sub_le_factorial` at `m = n / 2`
  have hkey : Nat.factorial (n / 2) * (n / 2) ^ (n - n / 2) ≤ Nat.factorial n :=
    Nat.factorial_mul_pow_sub_le_factorial (n := n / 2) (m := n) (by omega)
  exact le_trans (Nat.pow_le_pow_right hm hsub)
    (le_trans (Nat.le_mul_of_pos_left _ (Nat.factorial_pos (n / 2))) hkey)

/-- `log₂(n) * n = log₂(n ^ n)`. -/
theorem logb_two_pow_self (n : ℕ) (_hn : 1 ≤ n) :
    Real.logb 2 ((n : ℝ)) * (n : ℝ) = Real.logb 2 ((n : ℝ) ^ n) := by
  rw [Real.logb_pow]
  ring

/-- `log₂(n / 2) = log₂ n - 1`. -/
theorem logb_half_le (n : ℝ) (hn : 0 < n) : Real.logb 2 (n / 2) = Real.logb 2 n - 1 := by
  rw [Real.logb_div hn.ne' (by norm_num), Real.logb_self_eq_one (by norm_num)]

/-- Hence the log₂ of `n!` is at least `(n/4)·log₂ n` once `n ≥ 64`. -/
theorem logb_factorial_ge_quarter (n : ℕ) (hn : 64 ≤ n) :
    (n : ℝ) * Real.logb 2 n / 4 ≤ Real.logb 2 (Nat.factorial n) := by
  have hN : 64 ≤ (n : ℝ) := by exact_mod_cast hn
  -- `(n / 2 : ℝ)` is positive, at most `n / 2`, and at least `n / 2 - 1`
  have hMpos : 0 < ((n / 2 : ℕ) : ℝ) := by
    have h : (32 : ℕ) ≤ n / 2 := by omega
    have : (32 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hMle : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have h : 2 * (n / 2) ≤ n := by omega
    exact_mod_cast h
  have hMge : (n : ℝ) / 2 - 1 ≤ ((n / 2 : ℕ) : ℝ) := by
    have h : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h
    linarith
  -- `log₂ n ≥ log₂ 64 = 6`
  have hL : 6 ≤ Real.logb 2 (n : ℝ) := by
    have h64 : (64 : ℝ) = 2 ^ 6 := by norm_num
    have hmono : Real.logb 2 (64 : ℝ) ≤ Real.logb 2 (n : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) hN
    rw [h64, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hmono
    simpa using hmono
  -- `log₂ (n / 2) ≥ log₂ (n / 4) = log₂ n - 2`
  have hlogM : Real.logb 2 (n : ℝ) - 2 ≤ Real.logb 2 ((n / 2 : ℕ) : ℝ) := by
    have hquarter : (n : ℝ) / 4 ≤ ((n / 2 : ℕ) : ℝ) := by linarith
    have hmono : Real.logb 2 ((n : ℝ) / 4) ≤ Real.logb 2 ((n / 2 : ℕ) : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hquarter
    have hdiv : Real.logb 2 ((n : ℝ) / 4) = Real.logb 2 (n : ℝ) - 2 := by
      rw [Real.logb_div (by linarith : (n : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
      have h4 : Real.logb 2 (4 : ℝ) = 2 := by
        have : (4 : ℝ) = 2 ^ 2 := by norm_num
        rw [this, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
        norm_num
      linarith
    linarith
  -- cast the half-factorial bound and take base-2 logarithms
  have hfact : ((n / 2 : ℕ) : ℝ) ^ (n / 2) ≤ ((Nat.factorial n : ℕ) : ℝ) := by
    exact_mod_cast half_pow_le_factorial n
  have hlogfact : ((n / 2 : ℕ) : ℝ) * Real.logb 2 ((n / 2 : ℕ) : ℝ)
      ≤ Real.logb 2 ((Nat.factorial n : ℕ) : ℝ) := by
    have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (x := ((n / 2 : ℕ) : ℝ) ^ (n / 2)) (pow_pos hMpos _) hfact
    rwa [Real.logb_pow] at hmono
  -- the elementary real endgame: `(n / 4) * log₂ n ≤ (n / 2) * log₂ (n / 2)`
  have hstep : 6 * ((n : ℝ) / 4 - 1)
      ≤ Real.logb 2 (n : ℝ) * (((n / 2 : ℕ) : ℝ) - (n : ℝ) / 4) :=
    mul_le_mul hL (by linarith) (by linarith) (by linarith)
  have hkey : (n : ℝ) * Real.logb 2 (n : ℝ) / 4
      ≤ ((n / 2 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) - 2 * ((n / 2 : ℕ) : ℝ) := by
    nlinarith [hstep, hMle, hN]
  have h2 : ((n / 2 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) - 2 * ((n / 2 : ℕ) : ℝ)
      ≤ ((n / 2 : ℕ) : ℝ) * Real.logb 2 ((n / 2 : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogM (le_of_lt hMpos)
    nlinarith [h]
  linarith [hkey, h2, hlogfact]

end SortBounds
