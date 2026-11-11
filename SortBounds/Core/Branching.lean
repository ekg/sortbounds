/-
SortBounds/Core/Branching.lean

The reusable heart of every lower bound in this repository: **bits per probe**.

An algorithm that decides among `N` outcomes by a sequence of steps, where each
step has at most `b` possible results, needs at least `log_b N` steps — provided
distinct outcomes are separated by distinct transcripts.  The comparison-sorting
bound is the case `b = 2`; radix sorting uses `b` buckets per pass, an algebraic
decision tree uses the three signs, a word-RAM read of a `w`-bit word has
`b = 2 ^ w`, and so on.

The combinatorial content is Kraft's inequality: a prefix-free set of words over
an alphabet of size `b` has Kraft sum `∑ b ^ (-length) ≤ 1`, so if every word has
length at most `c` then the set has at most `b ^ c` elements.  **This file is
deliberately thin: the real combinatorics is Mathlib's**
(`InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`), and
the only content here is the counting corollary and its logarithmic form.  That
is the whole point of `Core`: instantiate, do not re-prove.

Recipe for using it: exhibit a map from inputs to `List (Fin b)` (the transcript
of the algorithm's steps on that input) that is injective on the inputs whose
transcripts are pairwise non-prefix (i.e. on inputs the algorithm
*distinguishes*), with `length = cost`.  Then `#inputs ≤ b ^ cost`, and
`log_b #inputs ≤ cost`.  `SortBounds.Comparison.Aggregate` is the `b = 2`
instance for comparison trees, with the transcripts read off the tree; and
`SortBounds.Instances.Network` is the cryptomorphic instance for sorting
networks, where the transcript is the swap/no-swap pattern.
-/
import Mathlib

namespace SortBounds

variable {b c : ℕ} [NeZero b]

/-- **Bits per probe, counting form.**  A prefix-free set of words over an
alphabet of size `b`, each of length at most `c`, has at most `b ^ c` elements.
Immediate from Kraft's inequality: `#P · b ^ (-c) ≤ ∑ b ^ (-length) ≤ 1`. -/
theorem card_le_pow_of_prefixFree (P : Finset (List (Fin b)))
    (hpre : ∀ p ∈ P, ∀ q ∈ P, p <+: q → p = q)
    (hlen : ∀ p ∈ P, p.length ≤ c) : P.card ≤ b ^ c := by
  classical
  -- Kraft's inequality (Mathlib, information theory)
  have hK : ∑ w ∈ P, (1 / (Fintype.card (Fin b) : ℝ)) ^ w.length ≤ 1 :=
    InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one (α := Fin b)
      (S := P) hpre
  have hb : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne b)
  have hb1 : (1 / (b : ℝ)) ≤ 1 := by
    rw [div_le_one hb]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne b)
  -- every word of length `≤ c` carries at least the weight `(1/b)^c`
  have hterm : ∀ w ∈ P, (1 / (b : ℝ)) ^ c ≤ (1 / (Fintype.card (Fin b) : ℝ)) ^ w.length := by
    intro w hw
    rw [Fintype.card_fin]
    exact pow_le_pow_of_le_one (by positivity) hb1 (hlen w hw)
  have hcard : (P.card : ℝ) * (1 / (b : ℝ)) ^ c ≤ 1 := by
    calc (P.card : ℝ) * (1 / (b : ℝ)) ^ c = ∑ _w ∈ P, (1 / (b : ℝ)) ^ c := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ w ∈ P, (1 / (Fintype.card (Fin b) : ℝ)) ^ w.length := Finset.sum_le_sum hterm
      _ ≤ 1 := hK
  have hgoal : (P.card : ℝ) ≤ (b : ℝ) ^ c := by
    have hcancel : (1 / (b : ℝ)) ^ c * (b : ℝ) ^ c = 1 := by
      rw [← mul_pow, one_div, inv_mul_cancel₀ hb.ne', one_pow]
    nlinarith [hcard, hcancel, pow_pos (by positivity : (0 : ℝ) < 1 / (b : ℝ)) c]
  exact_mod_cast hgoal

omit [NeZero b] in
/-- **Bits per probe, logarithmic form.**  If `N ≤ b ^ c` and `1 < b`, then
`log_b N ≤ c`: `c` steps with `b` outcomes each carry at most `c · log₂ b` bits. -/
theorem logb_le_of_le_pow {N : ℕ} (hb : 1 < b) (hN : 0 < N) (h : N ≤ b ^ c) :
    Real.logb b N ≤ (c : ℝ) := by
  rw [Real.logb_le_iff_le_rpow (show (1 : ℝ) < (b : ℝ) by exact_mod_cast hb)
    (by exact_mod_cast hN)]
  calc (N : ℝ) ≤ (b : ℝ) ^ c := by exact_mod_cast h
    _ = (b : ℝ) ^ (c : ℝ) := by rw [Real.rpow_natCast]

end SortBounds
