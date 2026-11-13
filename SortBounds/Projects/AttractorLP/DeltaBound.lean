/-
SortBounds/Projects/AttractorLP/DeltaBound.lean

**`LP* ≥ δ`: every primal-feasible fractional cover of the attractor LP has value at least
the substring complexity.**

`γ / LP* ≤ γ / δ` because `LP* ≥ δ` (`docs/research/lp-gap-growth.md` §3), so the LP gap
can never exceed the `δ`-gap.  This file kernel-checks that inequality in the only form in
which it is available without a simplex: for *every* feasible point, not for the optimum.

The LP (`Gap.lean`) has one row per nonempty factor of `s` and one column per position, the
column of `f` being `coverageSet s f`.  Its integral optimum is `γ` (`isAttractor_iff_coverageSet`
says a position set covers all rows iff it is an attractor), and its *fractional* optimum is
what `lp13_primal`/`lp13_dual` pin down at `11/5`.  What is proved here is that `δ` is a
**lower bound for the whole feasible region**:

  `deltaQ_le_primalValue (hx : PrimalFeasible s x) : deltaQ s ≤ ∑ p, x p`,

so `δ ≤ LP*` for every text, and at the `15/11` witness this is `δ(lp13) ≤ 11/5`.

**The proof is KNP's Lemma II.4 with weights.**  For each length `j` (`1 ≤ j ≤ n`) the
unweighted count `d_j = #(distinctFactors s j)` is replaced by "the weight the cover puts on
the rows of length `j`", and the crucial step is that each *position* can be crossed by at
most `j` distinct length-`j` factors — a factor of length `j` crossing `p` is determined by
the offset of its start behind `p`, an integer in `[0, j)`.  That is the same counting step
as `Repetitiveness.distinctFactors_card_le_mul_attractor` (KNP's `d_k ≤ k|Γ|`), with the
attractor `Γ` replaced by the single position `{p}`; it is proved here as
`card_filter_coverageSet_le` by the same technique — an inclusion into the image
`(s.drop (p - d)).take j` of an explicit offset set, so no `Classical.choose` and no
injectivity proof about a choice function.

Chain (for a fixed `j ∈ [1, n]`):

  `d_j = Σ_{f ∈ D_j} 1 ≤ Σ_{f ∈ D_j} Σ_{p ∈ C(f)} x p        (primal feasibility, x ≥ 0)`
  `    = Σ_p x p · #{f ∈ D_j : p ∈ C(f)}                       (sum swap)`
  `    ≤ Σ_p x p · j = j · Σ_p x p`                            (counting step, x ≥ 0)

hence `d_j / j ≤ Σ x` for every `j ∈ Icc 1 n`, and `deltaQ s` — the supremum of `d_j / j`
over that range — is `≤ Σ x` by `Finset.sup'_le`.
-/
import Mathlib
import SortBounds.Projects.AttractorLP.Gap
import SortBounds.Projects.AttractorLP.Witness

namespace SortBounds.Projects.AttractorLP

open SortBounds.Projects.Repetitiveness

variable {α : Type*} [DecidableEq α]

/-! ### Step 2: every length-`j` factor is a row of the LP -/

/-- A length-`j` factor (`j ≥ 1`) is a nonempty factor of `s`, hence a row of the LP:
`f = s[i .. i+j)` is `factorOcc s i (i + j)`.

The side condition `1 ≤ j` cannot be dropped: for `j = 0` the set `distinctFactors s 0 = {[]}`
contains the empty word, which has no occurrence covering any position and is therefore *not*
in `factorUniverse s` (see the header of `Repetitiveness.Attractor`, where the same condition
is what keeps KNP's Lemma II.4 from being false at `k = 0`).  No upper bound `j ≤ s.length` is
needed: `mem_distinctFactors` already yields a start `i` with `i + j ≤ s.length`. -/
theorem distinctFactors_subset_factorUniverse {s : List α} {j : ℕ} (hj : 1 ≤ j) :
    distinctFactors s j ⊆ factorUniverse s := by
  intro f hf
  obtain ⟨i, hik, rfl⟩ := mem_distinctFactors.mp hf
  exact mem_factorUniverse.mpr ⟨i, i + j, by omega, hik, factorOcc_self s i j⟩

/-! ### Step 5 (the crux): a position is crossed by at most `j` length-`j` factors -/

/-- **The counting step, one position at a time.**  Of the distinct length-`j` factors of
`s`, at most `j` of them cover a fixed position `p`: such a factor has an occurrence
`[i', j')` with `i' ≤ p < j'` and `j' - i' = j`, so its start is `i' = p - d` for a *unique*
`d = p - i' < j`, and `f = (s.drop (p - d)).take j`.

Packaged, as in `distinctFactors_card_le_mul_attractor`, as an inclusion into the image of an
explicit offset set (`Finset.range j` under `d ↦ (s.drop (p - d)).take j`) rather than as an
injection defined by choice: what is *not* needed is injectivity of that map, only that the
image has at most `j` elements. -/
theorem card_filter_coverageSet_le (s : List α) (j : ℕ) (p : Fin s.length) :
    ((distinctFactors s j).filter (fun f => p ∈ coverageSet s f)).card ≤ j := by
  classical
  have hsub : (distinctFactors s j).filter (fun f => p ∈ coverageSet s f) ⊆
      (Finset.range j).image (fun d => (s.drop ((p : ℕ) - d)).take j) := by
    intro f hf
    obtain ⟨hfD, hfp⟩ := Finset.mem_filter.mp hf
    -- an occurrence of `f` covering `p`
    obtain ⟨i', j', hi'p, hpj', hj', heq⟩ := mem_coverageSet.mp hfp
    -- its length is the length of `f`, which is `j`
    have hflen : f.length = j := by
      obtain ⟨i, hik, hfi⟩ := mem_distinctFactors.mp hfD
      rw [← hfi, List.length_take, List.length_drop]
      omega
    have hocc : j' - i' = j := by
      rw [← factorOcc_length hj', heq, hflen]
    -- the offset of the occurrence's start behind `p`
    refine Finset.mem_image.mpr ⟨(p : ℕ) - i', Finset.mem_range.mpr (by omega), ?_⟩
    have hstart : (p : ℕ) - ((p : ℕ) - i') = i' := by omega
    rw [hstart]
    have htake : (s.drop i').take j = factorOcc s i' j' := by
      rw [factorOcc, ← hocc]
    rw [htake, heq]
  calc ((distinctFactors s j).filter (fun f => p ∈ coverageSet s f)).card
      ≤ ((Finset.range j).image (fun d => (s.drop ((p : ℕ) - d)).take j)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range j).card := Finset.card_image_le
    _ = j := Finset.card_range j

/-! ### Step 4: the weighted double sum -/

/-- **Swap the two sums**, weighted: summing the cover's weight over the columns of all
length-`j` factors equals summing `x p` against the number of length-`j` factors covering `p`.

This is the `ℚ`-valued analogue of the first step of `weak_duality`, over the length-`j` part
of the universe instead of the whole of it. -/
theorem sum_distinctFactors_coverage (s : List α) (j : ℕ) (x : Fin s.length → ℚ) :
    ∑ f ∈ distinctFactors s j, ∑ p ∈ coverageSet s f, x p =
      ∑ p : Fin s.length,
        x p * (((distinctFactors s j).filter (fun f => p ∈ coverageSet s f)).card : ℚ) := by
  classical
  -- the column of `f`, as a sum over all positions
  have hsingle : ∀ f : List α, (∑ p ∈ coverageSet s f, x p) =
      ∑ p : Fin s.length, (if p ∈ coverageSet s f then x p else 0) := by
    intro f
    simp only [coverageSet, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  -- a sum of a constant over the positions covering `p` is `x p` times their number
  have hconst : ∀ p : Fin s.length,
      (∑ f ∈ distinctFactors s j, (if p ∈ coverageSet s f then x p else 0)) =
        x p * (((distinctFactors s j).filter (fun f => p ∈ coverageSet s f)).card : ℚ) := by
    intro p
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc ∑ f ∈ distinctFactors s j, ∑ p ∈ coverageSet s f, x p
      = ∑ f ∈ distinctFactors s j,
          ∑ p : Fin s.length, (if p ∈ coverageSet s f then x p else 0) :=
        Finset.sum_congr rfl fun f _ => hsingle f
    _ = ∑ p : Fin s.length,
          ∑ f ∈ distinctFactors s j, (if p ∈ coverageSet s f then x p else 0) :=
        Finset.sum_comm
    _ = ∑ p : Fin s.length,
          x p * (((distinctFactors s j).filter (fun f => p ∈ coverageSet s f)).card : ℚ) :=
        Finset.sum_congr rfl fun p _ => hconst p

/-! ### M0: the counting bound for a fixed length -/

/-- **M0 — KNP Lemma II.4 with weights.**  For a fixed length `j ∈ [1, n]`, the number `d_j`
of distinct length-`j` factors is at most `j` times the value of any primal-feasible cover.

Steps 1–6 of the lane contract: `d_j = Σ_{f ∈ D_j} 1 ≤ Σ_{f ∈ D_j} Σ_{p ∈ C(f)} x p` (each
`f ∈ D_j` is a row, `x ≥ 0`), swap the sums, bound the inner cardinal by `j`
(`card_filter_coverageSet_le`), and multiply out.

Only `1 ≤ j` is assumed.  The lane contract also asked for `j ≤ s.length`, but that is
redundant: `mem_distinctFactors` already yields a start `i` with `i + j ≤ s.length`, which is
all `distinctFactors_subset_factorUniverse` needs in order to place `f` in the universe.  The
`1 ≤ j` cannot be dropped (at `j = 0` the empty word is a factor no position covers, so
`d_0 = 1 > 0`), which is exactly the side condition of the unweighted
`Repetitiveness.distinctFactors_card_le_mul_attractor`; the hypothesis set is the same one. -/
theorem factor_card_le_primal_sum {s : List α} {x : Fin s.length → ℚ}
    (hx : PrimalFeasible s x) {j : ℕ} (hj : 1 ≤ j) :
    ((distinctFactors s j).card : ℚ) ≤ (j : ℚ) * ∑ p, x p := by
  classical
  obtain ⟨hx0, hx1⟩ := hx
  have hsub := distinctFactors_subset_factorUniverse (s := s) hj
  calc ((distinctFactors s j).card : ℚ)
      = ∑ _f ∈ distinctFactors s j, (1 : ℚ) := by simp
    _ ≤ ∑ f ∈ distinctFactors s j, ∑ p ∈ coverageSet s f, x p :=
        Finset.sum_le_sum fun f hf => hx1 f (hsub hf)
    _ = ∑ p : Fin s.length,
          x p * (((distinctFactors s j).filter (fun f => p ∈ coverageSet s f)).card : ℚ) :=
        sum_distinctFactors_coverage s j x
    _ ≤ ∑ p : Fin s.length, x p * (j : ℚ) := by
        refine Finset.sum_le_sum fun p _ => ?_
        exact mul_le_mul_of_nonneg_left
          (by exact_mod_cast card_filter_coverageSet_le s j p) (hx0 p)
    _ = (j : ℚ) * ∑ p : Fin s.length, x p := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => mul_comm _ _

/-! ### M1: `δ ≤ value of every primal-feasible cover` -/

/-- **`LP* ≥ δ`.**  Every primal-feasible fractional cover of the attractor LP has value at
least the substring complexity `δ = max_{1 ≤ k ≤ n} d_k / k`: each length-`k` term of the
supremum is `≤ Σ x` by M0 (`k > 0`), and `Finset.sup'_le` closes the supremum.

Together with `isAttractor_iff_coverageSet` (the integral optimum of the same LP is `γ`) this
is the pair `δ ≤ LP* ≤ γ` — the reason the LP gap `γ/LP*` is dominated by the `δ`-gap. -/
theorem deltaQ_le_primalValue {s : List α} {x : Fin s.length → ℚ}
    (hx : PrimalFeasible s x) : deltaQ s ≤ ∑ p, x p := by
  classical
  unfold deltaQ
  split_ifs with h
  · apply Finset.sup'_le
    intro j hj
    obtain ⟨hj1, -⟩ := Finset.mem_Icc.mp hj
    have hjpos : (0 : ℚ) < (j : ℚ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hj1
    rw [div_le_iff₀ hjpos]
    calc ((distinctFactors s j).card : ℚ)
        ≤ (j : ℚ) * ∑ p, x p := factor_card_le_primal_sum hx hj1
      _ = (∑ p : Fin s.length, x p) * (j : ℚ) := by ring
  · exact Finset.sum_nonneg fun p _ => hx.1 p

/-! ### M2: the instance `s = lp13` -/

/-- **The structural consequence**: since every primal-feasible `x` has value `≥ δ`, the LP gap
`γ / Σx` is **at most** the `δ`-gap `γ / δ`.  This is the inequality that says the attractor LP
cannot be worse than KNP's bound in relative terms — the LP gap is not an independent quantity. -/
theorem gamma_div_primal_le {s : List α} {x : Fin s.length → ℚ} (hx : PrimalFeasible s x)
    (hδ : 0 < deltaQ s) :
    (minAttractorSize s : ℚ) / (∑ p, x p) ≤ (minAttractorSize s : ℚ) / deltaQ s := by
  have hsum : 0 < ∑ p, x p := lt_of_lt_of_le hδ (deltaQ_le_primalValue hx)
  exact div_le_div_of_nonneg_left (by positivity) hδ (deltaQ_le_primalValue hx)

theorem deltaQ_lp13_le : deltaQ lp13 ≤ 11 / 5 := by
  obtain ⟨x, hx, hxval⟩ := lp13_primal
  rw [← hxval]
  exact deltaQ_le_primalValue hx

end SortBounds.Projects.AttractorLP
