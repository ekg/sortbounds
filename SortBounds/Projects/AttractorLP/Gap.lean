/-
SortBounds/Projects/AttractorLP/Gap.lean

**The set-cover LP of the attractor problem, and weak duality as a theorem.**

Kempa–Prezza (STOC'18, §3) formulate the minimum attractor as a set cover: the universe is
the set of nonempty factors of `s`, the set covering a position `p` is the set of factor
occurrences whose interval contains `p`, and `γ` is the minimum number of positions whose
sets cover the universe.  The LP relaxation of that integer program is

  (P)  min Σ_p x_p   s.t.  Σ_{p ∈ C(f)} x_p ≥ 1 for all f ∈ U,  x ≥ 0
  (D)  max Σ_f y_f   s.t.  Σ_{f ∋ p} y_f ≤ 1 for all p,      y ≥ 0

with `C(f)` the set of positions crossing an occurrence of `f` and `U` the factor universe.
`docs/research/lp-gap.md` measures `γ / LP*` exactly (rational simplex) and reports the
maximum `15/11` over all binary strings with `n ≤ 16`; this file supplies the LP half of the
*finite certificate* for such a value: a feasible primal and a feasible dual of equal value
pin the optimum by weak duality, with no LP theory and no simplex code.

Contents:

* `coverageSet s f` — the column of `f`: the positions crossed by an occurrence of `f`, built
  from `factorOcc` so that it is the same coverage notion `IsAttractor` uses;
* `factorUniverse s` — the rows: all nonempty factors of `s`;
* `isAttractor_iff_coverageSet` — `Γ` is an attractor iff every row meets `Γ` (the LP's
  covering condition, integrally);
* `PrimalFeasible`, `DualFeasible` — the two feasible regions, both stated over the finite
  `factorUniverse` and both decidable at a concrete `x`/`y`, so a proposed witness can be
  checked by evaluation rather than by a solver;
* `weak_duality` — `Σ y ≤ Σ x`, elementarily (swap the two sums; no duality theorem).

The LP optimum is *not* computed here: `weak_duality` plus a matching pair is what a witness
proves, and that is all the integrality gap needs.
-/
import Mathlib
import SortBounds.Projects.Repetitiveness.Basic
import SortBounds.Projects.Repetitiveness.Attractor

namespace SortBounds.Projects.AttractorLP

open SortBounds.Projects.Repetitiveness

variable {α : Type*} [DecidableEq α]

/-- **The LP column of a factor**: the positions crossed by some occurrence of `f`, i.e.
`p ∈ coverageSet s f` iff `f` occurs as the window `s[p-d .. p-d+|f|)` for some offset
`d < |f|`.  This is exactly the set of positions an occurrence of `f` *covers*, so it is the
set whose intersection with `Γ` the attractor condition asks to be nonempty
(`isAttractor_iff_coverageSet`).

Written with the offset rather than with a pair of interval endpoints, because `decide` (and
the kernel) then reads off at most `|f|` windows per position; `mem_coverageSet` states the
same set in the `factorOcc s i j` form. -/
def coverageSet (s : List α) (f : List α) : Finset (Fin s.length) :=
  Finset.univ.filter fun p =>
    ∃ d ∈ Finset.range f.length,
      d ≤ (p : ℕ) ∧ factorOcc s ((p : ℕ) - d) ((p : ℕ) - d + f.length) = f

/-- `p` crosses an occurrence of `f` iff some occurrence interval `[i, j)` of `f` satisfies
`i ≤ p < j`. -/
theorem mem_coverageSet {s : List α} {f : List α} {p : Fin s.length} :
    p ∈ coverageSet s f ↔
      ∃ i j : ℕ, i ≤ (p : ℕ) ∧ (p : ℕ) < j ∧ j ≤ s.length ∧ factorOcc s i j = f := by
  simp only [coverageSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨d, hd, hdp, hwin⟩
    refine ⟨(p : ℕ) - d, (p : ℕ) - d + f.length, by omega, by omega, ?_, hwin⟩
    have hlen : (factorOcc s ((p : ℕ) - d) ((p : ℕ) - d + f.length)).length = f.length := by
      rw [hwin]
    rw [factorOcc_self, List.length_take, List.length_drop] at hlen
    have hle : f.length ≤ s.length - ((p : ℕ) - d) := by omega
    omega
  · rintro ⟨i, j, hip, hpj, hj, heq⟩
    have hlen : (factorOcc s i j).length = j - i := factorOcc_length hj
    have hflen : f.length = j - i := by rw [← hlen, heq]
    refine ⟨(p : ℕ) - i, by omega, by omega, ?_⟩
    have hpi : (p : ℕ) - ((p : ℕ) - i) = i := Nat.sub_sub_self hip
    have hji : i + (j - i) = j := Nat.add_sub_cancel' (le_of_lt (by omega : i < j))
    rw [hpi, hflen, hji]
    exact heq

/-- **The LP rows**: every nonempty factor of `s` (`lp-gap.md`'s universe `U`).  It is the
union of the length-`k` factor sets `distinctFactors s k` over `1 ≤ k ≤ s.length` — the same
shape as `distinctFactors`, so occurrences are quotiented away and `k = 0` (the empty word,
which no position can cover) is excluded.  (The smaller universe keeping only the shortest
factor of each suffix-tree node defines the same LP — `lp-gap.md` §1a; not needed here.) -/
def factorUniverse (s : List α) : Finset (List α) :=
  (Finset.Icc 1 s.length).biUnion fun k =>
    ((Finset.range (s.length + 1)).filter fun i => i + k ≤ s.length).image
      fun i => (s.drop i).take k

theorem mem_factorUniverse {s : List α} {f : List α} :
    f ∈ factorUniverse s ↔ ∃ i j : ℕ, i < j ∧ j ≤ s.length ∧ factorOcc s i j = f := by
  simp only [factorUniverse, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨k, ⟨hk1, hk2⟩, ⟨i, ⟨-, hik⟩, rfl⟩⟩
    exact ⟨i, i + k, ⟨by omega, by omega, factorOcc_self s i k⟩⟩
  · rintro ⟨i, j, hij, hj, rfl⟩
    exact ⟨j - i, ⟨by omega, by omega⟩, ⟨i, ⟨by omega, by omega⟩, rfl⟩⟩

/-- `factorUniverse` is literally the union of the length-`k` factor sets of the lane
(`distinctFactors`), over `1 ≤ k ≤ s.length`: the universe of `lp-gap.md` is KNP's `d_k` counted
per length, with occurrences quotiented away. -/
theorem factorUniverse_eq_biUnion (s : List α) :
    factorUniverse s = (Finset.Icc 1 s.length).biUnion (distinctFactors s) := rfl

/-- **M0: the attractor condition is a covering condition.**  `Γ` is an attractor of `s` iff
every factor of `s` has its coverage set meeting `Γ` — the *integral* version of the LP's
`Σ_{p ∈ C(f)} x_p ≥ 1`.  Both directions are `mem_coverageSet` plus the definition; the
universe `factorUniverse` is exactly the set of substrings the definition quantifies over. -/
theorem isAttractor_iff_coverageSet {s : List α} (Γ : Finset (Fin s.length)) :
    IsAttractor s Γ ↔ ∀ f ∈ factorUniverse s, (coverageSet s f ∩ Γ).Nonempty := by
  constructor
  · intro h f hf
    obtain ⟨i, j, hij, hj, rfl⟩ := mem_factorUniverse.mp hf
    obtain ⟨i', j', -, hj', heq, p, hp, h1, h2⟩ := h i j hij hj
    exact ⟨p, Finset.mem_inter.mpr ⟨mem_coverageSet.mpr ⟨i', j', h1, h2, hj', heq⟩, hp⟩⟩
  · intro h i j hij hj
    have hmem : factorOcc s i j ∈ factorUniverse s :=
      mem_factorUniverse.mpr ⟨i, j, hij, hj, rfl⟩
    obtain ⟨p, hp⟩ := h _ hmem
    rw [Finset.mem_inter] at hp
    obtain ⟨hpC, hpΓ⟩ := hp
    obtain ⟨i', j', h1, h2, h3, h4⟩ := mem_coverageSet.mp hpC
    exact ⟨i', j', by omega, h3, h4, p, hpΓ, h1, by omega⟩

/-- **(P) the primal feasible region**: `x ≥ 0` and every row is covered with weight `≥ 1`.
Stated over `Fin s.length → ℚ`, so both conjuncts are finite (`s.length` positions,
`factorUniverse s` rows) and a proposed `x` is checkable row by row — although not by `decide`
directly: `ℚ` does not reduce in the kernel (see the header of `Witness.lean`). -/
def PrimalFeasible (s : List α) (x : Fin s.length → ℚ) : Prop :=
  (∀ p, 0 ≤ x p) ∧ ∀ f ∈ factorUniverse s, 1 ≤ ∑ p ∈ coverageSet s f, x p

/-- **(D) the dual feasible region**: `y ≥ 0` on the universe and every position carries load
at most `1`.  Nonnegativity is asked only on the finitely many rows in `factorUniverse`, since
`y` enters the objective only there (so this is the same region as `y ≥ 0` on all of
`List α`, restricted to the part that matters — and a finite, decidable condition). -/
def DualFeasible (s : List α) (y : List α → ℚ) : Prop :=
  (∀ f ∈ factorUniverse s, 0 ≤ y f) ∧
    ∀ p, ∑ f ∈ (factorUniverse s).filter (fun f => p ∈ coverageSet s f), y f ≤ 1

/-- **Weak duality**, elementarily: no LP theory, no simplex.

`Σ_f y_f ≤ Σ_f y_f (Σ_{p ∈ C(f)} x_p) ≤ Σ_p x_p (Σ_{f ∋ p} y_f) ≤ Σ_p x_p`:
primal feasibility (`Σ_{p ∈ C(f)} x_p ≥ 1`, `y_f ≥ 0`), then swap the two sums, then dual
feasibility (`Σ_{f ∋ p} y_f ≤ 1`, `x_p ≥ 0`).  Consequently a feasible `x` and a feasible `y`
with `Σ x = Σ y` pin the LP optimum on both sides — which is how the witness for `15/11`
becomes a proof rather than a solver run. -/
theorem weak_duality {s : List α} {x : Fin s.length → ℚ} {y : List α → ℚ}
    (hx : PrimalFeasible s x) (hy : DualFeasible s y) :
    (∑ f ∈ factorUniverse s, y f) ≤ ∑ p, x p := by
  classical
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  -- every row is covered, so each `y f` is bounded by `y f` times its row's coverage
  have hstep1 : (∑ f ∈ factorUniverse s, y f) ≤
      ∑ f ∈ factorUniverse s, y f * (∑ p ∈ coverageSet s f, x p) := by
    refine Finset.sum_le_sum fun f hf => ?_
    calc y f = y f * 1 := (mul_one _).symm
      _ ≤ y f * (∑ p ∈ coverageSet s f, x p) :=
        mul_le_mul_of_nonneg_left (hx1 f hf) (hy0 f hf)
  -- swap the two sums: the load of a position against the weight of a factor
  have hswap : (∑ f ∈ factorUniverse s, y f * (∑ p ∈ coverageSet s f, x p)) =
      ∑ p : Fin s.length,
        (∑ f ∈ (factorUniverse s).filter (fun f => p ∈ coverageSet s f), y f) * x p := by
    have hsingle : ∀ f : List α, y f * (∑ p ∈ coverageSet s f, x p) =
        ∑ p : Fin s.length, if p ∈ coverageSet s f then y f * x p else 0 := by
      intro f
      rw [Finset.mul_sum, ← Finset.sum_filter]
      congr 1
      ext p
      simp
    calc (∑ f ∈ factorUniverse s, y f * (∑ p ∈ coverageSet s f, x p))
        = ∑ f ∈ factorUniverse s, ∑ p : Fin s.length,
            (if p ∈ coverageSet s f then y f * x p else 0) :=
          Finset.sum_congr rfl fun f _ => hsingle f
      _ = ∑ p : Fin s.length, ∑ f ∈ factorUniverse s,
            (if p ∈ coverageSet s f then y f * x p else 0) := Finset.sum_comm
      _ = ∑ p : Fin s.length,
            (∑ f ∈ (factorUniverse s).filter (fun f => p ∈ coverageSet s f), y f) * x p := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_filter, Finset.sum_mul]
  -- the load of every position is at most `1`, and `x` is nonnegative
  have hstep3 : (∑ p : Fin s.length,
      (∑ f ∈ (factorUniverse s).filter (fun f => p ∈ coverageSet s f), y f) * x p) ≤
      ∑ p : Fin s.length, x p := by
    refine Finset.sum_le_sum fun p _ => ?_
    calc (∑ f ∈ (factorUniverse s).filter (fun f => p ∈ coverageSet s f), y f) * x p
        ≤ 1 * x p := mul_le_mul_of_nonneg_right (hy1 p) (hx0 p)
      _ = x p := one_mul _
  exact le_trans hstep1 (le_trans (le_of_eq hswap) hstep3)

end SortBounds.Projects.AttractorLP
