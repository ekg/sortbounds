/-
SortBounds/Projects/BenOr/Components.lean

The *topological* input to Ben-Or's method: connected components.

`ℚ` is totally disconnected, so counting connected components of a set of
rational points measures nothing (even `ℚ` itself falls apart into points).
Ben-Or's
argument therefore lives on `ℝ ^ n`, and the trees of `SortBounds.Projects.BenOr.Basic`,
whose coefficient field is `ℚ` (as fixed by the lane's model), are evaluated at
real points by reading the coefficients through `ℚ ↪ ℝ`.  `ADT.run` / `ADT.decides`
remain the rational semantics of the model; `ADT.runReal` / `ADT.decidesReal`
below are the real semantics that the topology needs.

The content of Ben-Or's method is then a single statement, recorded here as the
`Prop` `elementDistinctComponents` and **proved** in
`SortBounds.Projects.BenOr.Sectors` (`numComponents_distinctSet`):

> the set of real points with pairwise distinct coordinates has exactly `n!`
> connected components — one per ordering of the coordinates.

No `sorry`: an unproved target is stated as a `def … : Prop`.  (Of the lane's two
remaining inputs only Ben-Or's own bound, `componentBound` in
`SortBounds.Projects.BenOr.Bound`, is still unproved.)
-/
import Mathlib
import SortBounds.Projects.BenOr.Basic

namespace SortBounds.Projects.BenOr

variable {n : ℕ}

/-- Real semantics of a tree: the same tree, with the rational coefficients of
each test read in `ℝ`.  Left branch when the test is negative, as in `ADT.run`. -/
noncomputable def ADT.runReal : ADT n → (Fin n → ℝ) → Bool
  | .leaf b, _ => b
  | .node p l r, x =>
    if MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p < 0 then runReal l x else runReal r x

/-- `t` decides the set `S` of real points: every input reaches a leaf whose
label matches `S`.  Real counterpart of `ADT.decides`. -/
def ADT.decidesReal (t : ADT n) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ x : Fin n → ℝ, (t.runReal x = true ↔ x ∈ S)

/-- **Element distinctness**, as a set of real points: the inputs whose `n`
coordinates are pairwise distinct.  This is the set Ben-Or's theorem is about;
its complement is the union of the hyperplanes `x i = x j`. -/
def distinctSet (n : ℕ) : Set (Fin n → ℝ) := {x | Function.Injective x}

/-- The number of connected components of `S`, as the cardinality of the space of
components of the subspace `↥S`.  `Nat.card` is `0` on infinite types, so this
count is meaningful only in the finite case — which is the case stated. -/
noncomputable def numComponents (S : Set (Fin n → ℝ)) : ℕ :=
  Nat.card (ConnectedComponents ↥S)

/-- **The component count of element distinctness** (Ben-Or 1983; the input to
every topological lower bound for distinctness, and to Milnor–Thom style
bounds).  `n!` components, one per ordering of the coordinates: on the region
`x (σ 0) < x (σ 1) < ⋯ < x (σ (n-1))` the sign of every `x i - x j` is fixed, so
the region is convex, and two different regions are separated by the continuous
function `x ↦ sign (x i - x j)`.

Stated here and proved in `SortBounds.Projects.BenOr.Sectors`
(`numComponents_distinctSet`), with the sectors `sector σ` as the components.
`SortBounds.Projects.BenOr.Bound` derives Ben-Or's bound *from* this statement. -/
def elementDistinctComponents (n : ℕ) : Prop :=
  numComponents (distinctSet n) = n.factorial

/-- A preconnected nonempty set has exactly one component. -/
theorem numComponents_eq_one_of_isPreconnected {S : Set (Fin n → ℝ)} (hne : S.Nonempty)
    (hpre : IsPreconnected S) : numComponents S = 1 := by
  have hconn : PreconnectedSpace ↥S := Subtype.preconnectedSpace hpre
  have hne' : Nonempty ↥S := hne.to_subtype
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- **Sanity check.**  `elementDistinctComponents` holds at `n = 1`: there is
nothing to distinguish, the set is everything, and `ℝ` is connected. -/
theorem elementDistinctComponents_one : elementDistinctComponents 1 := by
  have hset : distinctSet 1 = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    exact fun a b _ => Subsingleton.elim a b
  rw [elementDistinctComponents, hset, Nat.factorial_one]
  exact numComponents_eq_one_of_isPreconnected ⟨0, trivial⟩ isPreconnected_univ

/-- **Sanity check.**  `elementDistinctComponents` holds at `n = 0`: there is a
single empty tuple. -/
theorem elementDistinctComponents_zero : elementDistinctComponents 0 := by
  have hset : distinctSet 0 = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    exact fun a => a.elim0
  rw [elementDistinctComponents, hset, Nat.factorial_zero]
  exact numComponents_eq_one_of_isPreconnected ⟨fun i => i.elim0, trivial⟩ isPreconnected_univ

end SortBounds.Projects.BenOr
