/-
SortBounds/Projects/BenOr/Sectors.lean

**The missing mathematical ingredient of the lane: the distinctness set has exactly
`n!` connected components.**

Ben-Or's bound counts the connected components of the set being decided, so for
element distinctness the whole lower bound rests on the count
`numComponents (distinctSet n) = n!`.  `Components.lean` recorded that count as a
`Prop` (`elementDistinctComponents`); this file proves it, and the proof needs no
algebraic geometry at all:

* a **sector** `sector σ` is the set of points whose increasing order is `σ`, i.e.
  `x (σ 0) < x (σ 1) < ⋯ < x (σ (n-1))`;
* each sector is *convex* and *open* (a finite intersection of open half-spaces),
  and the sectors are pairwise disjoint with union `distinctSet n` (every injective
  point has a unique increasing order — `Tuple.sort` supplies it);
* inside the subspace `↥(distinctSet n)` each sector is therefore **clopen**, its
  complement being the union of the other open sectors, and it is connected
  because it is convex;
* a pairwise disjoint cover by connected clopens is exactly the decomposition into
  connected components (`ConnectedComponents.equivOfIsClopenOfIsConnected`), so
  the components are in bijection with `Equiv.Perm (Fin n)`, of cardinality `n!`.

No `sorry`, no `axiom`.  The proof is by topology and order theory only.
-/
import Mathlib
import SortBounds.Projects.BenOr.Bound

namespace SortBounds.Projects.BenOr

variable {n : ℕ}

/-! ### The sectors -/

/-- The **sector** of a permutation `σ`: the points of `ℝ^n` whose increasing order
is `σ`, i.e. `x (σ 0) < x (σ 1) < ⋯ < x (σ (n-1))`.  On a sector the sign of every
difference `x i - x j` is fixed, which is why a sector is the natural "cell" of the
arrangement of the hyperplanes `x i = x j`. -/
def sector (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {x | ∀ k l : Fin n, k < l → x (σ k) < x (σ l)}

@[simp]
theorem mem_sector {x : Fin n → ℝ} {σ : Equiv.Perm (Fin n)} :
    x ∈ sector σ ↔ ∀ k l : Fin n, k < l → x (σ k) < x (σ l) := Iff.rfl

/-- A sector as an intersection of half-spaces, indexed so that both convexity and
openness are immediate.  The index pairs with `¬ k < l` contribute `Set.univ`. -/
theorem sector_eq_iInter (σ : Equiv.Perm (Fin n)) :
    sector σ = ⋂ k : Fin n, ⋂ l : Fin n, {x : Fin n → ℝ | k < l → x (σ k) < x (σ l)} := by
  ext x
  simp [sector]

theorem halfSpace_eq (σ : Equiv.Perm (Fin n)) {k l : Fin n} (hkl : k < l) :
    {x : Fin n → ℝ | k < l → x (σ k) < x (σ l)} = {x : Fin n → ℝ | x (σ k) < x (σ l)} := by
  ext x
  simp [hkl]

theorem halfSpace_eq_univ (σ : Equiv.Perm (Fin n)) {k l : Fin n} (hkl : ¬ k < l) :
    {x : Fin n → ℝ | k < l → x (σ k) < x (σ l)} = Set.univ := by
  ext x
  simp [hkl]

/-- A sector is an intersection of open half-spaces, hence convex. -/
theorem sector_convex (σ : Equiv.Perm (Fin n)) : Convex ℝ (sector σ) := by
  rw [sector_eq_iInter]
  refine convex_iInter fun k => convex_iInter fun l => ?_
  by_cases hkl : k < l
  · rw [halfSpace_eq σ hkl]
    have hEq : {x : Fin n → ℝ | x (σ k) < x (σ l)}
        = ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (σ k)) -
            (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (σ l))) ⁻¹' Set.Iio 0 := by
      ext x
      simp [sub_lt_iff_lt_add]
    rw [hEq]
    exact (convex_Iio (0 : ℝ)).linear_preimage _
  · rw [halfSpace_eq_univ σ hkl]
    exact convex_univ

/-- A sector is an intersection of open half-spaces, hence open. -/
theorem sector_isOpen (σ : Equiv.Perm (Fin n)) : IsOpen (sector σ) := by
  rw [sector_eq_iInter]
  refine isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun l => ?_
  by_cases hkl : k < l
  · rw [halfSpace_eq σ hkl]
    exact isOpen_lt (continuous_apply (σ k)) (continuous_apply (σ l))
  · rw [halfSpace_eq_univ σ hkl]
    exact isOpen_univ

/-! ### The sectors partition the distinctness set -/

/-- Members of a sector are increasing after reindexing by `σ`, hence monotone. -/
theorem monotone_comp_of_mem_sector {x : Fin n → ℝ} {σ : Equiv.Perm (Fin n)}
    (hx : x ∈ sector σ) : Monotone (x ∘ σ) :=
  fun _ _ hkl => by
    rcases lt_or_eq_of_le hkl with h | rfl
    · exact (hx _ _ h).le
    · exact le_rfl

/-- Points of a sector have pairwise distinct coordinates: `x i < x j` for
`i ≠ j` after reindexing by `σ`. -/
theorem sector_subset_distinctSet (σ : Equiv.Perm (Fin n)) : sector σ ⊆ distinctSet n := by
  intro x hx
  show Function.Injective x
  intro i j hij
  by_contra hne
  have hne' : σ.symm i ≠ σ.symm j := fun h => hne (σ.symm.injective h)
  have h1 : σ (σ.symm i) = i := σ.apply_symm_apply i
  have h2 : σ (σ.symm j) = j := σ.apply_symm_apply j
  rcases lt_or_gt_of_ne hne' with h | h
  · have hlt : x i < x j := by
      have h' := hx (σ.symm i) (σ.symm j) h
      rwa [h1, h2] at h'
    exact absurd hij hlt.ne
  · have hlt : x j < x i := by
      have h' := hx (σ.symm j) (σ.symm i) h
      rwa [h1, h2] at h'
    exact absurd hij.symm hlt.ne

/-- The degenerate sizes `n = 0, 1`: there is only one sector and it is everything (no
pair `k < l` exists), so the component count needs no separate argument there. -/
theorem sector_eq_univ_of_le_one (hn : n ≤ 1) (σ : Equiv.Perm (Fin n)) :
    sector σ = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  intro k l hkl
  have hk : (k : ℕ) < 1 := lt_of_lt_of_le k.isLt hn
  have hl : (l : ℕ) < 1 := lt_of_lt_of_le l.isLt hn
  exact absurd (Fin.lt_def.mp hkl) (by omega)

/-- Every sector is inhabited: the point with `x (σ k) = k`. -/
theorem sector_nonempty (σ : Equiv.Perm (Fin n)) : (sector σ).Nonempty := by
  refine ⟨fun i => (((σ.symm i : Fin n) : ℕ) : ℝ), ?_⟩
  intro k l hkl
  have h1 : σ.symm (σ k) = k := σ.symm_apply_apply k
  have h2 : σ.symm (σ l) = l := σ.symm_apply_apply l
  simp only [h1, h2]
  exact_mod_cast Fin.lt_def.mp hkl

/-- An injective point lies in the sector of `Tuple.sort`: the sorted order is its
increasing order. -/
theorem sort_mem_sector {x : Fin n → ℝ} (hx : Function.Injective x) :
    x ∈ sector (Tuple.sort x) := by
  intro k l hkl
  have hmono : Monotone (x ∘ Tuple.sort x) := Tuple.monotone_sort x
  have hne : (x ∘ Tuple.sort x) k ≠ (x ∘ Tuple.sort x) l := by
    intro heq
    have heq' : x ((Tuple.sort x) k) = x ((Tuple.sort x) l) := heq
    have hkl' : (Tuple.sort x) k = (Tuple.sort x) l := hx heq'
    exact Fin.ne_of_lt hkl ((Tuple.sort x).injective hkl')
  exact lt_of_le_of_ne (hmono hkl.le) hne

/-- **Uniqueness of the sector of a point**: two sectors that meet are equal.  Hence
the sectors are pairwise disjoint, and the increasing order of an injective point is
unique. -/
theorem eq_of_mem_sector {σ τ : Equiv.Perm (Fin n)} {x : Fin n → ℝ}
    (hσ : x ∈ sector σ) (hτ : x ∈ sector τ) : σ = τ := by
  have hmonoσ : Monotone (x ∘ σ) := monotone_comp_of_mem_sector hσ
  have hmonoτ : Monotone (x ∘ τ) := monotone_comp_of_mem_sector hτ
  have hx : Function.Injective x := sector_subset_distinctSet σ hσ
  have heq : x ∘ σ = x ∘ τ := Tuple.unique_monotone hmonoσ hmonoτ
  refine Equiv.ext fun k => hx ?_
  simpa using congrFun heq k

theorem sectors_disjoint {σ τ : Equiv.Perm (Fin n)} (h : σ ≠ τ) :
    Disjoint (sector σ) (sector τ) := by
  refine Set.disjoint_left.mpr fun x hxσ hxτ => h ?_
  exact eq_of_mem_sector hxσ hxτ

/-- **The sectors partition the distinctness set**: every injective point has exactly
one increasing order. -/
theorem distinctSet_eq_iUnion (n : ℕ) : distinctSet n = ⋃ σ : Equiv.Perm (Fin n), sector σ := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨Tuple.sort x, sort_mem_sector hx⟩
  · intro x hx
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hx
    exact sector_subset_distinctSet σ hσ

/-! ### The sectors are the connected components -/

/-- A sector, regarded as a subset of the subspace `↥(distinctSet n)`.  This is where
the topology lives: `distinctSet n` is not closed in `ℝ^n` (it is dense), but inside
it each sector is clopen. -/
def sectorIn (σ : Equiv.Perm (Fin n)) : Set ↥(distinctSet n) :=
  {x | (x : Fin n → ℝ) ∈ sector σ}

@[simp]
theorem mem_sectorIn {σ : Equiv.Perm (Fin n)} {x : ↥(distinctSet n)} :
    x ∈ sectorIn σ ↔ (x : Fin n → ℝ) ∈ sector σ := Iff.rfl

theorem isOpen_sectorIn (σ : Equiv.Perm (Fin n)) : IsOpen (sectorIn σ) :=
  (sector_isOpen σ).preimage continuous_subtype_val

/-- Inside `↥(distinctSet n)` a sector is also closed: its complement is the union of
the other open sectors. -/
theorem isClosed_sectorIn (σ : Equiv.Perm (Fin n)) : IsClosed (sectorIn σ) := by
  rw [← isOpen_compl_iff]
  have hcompl : (sectorIn σ)ᶜ = ⋃ τ ∈ {τ : Equiv.Perm (Fin n) | τ ≠ σ}, sectorIn τ := by
    ext x
    constructor
    · intro hx
      obtain ⟨τ, hτ⟩ : ∃ τ, (x : Fin n → ℝ) ∈ sector τ :=
        Set.mem_iUnion.mp (distinctSet_eq_iUnion n ▸ x.2)
      refine Set.mem_iUnion₂.mpr ⟨τ, ?_, hτ⟩
      rintro rfl
      exact hx hτ
    · rintro hx hxσ
      obtain ⟨τ, hτne, hxτ⟩ := Set.mem_iUnion₂.mp hx
      exact Set.disjoint_left.mp (sectors_disjoint hτne) hxτ hxσ
  rw [hcompl]
  exact isOpen_biUnion fun τ _ => isOpen_sectorIn τ

theorem isClopen_sectorIn (σ : Equiv.Perm (Fin n)) : IsClopen (sectorIn σ) :=
  ⟨isClosed_sectorIn σ, isOpen_sectorIn σ⟩

/-- A sector is connected inside `↥(distinctSet n)`: it is the homeomorphic image of
the convex set `sector σ`. -/
theorem isConnected_sectorIn (σ : Equiv.Perm (Fin n)) : IsConnected (sectorIn σ) := by
  have hsub : sector σ ⊆ distinctSet n := sector_subset_distinctSet σ
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := sector_nonempty σ
    exact ⟨⟨x, hsub hx⟩, hx⟩
  · have hpre : PreconnectedSpace ↥(sector σ) :=
      Subtype.preconnectedSpace (sector_convex σ).isPreconnected
    have hcont : Continuous fun x : ↥(sector σ) =>
        (⟨(x : Fin n → ℝ), hsub x.2⟩ : ↥(distinctSet n)) :=
      Continuous.subtype_mk continuous_subtype_val _
    have hrange : Set.range (fun x : ↥(sector σ) =>
        (⟨(x : Fin n → ℝ), hsub x.2⟩ : ↥(distinctSet n))) = sectorIn σ := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact z.2
      · intro hy
        exact ⟨⟨(y : Fin n → ℝ), hy⟩, Subtype.ext rfl⟩
    rw [← hrange]
    exact isPreconnected_range hcont

theorem iUnion_sectorIn (n : ℕ) :
    ⋃ σ : Equiv.Perm (Fin n), sectorIn σ = Set.univ := by
  ext x
  constructor
  · intro hx
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_univ _
  · intro _
    obtain ⟨σ, hσ⟩ : ∃ σ, (x : Fin n → ℝ) ∈ sector σ :=
      Set.mem_iUnion.mp (distinctSet_eq_iUnion n ▸ x.2)
    exact Set.mem_iUnion.mpr ⟨σ, hσ⟩

theorem pairwiseDisjoint_sectorIn (n : ℕ) ⦃σ τ : Equiv.Perm (Fin n)⦄ (hστ : σ ≠ τ) :
    Disjoint (sectorIn σ) (sectorIn τ) := by
  refine Set.disjoint_left.mpr fun x hxσ hxτ => hστ ?_
  exact eq_of_mem_sector hxσ hxτ

/-- **The components of the distinctness set are the orderings of the coordinates.**
A pairwise disjoint cover by connected clopens is the decomposition into connected
components (`ConnectedComponents.equivOfIsClopenOfIsConnected`), and the sectors are
such a cover; so the components are indexed by `Equiv.Perm (Fin n)`. -/
noncomputable def componentsEquivPerm (n : ℕ) :
    ConnectedComponents ↥(distinctSet n) ≃ Equiv.Perm (Fin n) :=
  ConnectedComponents.equivOfIsClopenOfIsConnected
    (fun σ => isClopen_sectorIn σ)
    (fun _ _ hστ => pairwiseDisjoint_sectorIn n hστ)
    (iUnion_sectorIn n)
    (fun σ => isConnected_sectorIn σ)

/-- The equivalence `componentsEquivPerm` is the intended one: a point of the sector of
`σ` sits in the component indexed by `σ`.  (Not vacuous: every sector is inhabited, so
every permutation indexes a genuine component.) -/
theorem componentsEquivPerm_mk {σ : Equiv.Perm (Fin n)} {x : ↥(distinctSet n)}
    (hx : x ∈ sectorIn σ) : componentsEquivPerm n (ConnectedComponents.mk x) = σ :=
  ConnectedComponents.equivOfIsClopenOfIsConnected_mk
    (fun σ => isClopen_sectorIn σ) (fun _ _ hστ => pairwiseDisjoint_sectorIn n hστ)
    (iUnion_sectorIn n) (fun σ => isConnected_sectorIn σ) x hx

/-- **The distinctness set has exactly `n!` connected components.**  One component per
ordering of the coordinates. -/
theorem numComponents_distinctSet (n : ℕ) :
    Nat.card (ConnectedComponents ↥(distinctSet n)) = Nat.factorial n := by
  refine (Nat.card_congr (componentsEquivPerm n)).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- The lane's component-count statement, now a theorem: `elementDistinctComponents n`
holds for every `n`, so every use of `componentBound_distinctness` and
`elementDistinctHeightBound_of_benOrBound` can discharge its `hcomp` hypothesis. -/
theorem forall_elementDistinctComponents : ∀ n : ℕ, elementDistinctComponents n :=
  numComponents_distinctSet

/-- **Ben-Or's bound gives `Ω(log n!)` for element distinctness**, with the component
count discharged: no hypothesis about `n!` components is needed any more. -/
theorem benOrBound_benOrDistinctness (h : BenOrBound) : ∀ d : ℕ, BenOrDistinctness d :=
  benOrBound_distinctness h forall_elementDistinctComponents

/-- **Ben-Or's bound gives `Ω(n log n)` for element distinctness**, with the component
count discharged. -/
theorem benOrBound_elementDistinctHeightBound (d : ℕ) (h : BenOrBound) :
    ElementDistinctHeightBound d :=
  elementDistinctHeightBound_of_benOrBound d h forall_elementDistinctComponents

end SortBounds.Projects.BenOr
