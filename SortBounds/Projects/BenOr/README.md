# Lane: BenOr — algebraic decision trees

**Question.** In the comparison model each test has 2 outcomes, so `b = 2` and
the bound is `log₂(n!)`. In an *algebraic* decision tree a test asks for the sign
of a polynomial, so `b = 3` and the bound `log₂(n!)` weakens — yet Ben-Or (1983)
recovers `Ω(n log n)` for element distinctness from **topology**: the number of
connected components of the set being decided. This is the standard example of
"the model changes, and the answer changes for non-obvious reasons".

**Why it matters.** It is the honest boundary of our result: our theorem is about
bits per *binary* probe. Ben-Or's is about bits per *component*, and no one has
machine-checked it.

## Contract

Everything below is *in the source today* and elaborated (`lake env lean` on each
file; `Witness.lean` and `Sectors.lean` are new, so the integrator still has to
import them into `SortBounds.lean`). The label says what is established about it:
`PROVED` = there is a proof in this lane; `STATED-ONLY` = the signature is a
definition whose *proposition* nothing here proves (it is stated, cited, and used as
a hypothesis — never `sorry`-ed).

```lean
namespace SortBounds.Projects.BenOr

variable {n : ℕ}

/-! ---- M0, `Basic.lean` ---- -/

/-- An algebraic decision tree over `n` real variables: branch on the sign of a
polynomial, leaves accept/reject. -/
inductive ADT (n : ℕ) where
  | leaf : Bool → ADT n
  | node : MvPolynomial (Fin n) ℚ → ADT n → ADT n → ADT n        -- PROVED (def)

def ADT.height : ADT n → ℕ                                        -- PROVED (def)
def ADT.numCells : ADT n → ℕ                                      -- PROVED (def)
def ADT.run : ADT n → (Fin n → ℚ) → Bool                          -- PROVED (def)
/-- `t` decides `S` if every input reaches a leaf whose label matches `S`. -/
def ADT.decides (t : ADT n) (S : Set (Fin n → ℚ)) : Prop          -- PROVED (def)
/-- Every test has total degree `≤ d`. -/
def ADT.degreeLe (d : ℕ) : ADT n → Prop                           -- PROVED (def)

/-- The combinatorial shadow of Ben-Or: height `h` ⇒ at most `2^h` cells. -/
theorem ADT.card_cells_le (t : ADT n) : t.numCells ≤ 2 ^ t.height              -- PROVED
theorem ADT.one_le_numCells (t : ADT n) : 1 ≤ t.numCells                        -- PROVED
noncomputable def halfLineTree : ADT 1                                          -- PROVED (def)
theorem halfLineTree_decides : halfLineTree.decides {x : Fin 1 → ℚ | 0 ≤ x 0}  -- PROVED
theorem halfLineTree_degreeLe : halfLineTree.degreeLe 1                         -- PROVED

/-! ---- M1, `Components.lean` (the real semantics) ---- -/

/-- Left branch when the test is negative, coefficients read in `ℝ`. -/
noncomputable def ADT.runReal : ADT n → (Fin n → ℝ) → Bool         -- PROVED (def)
def ADT.decidesReal (t : ADT n) (S : Set (Fin n → ℝ)) : Prop       -- PROVED (def)
/-- Element distinctness as a set of real points. -/
def distinctSet (n : ℕ) : Set (Fin n → ℝ)                          -- PROVED (def)
noncomputable def numComponents (S : Set (Fin n → ℝ)) : ℕ          -- PROVED (def)

theorem numComponents_eq_one_of_isPreconnected {S : Set (Fin n → ℝ)}
    (hne : S.Nonempty) (hpre : IsPreconnected S) : numComponents S = 1         -- PROVED

/-- `numComponents (distinctSet n) = n!` — `n!` orderings. -/
def elementDistinctComponents (n : ℕ) : Prop                                   -- PROVED (Sectors.lean)
theorem elementDistinctComponents_zero : elementDistinctComponents 0           -- PROVED
theorem elementDistinctComponents_one : elementDistinctComponents 1            -- PROVED

/-! ---- M1, `Bound.lean` (the bound and the steps that are proved) ---- -/

/-- Ben-Or 1983 with Milnor–Thom: `height ≥ c · log #components`, `c = c d`. -/
def componentBound (d : ℕ) : Prop                                             -- STATED-ONLY
def BenOrBound : Prop := ∀ d : ℕ, componentBound d                            -- STATED-ONLY
/-- `Ω(log n!)` for distinctness at fixed degree. -/
def BenOrDistinctness (d : ℕ) : Prop                                          -- STATED-ONLY
def ElementDistinctHeightBound (d : ℕ) : Prop                                 -- STATED-ONLY

theorem componentBound_distinctness (d : ℕ) (hb : componentBound d)
    (hcomp : ∀ n : ℕ, elementDistinctComponents n) : BenOrDistinctness d        -- PROVED
theorem log_factorial_ge_sixteenth (n : ℕ) :
    (n : ℝ) * Real.log n / 16 ≤ Real.log (n.factorial : ℝ)                      -- PROVED
theorem elementDistinctHeightBound_of_distinctness (d : ℕ) (h : BenOrDistinctness d) :
    ElementDistinctHeightBound d                                                -- PROVED
theorem benOrBound_distinctness (h : BenOrBound)
    (hcomp : ∀ n : ℕ, elementDistinctComponents n) : ∀ d : ℕ, BenOrDistinctness d -- PROVED
theorem elementDistinctHeightBound_of_benOrBound (d : ℕ) (h : BenOrBound)
    (hcomp : ∀ n : ℕ, elementDistinctComponents n) :
    ElementDistinctHeightBound d                                                -- PROVED

/-! ---- M1, `Witness.lean` (non-vacuity of the semantics) ---- -/

/-- One test, `-(∏ i < j, (X i - X j) ^ 2)`, decides element distinctness. -/
theorem exists_decidesReal_distinct (n : ℕ) :
    ∃ t : ADT n, t.degreeLe (n * (n - 1)) ∧ t.decidesReal (distinctSet n)       -- PROVED
theorem halfLineTree_decidesReal :
    halfLineTree.decidesReal {x : Fin 1 → ℝ | 0 ≤ x 0}                           -- PROVED

theorem distinctSet_nonempty (n : ℕ) : (distinctSet n).Nonempty                -- PROVED
theorem distinctSet_ne_univ {n : ℕ} (hn : 2 ≤ n) : distinctSet n ≠ Set.univ     -- PROVED
theorem leaf_not_decidesReal_distinct {n : ℕ} (hn : 2 ≤ n) (b : Bool) :
    ¬ (ADT.leaf b).decidesReal (distinctSet n)                                   -- PROVED
theorem distinctnessTree_decides (n : ℕ) :
    (distinctnessTree n).decides {x : Fin n → ℚ | Function.Injective x}          -- PROVED

/-! ---- M1, `Sectors.lean` (the component count, proved) ---- -/

/-- The sector of a permutation: the points whose increasing order is `σ`. -/
def sector (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ)                          -- PROVED (def)
theorem sector_convex (σ) : Convex ℝ (sector σ)                                 -- PROVED
theorem sector_isOpen (σ) : IsOpen (sector σ)                                   -- PROVED
theorem sector_eq_univ_of_le_one (hn : n ≤ 1) (σ) : sector σ = Set.univ        -- PROVED
theorem sectors_disjoint {σ τ} (h : σ ≠ τ) : Disjoint (sector σ) (sector τ)     -- PROVED
theorem distinctSet_eq_iUnion (n) : distinctSet n = ⋃ σ, sector σ               -- PROVED

/-- A sector as a subset of the subspace `↥(distinctSet n)`. -/
def sectorIn (σ) : Set ↥(distinctSet n)                                         -- PROVED (def)
theorem isOpen_sectorIn (σ) : IsOpen (sectorIn σ)                               -- PROVED
theorem isClosed_sectorIn (σ) : IsClosed (sectorIn σ)                           -- PROVED
theorem isClopen_sectorIn (σ) : IsClopen (sectorIn σ)                           -- PROVED
theorem isConnected_sectorIn (σ) : IsConnected (sectorIn σ)                     -- PROVED
theorem iUnion_sectorIn (n) : ⋃ σ, sectorIn σ = Set.univ                       -- PROVED
theorem pairwiseDisjoint_sectorIn (n) {σ τ} (h : σ ≠ τ) :
    Disjoint (sectorIn σ) (sectorIn τ)                                          -- PROVED

/-- Components of the distinctness set = orderings of the coordinates. -/
noncomputable def componentsEquivPerm (n) :
    ConnectedComponents ↥(distinctSet n) ≃ Equiv.Perm (Fin n)                   -- PROVED (def)
theorem componentsEquivPerm_mk {σ} {x} (hx : x ∈ sectorIn σ) :
    componentsEquivPerm n (ConnectedComponents.mk x) = σ                        -- PROVED
theorem numComponents_distinctSet (n : ℕ) :
    Nat.card (ConnectedComponents ↥(distinctSet n)) = Nat.factorial n           -- PROVED

theorem forall_elementDistinctComponents : ∀ n : ℕ, elementDistinctComponents n -- PROVED
theorem benOrBound_benOrDistinctness (h : BenOrBound) :
    ∀ d : ℕ, BenOrDistinctness d                                                -- PROVED
theorem benOrBound_elementDistinctHeightBound (d : ℕ) (h : BenOrBound) :
    ElementDistinctHeightBound d                                                -- PROVED

end SortBounds.Projects.BenOr
```

## Milestones

* **M0** the `ADT` datatype, `height`, `decides`, and the leaf-counting corollary
  (`b = 2`, reuse `Core.Branching`'s idea). Everything must compile.
* **M1** the `BenOrBound` specialised to element distinctness.  The component count
  `n!` — the mathematical heart, `numComponents (distinctSet n) = n!` — is **proved**
  (`Sectors.lean`, no algebraic geometry needed: the ordering sectors are the
  components).  Still unproved: `componentBound d` itself (Ben-Or 1983 with
  Milnor–Thom), stated and cited.  M1 also carries the lane's **non-vacuity**
  obligation: `decidesReal` has to be satisfiable for the sets the bound quantifies
  over, or the `componentBound` implications hold for want of a tree.  `Witness.lean`
  supplies that witness (`exists_decidesReal_distinct`).
* **M2** *gated*: the bound itself. Not committed.

**Deliverable = a precise, compiled statement of the theorem plus its model.**
That alone is useful: it makes "the model changes the answer" machine-readable.

## Rules

Own only `SortBounds/Projects/BenOr/`. `lake env lean`. No `sorry`. A `def
BenOrBound : Prop := …` with no proof is the correct shape for the unproved part.

## Prior art

Ben-Or 1983 (STOC, topological method); Milnor–Thom component bounds. No
formalization found.

## M1 target: `n!` connected components of the distinctness set (opened 2026-11-11, **done**)

Ben-Or's bound reads off the number of connected components of the set being decided;
for element distinctness that number is `n!`, which is *why* the bound gives `Ω(n log n)`
there even though an algebraic test has three outcomes rather than two.  The model and
the statements are already in this lane; this is the missing mathematical ingredient, and
it is provable without any algebraic geometry.  The sketch below was the contract; the
file `Sectors.lean` proves all of it (the name `sector_open` came out as
`sector_isOpen`, matching the rest of the repository; everything else is verbatim, with
`n` implicit where the sketch leaves it implicit):

```lean
/-- The **sector** of a permutation: the points whose increasing order is `σ`. -/
def sector [LinearOrder α] (σ : Equiv.Perm (Fin n)) : Set (Fin n → α)
  := {x | ∀ k l : Fin n, k < l → x (σ k) < x (σ l)}

theorem sector_convex (σ) : Convex ℝ (sector σ)          -- an intersection of open half-spaces
theorem sector_open (σ) : IsOpen (sector σ)
theorem sectors_disjoint {σ τ} (h : σ ≠ τ) : Disjoint (sector σ) (sector τ)
theorem distinctSet_eq_iUnion : distinctSet n = ⋃ σ, sector σ

/-- **The distinctness set has exactly `n!` connected components.** -/
theorem numComponents_distinctSet (n : ℕ) :
    Nat.card (ConnectedComponents ↥(distinctSet n)) = Nat.factorial n
```

**Proof route (no paths needed), as carried out.** Each `sector σ` is open (a finite
intersection of half-spaces `{x | x i < x j}`), convex (same), and the sectors are
pairwise disjoint with union the distinctness set.  Inside the subspace `↥(distinctSet n)`,
each sector is therefore *clopen*: open by `sector_isOpen`, and closed because its
complement is the union of the other open sectors.  A clopen connected set is a connected
component, and `sector σ` is connected because it is convex.  So the components are in
bijection with `Equiv.Perm (Fin n)`, whose cardinality is `n!` — realised as the
equivalence `componentsEquivPerm`, with `componentsEquivPerm_mk` certifying that a point
of `sectorIn σ` lands in component `σ` (so the bijection is the intended one, not a junk
bijection between two finite types of equal size).  The single Mathlib input is
`ConnectedComponents.equivOfIsClopenOfIsConnected`; the uniqueness of the ordering of a
point is `Tuple.unique_monotone`, its existence `Tuple.sort`.

Edge cases: `n = 0, 1` need no case split (`sector_eq_univ_of_le_one`: there is no pair
`k < l`, so the one sector is everything), and the topology is the subtype topology of
`↥(distinctSet n)` throughout (`sectorIn`, `isOpen_sectorIn`, `isClosed_sectorIn`), with
`Nat.card` computed through the equivalence to `Equiv.Perm (Fin n)` so no
`Fintype (ConnectedComponents …)` instance is needed.

## Log

* 2026-11-11 — **M0 done** (`Basic.lean`): `ADT`, `ADT.height`, `ADT.numCells`,
  `ADT.run`, `ADT.decides`, `ADT.degreeLe`, and `ADT.card_cells_le`
  (`t.numCells ≤ 2 ^ t.height`).  Non-vacuity and degree checks:
  `halfLineTree_decides`, `halfLineTree_degreeLe`.  Validated with
  `lake env lean`; `#print axioms` gives only `propext, Classical.choice,
  Quot.sound`.
* 2026-11-11 — **M1 done** (`Components.lean`, `Bound.lean`).  *Modelling
  decision:* the component count lives over `ℝ`, not `ℚ` — `ℚ` is totally
  disconnected, so "`n!` components" is already false at `n = 1` over `ℚ`.  The
  trees keep the contract's `ℚ`-coefficient `MvPolynomial` tests; `ADT.runReal` /
  `ADT.decidesReal` read those coefficients at real points, and `ADT.run` /
  `ADT.decides` stay the rational semantics of the contract.
  Stated, not proved (`def … : Prop`, no `sorry`):
  `elementDistinctComponents n` := `numComponents (distinctSet n) = n!`,
  `componentBound d`, `BenOrBound`, `BenOrDistinctness d`,
  `ElementDistinctHeightBound d`.  Proved: `numComponents_eq_one_of_isPreconnected`,
  `elementDistinctComponents_zero`, `elementDistinctComponents_one`,
  `componentBound_distinctness` (`componentBound d` + `n!` components ⇒
  `Ω(log n!)`), `log_factorial_ge_sixteenth` (`n log n / 16 ≤ log n!`, all `n`),
  `elementDistinctHeightBound_of_distinctness`, `benOrBound_distinctness`, and
  `elementDistinctHeightBound_of_benOrBound` (`BenOrBound` + `n!` components ⇒
  `Ω(n log n)` for element distinctness at every fixed degree).
* 2026-11-11 — **M1 non-vacuity** (`Witness.lean`).  The gap: nothing showed
  `t.decidesReal (distinctSet n)` is satisfiable, so every `componentBound` /
  `BenOrDistinctness` / `ElementDistinctHeightBound` statement was potentially
  vacuous in its `decidesReal` hypothesis.  Proved

  ```lean
  theorem exists_decidesReal_distinct (n : ℕ) :
      ∃ t : ADT n, t.degreeLe (n * (n - 1)) ∧ t.decidesReal (distinctSet n)
  ```

  with the one-test tree
  `.node (-(∏ p ∈ distinctPairs n, (X p.1 - X p.2) ^ 2)) (.leaf true) (.leaf false)`:
  the test is `-(∏ i < j, (x i - x j) ^ 2)`, which is negative exactly on the
  distinct points (`prod_sq_nonneg`, `prod_sq_eq_zero_iff`, `injective_iff_pairs`,
  assembled in `distinctnessPoly_eval₂_neg_iff`).  Degree bookkeeping
  (`totalDegree_distinctnessPoly_le`, bound `n * (n - 1)`): `n.choose 2` factors
  of total degree `2` (`Finset.card_product_filter_lt`, `totalDegree_pow`,
  `totalDegree_sub`, `totalDegree_finsetProd`) and `2 * n.choose 2 = n * (n - 1)`
  (`two_mul_choose_two`).  The sign argument runs over an arbitrary
  `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`, so the *same* tree decides
  distinctness in the rational semantics too (`distinctnessTree_decides`), and
  the real half-line witness `halfLineTree_decidesReal` closes the other
  semantics (its rational counterpart `halfLineTree_decides` was already M0).
  The witness has height `1`, so it is no threat to the bound: it is available
  only at degree `n * (n - 1)`, and a statement fixing `d` excludes it once
  `n * (n - 1) > d` — which is exactly why `d` is fixed in `componentBound`.
  Non-degeneracy of the witness: `distinctSet_nonempty` and `distinctSet_ne_univ`
  (`distinctSet n` is neither empty nor everything for `n ≥ 2`), hence
  `leaf_not_decidesReal_distinct` — a tree with no test cannot meet the
  hypothesis, so the witness really does test.
  `#print axioms`: `propext, Classical.choice, Quot.sound`.
* 2026-11-11 — Contract block above now records the M1 interface verbatim with
  per-signature `PROVED` / `STATED-ONLY` labels, so the unproved part of the
  lane is a finite, visible list: `elementDistinctComponents`, `componentBound`,
  `BenOrBound`, `BenOrDistinctness`, `ElementDistinctHeightBound`.
* 2026-11-11 — Not attempted, by design: the two algebraic-geometry inputs
  (`elementDistinctComponents`, i.e. `n!` convex ordering regions separated by
  `sign (x i - x j)`; and `componentBound`, Ben-Or 1983 with Milnor–Thom
  component bounds).  `log_factorial_ge_sixteenth` belongs in
  `SortBounds/Comparison/Stirling.lean` — outside this lane's write scope; the
  integrator may move it.
* 2026-11-11 — **M1 component count PROVED** (`Sectors.lean`).  The statement
  `elementDistinctComponents` is no longer a `Prop` with no proof:

  ```lean
  theorem numComponents_distinctSet (n : ℕ) :
      Nat.card (ConnectedComponents ↥(distinctSet n)) = Nat.factorial n
  ```

  The route is the one sketched under "M1 target" above and needs no algebraic
  geometry.  `sector σ = {x | ∀ k l, k < l → x (σ k) < x (σ l)}`;
  `sector_convex` (intersection of half-spaces `{x | x (σ k) < x (σ l)}`, i.e. of
  `LinearMap.proj` preimages of `Iio 0`), `sector_isOpen` (`isOpen_lt` +
  `isOpen_iInter_of_finite`), `sectors_disjoint` and
  `distinctSet_eq_iUnion` (`distinctSet n = ⋃ σ, sector σ`).  Uniqueness of the
  ordering of an injective point is `eq_of_mem_sector`, from
  `Tuple.unique_monotone`; existence is `sort_mem_sector`, from `Tuple.sort` /
  `Tuple.monotone_sort` plus injectivity.  Inside the subspace `↥(distinctSet n)`
  the sector becomes `sectorIn σ`: `isOpen_sectorIn` (preimage under
  `Subtype.val`), `isClosed_sectorIn` (complement = union of the other open
  sectors), `isConnected_sectorIn` (image of the convex `sector σ`, which is
  `PreconnectedSpace`), `iUnion_sectorIn`, `pairwiseDisjoint_sectorIn` — the four
  hypotheses of `ConnectedComponents.equivOfIsClopenOfIsConnected`, which yields

  ```lean
  noncomputable def componentsEquivPerm (n : ℕ) :
      ConnectedComponents ↥(distinctSet n) ≃ Equiv.Perm (Fin n)
  theorem componentsEquivPerm_mk {σ} {x} (hx : x ∈ sectorIn σ) :
      componentsEquivPerm n (ConnectedComponents.mk x) = σ
  ```

  (`componentsEquivPerm_mk` pins the bijection to the intended one: sector `σ` ↦
  component `σ`; every sector is inhabited by `sector_nonempty`, so no permutation
  indexes a phantom component).  `Nat.card` then comes from
  `Nat.card_congr` + `Fintype.card_perm`, so no `Fintype (ConnectedComponents …)`
  instance is needed.  Degenerate sizes need no case split:
  `sector_eq_univ_of_le_one` (`n ≤ 1` ⇒ the one sector is all of `distinctSet n`),
  and `numComponents_distinctSet 4` evaluates to `24`, `… 0` to `1`.
  `#print axioms`: `propext, Classical.choice, Quot.sound`.
* 2026-11-11 — Statement-level consequence (`Sectors.lean`): the `hcomp`
  hypothesis of `componentBound_distinctness`, `benOrBound_distinctness` and
  `elementDistinctHeightBound_of_benOrBound` can now be discharged, and
  `Sectors.lean` states the improved forms

  ```lean
  theorem forall_elementDistinctComponents : ∀ n : ℕ, elementDistinctComponents n
  theorem benOrBound_benOrDistinctness (h : BenOrBound) : ∀ d, BenOrDistinctness d
  theorem benOrBound_elementDistinctHeightBound (d : ℕ) (h : BenOrBound) :
      ElementDistinctHeightBound d
  ```

  So the *only* unproved input of the lane is now Ben-Or's own topological bound
  `componentBound`/`BenOrBound`; the model, the witnesses, the component count,
  the Stirling arithmetic and the reductions are all checked.  The landed
  signatures of the earlier files were **not** changed (their `hcomp` hypothesis
  stays, with the improved versions beside them).
* 2026-11-11 — The earlier log entry "not attempted, by design" is superseded for
  the component count (only `componentBound` remains un-attempted).  Prose in
  `Components.lean` and `Bound.lean` that said the component count is "not proved"
  was corrected; no definition or theorem statement was touched.
