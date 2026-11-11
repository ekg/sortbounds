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

Everything below is *in the environment today* and compiles. The label says what
is established about it: `PROVED` = there is a proof in this lane; `STATED-ONLY`
= the signature is a definition whose *proposition* nothing here proves (it is
stated, cited, and used as a hypothesis — never `sorry`-ed).

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
def elementDistinctComponents (n : ℕ) : Prop                                   -- STATED-ONLY
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

theorem distinctnessTree_decides (n : ℕ) :
    (distinctnessTree n).decides {x : Fin n → ℚ | Function.Injective x}          -- PROVED

end SortBounds.Projects.BenOr
```

## Milestones

* **M0** the `ADT` datatype, `height`, `decides`, and the leaf-counting corollary
  (`b = 2`, reuse `Core.Branching`'s idea). Everything must compile.
* **M1** *gated*: `BenOrBound` specialised to element distinctness, i.e. the
  statement that `{x | all xᵢ distinct}` has `n!` connected components. Real
  algebraic geometry; state it, cite Ben-Or 1983, do not attempt a proof.
  M1 also carries the lane's **non-vacuity** obligation: `decidesReal` has to be
  satisfiable for the sets the bound quantifies over, or the `componentBound`
  implications hold for want of a tree. `Witness.lean` supplies that witness
  (`exists_decidesReal_distinct`).
* **M2** *gated*: the bound itself. Not committed.

**Deliverable = a precise, compiled statement of the theorem plus its model.**
That alone is useful: it makes "the model changes the answer" machine-readable.

## Rules

Own only `SortBounds/Projects/BenOr/`. `lake env lean`. No `sorry`. A `def
BenOrBound : Prop := …` with no proof is the correct shape for the unproved part.

## Prior art

Ben-Or 1983 (STOC, topological method); Milnor–Thom component bounds. No
formalization found.

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
