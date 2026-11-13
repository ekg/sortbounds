# Lane 3 — AttractorLP: the integrality gap `15/11` as a theorem

**Why.** `docs/research/lp-gap.md` reports the headline `γ/LP* = 15/11` at `n = 13` as a
*computation* (`tools/gap/`, exact rational simplex, exhaustive to `n ≤ 16`). The maximum is a
single instance with a **finite certificate**: an integral attractor of size 3, a primal feasible
`x` with `Σx = 11/5`, and a dual feasible `y` with `Σy = 11/5`. Weak duality then pins `LP* = 11/5`
without any simplex code, and `3/(11/5) = 15/11` is arithmetic. So the claim "the attractor LP is
not integral; the gap is at least `15/11`" is provable in Lean in ~200 lines, and nobody has
published an integrality-gap statement for string attractors.

This lane produces the first *kernel-checked* integrality gap for the attractor LP.

## The witness (verbatim from `lp-gap.md` §"The maximum over all binary strings")

```
s = "0110101101110"            n = 13
γ = 3                          attractor positions {3, 8, 9}
x: 3 ↦ 1/5, 4 ↦ 1/5, 5 ↦ 3/5, 8 ↦ 1/5, 9 ↦ 2/5, 10 ↦ 3/5,  x(p) = 0 otherwise,  Σx = 11/5
y: "0" ↦ 1/5, "11" ↦ 1/5, "110" ↦ 1/5, "1101" ↦ 1/5,
   "011010" ↦ 2/5, "10110" ↦ 2/5, "111" ↦ 3/5,   y(f) = 0 otherwise,  Σy = 11/5
```

`C(f)` = the set of positions crossing an *occurrence* of `f` (this is exactly the coverage notion
inside `IsAttractor`, so define it from `factorOcc` rather than anew).

## Contract — `SortBounds/Projects/AttractorLP/Gap.lean`

```lean
namespace SortBounds.Projects.AttractorLP

open SortBounds.Projects.Repetitiveness

variable {α : Type*} [DecidableEq α]

/-- Positions crossing some occurrence of `f` (the LP column of the factor `f`). -/
def coverageSet (s : List α) (f : List α) : Finset (Fin s.length)

/-- The factor universe: all nonempty factors of `s`. -/
def factorUniverse (s : List α) : Finset (List α)

/-- (P) `min Σ_p x_p` s.t. every factor is covered with weight ≥ 1, `x ≥ 0`. -/
def PrimalFeasible (s : List α) (x : Fin s.length → ℚ) : Prop

/-- (D) `max Σ_f y_f` s.t. every position carries weight ≤ 1, `y ≥ 0`. -/
def DualFeasible (s : List α) (y : List α → ℚ) : Prop

/-- **Weak duality**, elementarily (no LP theory): swapping the two sums and using
`Σ_{p ∈ C(f)} x_p ≥ 1` and `Σ_{f ∋ p} y_f ≤ 1`. -/
theorem weak_duality {s : List α} {x : Fin s.length → ℚ} {y : List α → ℚ}
    (hx : PrimalFeasible s x) (hy : DualFeasible s y) :
    (∑ f ∈ factorUniverse s, y f) ≤ ∑ p, x p

end SortBounds.Projects.AttractorLP
```

and, in `SortBounds/Projects/AttractorLP/Witness.lean`:

```lean
def lp13 : List Bool := "0110101101110" as a List Bool     -- 13 characters

theorem lp13_attractor :
    IsAttractor lp13 {⟨3, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩}
theorem lp13_gamma : minAttractorSize lp13 = 3
  -- `≤ 3` from the attractor above; `≥ 3` by `decide` over all subsets of size ≤ 2
  -- (`isAttractor_iff_check` gives decidability; 91 candidate subsets, no `native_decide`)
theorem lp13_primal : ∃ x, PrimalFeasible lp13 x ∧ ∑ p, x p = 11 / 5
theorem lp13_dual : ∃ y, DualFeasible lp13 y ∧ ∑ f ∈ factorUniverse lp13, y f = 11 / 5

/-- **The theorem**: the attractor LP has integrality gap at least `15/11`, and exactly `15/11`
on this instance. -/
theorem lp13_gap :
    minAttractorSize lp13 = 3 ∧ (11 / 5 : ℚ) < 3 ∧ (3 : ℚ) / (11 / 5) = 15 / 11
```

## Milestones

* **M0** `coverageSet`, `factorUniverse`, and the equivalence "`Γ` is an attractor iff every
  factor in `factorUniverse` has its coverage set meeting `Γ`" (should be cheap from `IsAttractor`
  and `mem_distinctFactors`; if it is *not* cheap, say so and state only what you need).
* **M1** `PrimalFeasible`, `DualFeasible` (state them over `factorUniverse s` so the sums are
  finite; both must be `Prop`-valued and decidably checkable at a concrete `x`, `y`).
* **M2** `weak_duality` — the only real proof. Suggested route: bound `Σ_f y_f` by
  `Σ_f y_f (Σ_{p∈C(f)} x_p)` using `hx`, rewrite the double sum as `Σ_p x_p (Σ_{f ∋ p} y_f)`
  (`Finset.sum_comm` with the indicator), then use `hy`. All terms are `ℚ`.
* **M3** `lp13_attractor` and `lp13_gamma`: the attractor by `isAttractor_iff_check` + `decide`;
  the lower bound `≥ 3` by `decide` over the 91 subsets of size ≤ 2 (use `Finset.univ.powerset`
  filtered by `card ≤ 2`, or `Finset.card_le_two` style reasoning on `Finset` subsets of `Fin 13`).
  **If enumerating subsets is painful, prove instead that three specific factors have pairwise
  disjoint coverage sets** (a packing of 3), which forces `γ ≥ 3` and is the same argument the
  Python side uses. State which route you took.
* **M4** `lp13_primal`, `lp13_dual` with the exact weights above; check feasibility with
  `decide` (this is a finite rational computation, ~13 positions × ~91 factors — if `decide` is
  too slow, use `norm_num` after `Finset.sum` simplification, or verify each position's dual load
  as a separate `norm_num` lemma and combine).
* **M5** `lp13_gap`.

## Rules

Own only `SortBounds/Projects/AttractorLP/`.  `lake env lean` only (oleans to `/tmp`); no git; no
`lake build`.  No `sorry`/`admit`/`axiom`/`native_decide`.  Read
`SortBounds/Projects/Repetitiveness/Basic.lean` (`IsAttractor`, `factorOcc`, `isAttractor_iff_check`)
and `Attractor.lean` (`minAttractorSize`, `minAttractorSize_le`) first and reuse everything.

**Do not report the gap as `> 15/11` or as a supremum over all strings** — this lane proves the
*instance* value and the *lower bound* `15/11` on the supremum.  The measured maximum over
`n ≤ 16` is `15/11` (`lp-gap.md`), but that is a computation, not this theorem.

## Log

### 2026-11-13 — lane done: M0–M5 all kernel-checked, `lake env lean` silent

**Files.** `SortBounds/Projects/AttractorLP/Gap.lean` (194 lines: the LP, M0, M2) and
`SortBounds/Projects/AttractorLP/Witness.lean` (252 lines: the `15/11` certificate, M3–M5).
Nothing else was touched; no `sorry`/`admit`/`axiom`/`native_decide`
(`grep -n "sorry\|admit\|native_decide\|^axiom"` over the directory is empty), and
`#print axioms` on every theorem below returns only `[propext, Classical.choice, Quot.sound]`.

**Exact final signatures** (all elaborated, `lake env lean` prints nothing):

```lean
-- Gap.lean
def coverageSet (s : List α) (f : List α) : Finset (Fin s.length)
theorem mem_coverageSet : p ∈ coverageSet s f ↔
    ∃ i j : ℕ, i ≤ ↑p ∧ ↑p < j ∧ j ≤ s.length ∧ factorOcc s i j = f
def factorUniverse (s : List α) : Finset (List α)
theorem mem_factorUniverse : f ∈ factorUniverse s ↔
    ∃ i j : ℕ, i < j ∧ j ≤ s.length ∧ factorOcc s i j = f
theorem factorUniverse_eq_biUnion (s : List α) :
    factorUniverse s = (Finset.Icc 1 s.length).biUnion (distinctFactors s)   -- rfl
theorem isAttractor_iff_coverageSet (Γ : Finset (Fin s.length)) :
    IsAttractor s Γ ↔ ∀ f ∈ factorUniverse s, (coverageSet s f ∩ Γ).Nonempty
def PrimalFeasible (s : List α) (x : Fin s.length → ℚ) : Prop
def DualFeasible (s : List α) (y : List α → ℚ) : Prop
theorem weak_duality {s : List α} {x : Fin s.length → ℚ} {y : List α → ℚ}
    (hx : PrimalFeasible s x) (hy : DualFeasible s y) :
    (∑ f ∈ factorUniverse s, y f) ≤ ∑ p, x p

-- Witness.lean  (all over `lp13 : List Bool := [false,true,true,false,true,false,true,true,
--                false,true,true,true,false]`, i.e. `0110101101110`)
def lp13 : List Bool
def lp13Attractor : Finset (Fin lp13.length)          -- {⟨3,_⟩, ⟨8,_⟩, ⟨9,_⟩}
theorem lp13Attractor_card : lp13Attractor.card = 3
theorem lp13_attractor : IsAttractor lp13 lp13Attractor
def lp13X (p : Fin lp13.length) : ℕ                   -- 5·x, the integral form
def lp13x (p : Fin lp13.length) : ℚ                   -- := lp13X p / 5
theorem lp13x_values : lp13x ⟨3,_⟩ = 1/5 ∧ lp13x ⟨4,_⟩ = 1/5 ∧ lp13x ⟨5,_⟩ = 3/5 ∧
    lp13x ⟨8,_⟩ = 1/5 ∧ lp13x ⟨9,_⟩ = 2/5 ∧ lp13x ⟨10,_⟩ = 3/5
theorem sum_lp13x (s : Finset (Fin lp13.length)) :
    ∑ p ∈ s, lp13x p = ↑(∑ p ∈ s, lp13X p) / 5
def lp13Y : List Bool → ℕ                             -- 5·y, the integral form
def lp13y (f : List Bool) : ℚ                         -- := lp13Y f / 5
theorem lp13y_values : lp13y [false] = 1/5 ∧ lp13y [true,true] = 1/5 ∧
    lp13y [true,true,false] = 1/5 ∧ lp13y [true,true,false,true] = 1/5 ∧
    lp13y [false,true,true,false,true,false] = 2/5 ∧
    lp13y [true,false,true,true,false] = 2/5 ∧ lp13y [true,true,true] = 3/5
theorem sum_lp13y (s : Finset (List Bool)) :
    ∑ f ∈ s, lp13y f = ↑(∑ f ∈ s, lp13Y f) / 5
theorem lp13_primalRows : ∀ f ∈ factorUniverse lp13,
    5 ≤ ∑ p ∈ coverageSet lp13 f, lp13X p                                    -- decide
theorem lp13_dualRows : ∀ p : Fin lp13.length,
    ∑ f ∈ (factorUniverse lp13).filter (fun f => p ∈ coverageSet lp13 f), lp13Y f ≤ 5  -- decide
theorem lp13_primal_total : ∑ p : Fin lp13.length, lp13X p = 11             -- decide
theorem lp13_dual_total : ∑ f ∈ factorUniverse lp13, lp13Y f = 11           -- decide
theorem lp13_primal : ∃ x : Fin lp13.length → ℚ,
    PrimalFeasible lp13 x ∧ ∑ p, x p = 11 / 5
theorem lp13_dual : ∃ y : List Bool → ℚ,
    DualFeasible lp13 y ∧ ∑ f ∈ factorUniverse lp13, y f = 11 / 5
def lp13Hard : Finset (List Bool)                      -- 6 factors: 0 110 111 1101 01011 10110
theorem lp13Hard_subset : lp13Hard ⊆ factorUniverse lp13                    -- decide
theorem lp13_no_two_positions : ∀ p q : Fin lp13.length,
    ¬ (∀ t ∈ lp13Hard, p ∈ coverageSet lp13 t ∨ q ∈ coverageSet lp13 t)     -- decide
theorem three_le_card_of_isAttractor {Γ : Finset (Fin lp13.length)}
    (hΓ : IsAttractor lp13 Γ) : 3 ≤ Γ.card
theorem lp13_gamma : minAttractorSize lp13 = 3
theorem lp13_lpValue {x : Fin lp13.length → ℚ} (hx : PrimalFeasible lp13 x) :
    11 / 5 ≤ ∑ p, x p                                  -- weak_duality against lp13_dual's `y`
theorem lp13_gap : minAttractorSize lp13 = 3 ∧ (11 / 5 : ℚ) < 3 ∧ (3 : ℚ) / (11 / 5) = 15 / 11
```

**Milestones: all done, nothing weakened.**

* **M0** — `coverageSet`, `factorUniverse` and the covering equivalence.  Cheaper than the brief
  feared: the equivalence falls out of `factorOcc` directly (`isAttractor_iff_coverageSet`), and
  the link to `mem_distinctFactors` is the `rfl` lemma `factorUniverse_eq_biUnion`.  Two
  membership lemmas (`mem_coverageSet`, `mem_factorUniverse`) are the only plumbing.  The empty
  word is excluded from the universe (it is `distinctFactors s 0`), which is forced: no position
  crosses it, so including `k = 0` would make the primal infeasible for a reason that has
  nothing to do with attractors.
* **M1** — `PrimalFeasible`, `DualFeasible`, both `Prop`-valued over the finite
  `factorUniverse`.  One deliberate narrowing: dual nonnegativity is asked on `factorUniverse`
  only, not on all of `List α` (`y` enters the objective and the loads nowhere else, so this is
  the same LP, and it is the only form that is finite).  `weak_duality` is therefore *stronger*
  than the contract's hypothesis, never weaker.
* **M2** — `weak_duality`: no LP theory, no simplex; the three-step chain in the docstring
  (`Σy ≤ Σ y·(Σ x) ≤ Σ_x x·(Σ y) ≤ Σ x`), with `Finset.sum_comm` doing the swap through an
  indicator (`Finset.sum_filter` both ways).
* **M3** — `lp13_attractor` (`isAttractor_iff_check` + `decide`, ~2 s) and `lp13_gamma`
  (`≤ 3` from that attractor, `≥ 3` from `three_le_card_of_isAttractor`).
* **M4** — `lp13_primal` and `lp13_dual`, exactly the weights of `lp-gap.md`, in the contract's
  existential form.
* **M5** — `lp13_gap`.  Plus one theorem the contract only gestured at: `lp13_lpValue`
  (`LP* = 11/5`, two-sided), which is what makes "`γ/LP* = 15/11`" a statement about the LP
  optimum rather than about two numbers that happen to be `11/5`.

**Routes taken where the contract offered one, and where it offered none.**

* **M3, first fallback (`3` pairwise disjoint coverage sets) is impossible here** — not "hard",
  *false*: enumerating all triples of the 61 factors in Python gives no triple with pairwise
  disjoint coverage sets (the largest packing has size `2`: `C("0") = {0,3,5,8,12}` and
  `C("11") = {1,2,6,7,9,10,11}`, which partition the text).  So a packing cannot give `γ ≥ 3`.
* **M3, route actually taken**: the contract's *fuller* option, a `decide` over position pairs,
  but with a 6-factor **hitting certificate** instead of all `91` subsets.  `lp13Hard` is a set
  of 6 factors that **no two positions jointly cover** (`lp13_no_two_positions`, a `decide` over
  the `13 × 13` position pairs, ~2 s); an attractor of size `≤ 2` must cover all six
  (`isAttractor_iff_coverageSet`), so `3 ≤ Γ.card` for every attractor.  This is strictly
  stronger than a packing and needs no exhaustive subset enumeration at all.  (The certificate
  was found by a min-hitting-set search in Python; 6 is its minimum size, and the statement
  "no two positions cover `lp13Hard`" is a Lean theorem, not a computation handed in from
  outside.)
* **M4, `decide` on `ℚ`: impossible, not merely slow.**  In this toolchain (`leanprover/lean4:
  v4.35.0-rc2`) `Rat.add` / `Rat.decEq` **do not reduce in the kernel** — even
  `example : (1/5 : ℚ) + 3/5 = 4/5 := by decide` fails with "reduction got stuck".  So both
  contracts' `decide` routes were unavailable and `norm_num` per row would have meant `61 + 13`
  hand-written goals.  Fallback taken (better than either): scale the witnesses by `5`,
  `lp13X = 5·x` and `lp13Y = 5·y`, which live in `ℕ` and *are* `decide`-able, decide the row
  conditions there (`lp13_primalRows`, `lp13_dualRows`, and the two totals), and transport back
  to `ℚ` by the two general lemmas `sum_lp13x`/`sum_lp13y` (`Finset.sum_div` + `Nat.cast_sum`).
  No statement weakened; both witnesses are literally the ones in `lp-gap.md`, and
  `lp13x_values`/`lp13y_values` state those values as theorems.  `Witness.lean` needs
  `set_option maxRecDepth 100000` for those `decide`s (the row conditions evaluate
  `coverageSet` for all 61 factors) — set at the top of the file, kernel-check, no
  `native_decide`.
* **One naming deviation**: `lp13_attractor` is stated as `IsAttractor lp13 lp13Attractor` with
  `lp13Attractor := {⟨3,_⟩, ⟨8,_⟩, ⟨9,_⟩}` (so `lp13Attractor_card : …card = 3` is available),
  rather than with the inline Finset literal.  Same statement up to definitional unfolding.

**`lake env lean` output: silent, both files.**

```
$ lake env lean SortBounds/Projects/AttractorLP/Gap.lean
                                   # no output
$ lake env lean SortBounds/Projects/AttractorLP/Witness.lean
…/Gap.olean does not exist         # only because Witness imports Gap and the repo build dir
                                   # has no olean for a lane file until the integrator builds
```
To check `Witness.lean` without writing oleans into the repo (lane rule), `Gap.olean` was built
to a `/tmp` mirror of `LEAN_PATH`, and the elaboration run against it is also silent:

```
$ lean -o /tmp/oleanroot/SortBounds/Projects/AttractorLP/Gap.olean …/Gap.lean      # silent
$ LEAN_PATH=/tmp/oleanroot:$LEAN_PATH lean …/Witness.lean                          # silent
$ … with -DwarningAsError=true                                                     # silent
```
Timings: `Gap.lean` ~7 s, `Witness.lean` ~16 s (both dominated by the `Mathlib` import).

**Integrator TODO.** Add `import SortBounds.Projects.AttractorLP.Gap` and
`import SortBounds.Projects.AttractorLP.Witness` to `SortBounds.lean` (the lane owns neither the
umbrella nor `docs/PROGRESS.md`), then `lake build` picks both up; nothing in the lane writes
oleans.

**The hardest step.**  Not `weak_duality` (the double-sum swap is `Finset.sum_comm` plus
`Finset.sum_filter` in the two directions, and it went through after one iteration), and not
`γ ≥ 3` (mechanical once the hitting certificate existed).  It was **M4**, and the reason is a
toolchain fact that the contract did not anticipate: `decide` cannot evaluate `ℚ` at all in Lean
`v4.35.0-rc2`, so *every* numeric claim had to be re-expressed in `ℕ` before the kernel could
see it.  Getting that right also forced the design of the witness functions
(`lp13x := lp13X/5`, so that the scaling is a general lemma instead of 74 case splits), which is
why no row sum in `Witness.lean` is hand-computed: the `norm_num` calls are only the two
`lp13*_values` lemmas (which *document* the witnesses), the two `Σ = 11/5` objectives, one
`(0 : ℚ) < 5`, and the final arithmetic of `lp13_gap`.

* Second-order note for whoever writes the *next* LP lane: `decide` over `ℕ` is fast here
  (~2 s for 2028 evaluations of `coverageSet`, i.e. a `61`-row and a `169`-pair condition), so
  the integer-scaling trick is cheap; but `ℚ`, `Int` and `Rat` are opaque to the kernel and any
  `decide` that touches them will fail rather than be slow.
