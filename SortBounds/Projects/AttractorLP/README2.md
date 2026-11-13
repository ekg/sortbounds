# Lane 4 — LPdelta: `LP* ≥ δ`, the inequality that ties the programme together

**Why.** `γ/LP* ≤ γ/δ` because `LP* ≥ δ`.  So the LP gap **cannot exceed** the `δ`-gap: on every
measurement `γ − ⌈δ⌉ ≤ 3`, which would force the LP gap to `1` at scale.  That is the single most
consequential structural fact in the whole programme (`docs/research/lp-gap-growth.md` §3), and
right now it is prose.  Kernel-check it.

`LP*` is not a Lean object here (no simplex), so state it in the form that is equivalent for every
feasible point — the counting bound with **weights**:

```lean
theorem deltaQ_le_primalValue {s : List α} {x : Fin s.length → ℚ}
    (hx : PrimalFeasible s x) : deltaQ s ≤ ∑ p, x p
```

i.e. *every primal-feasible fractional cover has value at least `δ`*.  Instantiated at the `15/11`
witness this gives `δ ≤ 11/5` (true: `δ = 2`), and combined with `lp13_primal`/`lp13_dual` it shows
the LP optimum is squeezed from below by KNP's bound — which is why the gap is small in the first
place.

## Where to write

New file `SortBounds/Projects/AttractorLP/DeltaBound.lean` (import `Gap`, `Witness`).
**Do not modify `Gap.lean` or `Witness.lean`** — they are committed and audited.  If you need a
lemma from them, restate it locally or ask.

## The proof (unweighted version is already in the repo; this is the weighted one)

For each `j` with `1 ≤ j ≤ s.length`:

1. `d_j = #(distinctFactors s j)`.
2. Each `f ∈ distinctFactors s j` is in `factorUniverse s` (every nonempty factor is), so
   `1 ≤ ∑ p ∈ coverageSet s f, x p` by `hx`.
3. Hence `d_j ≤ ∑ f ∈ distinctFactors s j, ∑ p ∈ coverageSet s f, x p`.
4. Swap the sums: `= ∑ p, x p * #{f ∈ distinctFactors s j : p ∈ coverageSet s f}`.
5. **The counting step**: `#{f ∈ distinctFactors s j : p ∈ coverageSet s f} ≤ j`, because such an
   `f` is determined by an offset `d < j` via `f = (s.drop (p − d)).take j` (this is
   `exists_cover_of_isAttractorK`'s conclusion, or `mem_coverageSet`).  Use
   `Finset.card_le_card` against `Finset.range j` under the map `f ↦ (j - ?)` — or, more
   robustly, build an injection into `Finset.range j` (mirror
   `Repetitiveness.distinctFactors_card_le_mul_attractor`, which does the unweighted version of
   exactly this step).
6. Since `x p ≥ 0`, `∑ p, x p * c_p ≤ ∑ p, x p * j = j * ∑ p, x p`.
7. Therefore `d_j / j ≤ ∑ p, x p` for every `j ∈ Icc 1 n`, so the supremum `deltaQ s` is `≤ ∑ x`
   (`Finset.sup'_le`).

In Lean the cleanest route for step 4–6 is a **single application of a weighted-sum lemma**:
prove `∑ f ∈ A, ∑ p ∈ coverageSet s f, x p = ∑ p, x p * (A.filter (fun f => p ∈ coverageSet s f)).card`
via `Finset.sum_comm` and `Finset.sum_ite_mem`/`Finset.sum_filter`, then bound the inner cardinal.
If that lemma is painful, an acceptable **fallback** is to prove it for the specific witness
universe only (`s = lp13`) by `decide`/`norm_num` over the 13 positions — that still gives
`δ(lp13) ≤ 11/5` concretely, but say clearly in the report that the general statement was not
reached.

## Milestones

* **M0** `factor_card_le_primal_sum {j} (hj : 1 ≤ j) (hj' : j ≤ s.length) (hx) :
    (distinctFactors s j).card ≤ j * ∑ p, x p` — steps 1–6 for a fixed `j`.
* **M1** `deltaQ_le_primalValue` — `sup'_le` over `Icc 1 n` from M0.
* **M2** the instance corollary on the `15/11` witness: `deltaQ lp13 ≤ 11/5`.

## Rules

Own only `SortBounds/Projects/AttractorLP/DeltaBound.lean` (+ a `Log` entry here).
`lake env lean` only; oleans to `/tmp`; no git; no `lake build`.  No
`sorry`/`admit`/`axiom`/`native_decide`.  Read `Gap.lean` (definitions of `PrimalFeasible`,
`coverageSet`, `factorUniverse`, `weak_duality`) and `Lane 3`'s style before writing.

**Watch the trap:** `PrimalFeasible` quantifies over `factorUniverse s`, so step 2 needs
`f ∈ distinctFactors s j → f ∈ factorUniverse s`, which requires `j ≥ 1` and `j ≤ s.length`.
State `hj`/`hj'` explicitly; do not silently strengthen or weaken the hypotheses.

## Log

* **M0, M1, M2 landed** (`DeltaBound.lean`; `lake env lean` on the file is silent, and
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]` only — no `decide`, no
  `sorry`, no `native_decide`).
  * `distinctFactors_subset_factorUniverse {s} {j} (hj : 1 ≤ j) :
    distinctFactors s j ⊆ factorUniverse s` — step 2 (a length-`j` factor is a row).
  * `card_filter_coverageSet_le (s) (j) (p) :
    ((distinctFactors s j).filter (fun f => p ∈ coverageSet s f)).card ≤ j` — **step 5, the
    crux**, by the technique of `Repetitiveness.distinctFactors_card_le_mul_attractor`
    (inclusion into an explicit image of `Finset.range j`, no choice, no injectivity).
  * `sum_distinctFactors_coverage (s) (j) (x) : Σ_{f ∈ D_j} Σ_{p ∈ C(f)} x p =
    Σ_p x p · #{f ∈ D_j : p ∈ C(f)}` — step 4, the weighted double sum (`Finset.sum_comm`
    then `Finset.sum_filter`/`sum_const`; the `ℚ` analogue of `weak_duality`'s swap).
  * `factor_card_le_primal_sum (hx : PrimalFeasible s x) (hj : 1 ≤ j) :
    ((distinctFactors s j).card : ℚ) ≤ (j : ℚ) * Σ p, x p` — **M0**, steps 1–6.
  * `deltaQ_le_primalValue (hx : PrimalFeasible s x) : deltaQ s ≤ Σ p, x p` — **M1**, i.e.
    `δ ≤ LP*`: `Finset.sup'_le` over `Icc 1 n` from M0.  General in `s : List α`.
  * `deltaQ_lp13_le : deltaQ lp13 ≤ 11 / 5` — **M2**, via `lp13_primal`.  Not tight, and not
    meant to be: `decide` on the `ℕ`-valued `substringComplexity lp13` gives `δ(lp13) = 2`, so
    the witness chain reads `δ = 2 ≤ LP* = 11/5 < γ = 3` — the LP gap `15/11` is smaller than
    the `δ`-gap would allow at this size, as `docs/research/lp-gap-growth.md` §3 predicts.
* **Contract deviation (one, deliberate, small).**  The brief's M0 also required the
  hypothesis `hj' : j ≤ s.length` and its trap note says step 2 needs both `j ≥ 1` *and*
  `j ≤ s.length` — but the upper bound is **redundant**: `mem_distinctFactors` already yields
  a start `i` with `i + j ≤ s.length`, which is all `mem_factorUniverse` needs.  Only `1 ≤ j`
  is assumed, matching the side condition of the unweighted
  `distinctFactors_card_le_mul_attractor` in `Repetitiveness.Attractor` (whose header records
  the same `k` vs `k ≤ n` decision).  `1 ≤ j` itself *is* essential: at `j = 0`,
  `distinctFactors s 0 = {[]}` and `[] ∉ factorUniverse s`, so the bound `d_0 ≤ 0` is false.
  Nothing else in the statement set was changed.
* **Non-vacuity of M1.**  `coverageSet s f` is nonempty for every `f ∈ factorUniverse s`
  (`mem_factorUniverse` gives the occurrence, `mem_coverageSet` puts its start in the column),
  so `x ≡ 1` is primal feasible and M1 instantiates to `deltaQ s ≤ s.length` for every text.
  Both were checked in a scratch file and deliberately **not** committed: they are not
  milestones of this lane and would widen the diff.
