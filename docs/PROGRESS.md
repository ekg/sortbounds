# PROGRESS

Single source of truth for status. Only the integrator edits this file; lanes
update the `## Log` of their own `README.md`.

Status values: `DONE` · `ACTIVE` · `QUEUED` · `BLOCKED` · `SHELVED` (with reason).

## Where we are

The comparison-model result is **settled and frozen**: `Ω(n log n)` for the worst
case over inputs, the average case, arbitrary value types, plus a matching
`O(n log n)` upper bound. Frozen means: no more work on restating it, no constant
chasing. It is the worked example for `SortBounds/Core`.

The question now is not "is the bound true" but **"what does the bound say about
other models"** — every open lane is about a model where the answer changes.

## Lanes

| Lane | Question | Target theorem | Status | Milestone |
| --- | --- | --- | --- | --- |
| `Core` | bits per probe | `card_le_pow_of_prefixFree`, `logb_le_of_le_pow` | **DONE** | M0 |
| `Comparison` | comparison sorts | `exists_input_cost_ge_quarter`, `avg_cost_ge_log2_factorial` | **DONE** | frozen |
| `Instances` | where the bound breaks | `radixSort_keys_congr`, `msortCount_le` | **DONE** | frozen |
| `FordJohnson` | exact comparison counts, upper bound | `fj_cast_count`, `fj_take_count` | **ACTIVE** | M1/M3 |
| `SN` | exact `S(n)`, both bounds | `exists_correct_tree`, `S_eq_*` table | **ACTIVE** | M0/M1 |
| `XY` | sorting `X+Y` | `xy_*` model + bounds | **ACTIVE** | M0 |
| `BenOr` | algebraic decision trees | statement + model | **ACTIVE** | M0 |
| `SAIS` | suffix arrays, cost model | `…` | **QUEUED** | — |

## Decisions (and why)

1. **Freeze the lower bound.** It is done three times over elsewhere; more
   restatements add nothing. See `docs/PRIOR-ART.md`.
2. **One project, directories per lane.** Mathlib oleans are 7.6 GB; per-lane
   Lake packages would duplicate that. Details in `docs/STRUCTURE.md`.
3. **`Core` first, instances second.** The reusable object is the
   branching-factor counting lemma, not the Ω statement.
4. **Prior art checked before each lane starts.** Two earlier ideas died this
   way: the 0-1 principle + verified sorting networks (Coq: arXiv 2203.01579,
   1502.05209, 2012.04400; Lean: girving/aks formalises AKS), and verified SA-IS
   correctness (Isabelle AFP `SuffixArray`, 2024). Only the *cost model* for
   suffix arrays is unclaimed.
5. **Lanes are allowed to end at M1.** Reaching a weaker true theorem is a
   success; a `sorry` is not.

## Milestone vocabulary

* `M0` — definitions and the target statement compiles (possibly with the easy
  direction only). No `sorry`.
* `M1` — the main theorem proved for the small/central case.
* `M2` — the general theorem.
* `M3` — the result that would be new to the literature (gated; may not land).

## Blockers and dependencies

* `SN` M2 (optimal trees for `n = 6..11`) **depends on** `FordJohnson` M1: the
  merge-insertion algorithm is the cheapest way to *construct* the optimal trees.
  Until then `SN` works on `M0`/`M1` (which are independent).
* `SN` M3 (`S 12 = 30`, the first case where `⌈log₂ 12!⌉ = 29 < 30`) needs a
  genuine adversary/entropy argument, not just counting. Research-level.
* `XY` M2+ (Fredman's `O(n²)` comparison algorithm) is research-level.
* `BenOr` M1+ (component count of the distinctness set) needs real algebraic
  geometry; `M0` only is the committed deliverable.
* `SAIS` is queued behind `XY`, which will exercise the same weighted cost model.

## Changelog

| Date | Change |
| --- | --- |
| 2026-11-09 | Repo restructured (`Core`/`Comparison`/`Instances`/`Projects`); `Core.Branching` landed; four lanes opened. |
| 2026-11-09 | Initial development: comparison model, Ω(n log n) (worst/average/any value type), radix, counted merge sort. |
