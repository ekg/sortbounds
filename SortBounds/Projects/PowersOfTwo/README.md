# Lane 7 — PowersOfTwo: an exact `γ` for the extremal family, proved

**The family.**  For `j ≥ 1` let `T_j` be the binary word of length `2^j` whose `i`-th symbol
(0-indexed) is `1` exactly when `i + 1` is a power of two:

```
T_1 = 11            T_2 = 1101            T_3 = 11010001
T_4 = 1101000100000001
```

Equivalently `1 1 0 1 000 1 0000000 1 0^15 1 …`: the zero-runs between consecutive `1`s have
lengths `0, 1, 3, 7, 15, …` (`= 2^k − 1`), so **every run length occurs exactly once**.

**What is measured (certified, both ends closed by `tools/attractor`).**

| j | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `γ(T_j)` | 3 | 3 | 4 | 4 | 5 | 5 | 6 | 6 | 7 | 7 | 8 |
| `δ(T_j)` | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |

i.e. **`γ(T_j) = ⌈j/2⌉ + 1`** and **`δ(T_j) = 2`** for all eleven values.  Since `δ = 2` while
`γ = Θ(log n)`, this family proves `γ/δ = Ω(log n)` **constructively on a binary alphabet** — the
KNP separation made exact.  This lane turns the two formulas into theorems.

**Why it should be provable.**  The factor `f_k = 1 0^{2^k−1} 1` (length `2^k + 1`) occurs
**exactly once** in `T_j`, because the gap between consecutive `1`s at scale `k` is `2^k` and no
other scale has that gap.  So its coverage set is the single interval `[2^k, 2^{k+1}]` (0-indexed
positions `2^k … 2^{k+1}`), and spans of *non-adjacent* scales are disjoint — consecutive spans
share the `1` at `2^{k+1}`.  Hence the factors at every other scale are pairwise disjoint, giving
`⌈j/2⌉` and one more for the `11` at the start.

## Contract — `SortBounds/Projects/PowersOfTwo/PowersOfTwo.lean`

```lean
namespace SortBounds.Projects.PowersOfTwo

open SortBounds.Projects.Repetitiveness SortBounds.Projects.AttractorLP Packaging

/-- `T_j`: length `2^j`, `1` exactly at the positions `2^k - 1`. -/
def T (j : ℕ) : List Bool

theorem T_length (j : ℕ) : (T j).length = 2 ^ j

/-- **`δ(T_j) = 2`** (upper half: `d_k ≤ 2k`; lower half: `d_1 = 2`, so `δ ≥ 2`). -/
theorem delta_T (j : ℕ) (hj : 1 ≤ j) : deltaQ (T j) = 2

/-- **The exact attractor number.** -/
theorem gamma_T (j : ℕ) (hj : 3 ≤ j) :
    minAttractorSize (T j) = (j + 1) / 2 + 1        -- = ⌈j/2⌉ + 1 for j ≥ 1

/-- **The consequence, which needs no ceiling convention**: `δ = 2` and `γ → ∞`. -/
theorem gamma_unbounded_over_delta :
    ∀ c : ℚ, ∃ j : ℕ, c < (minAttractorSize (T j) : ℚ) / deltaQ (T j)

end SortBounds.Projects.PowersOfTwo
```

## Milestones (in this order — stop at whatever compiles and report)

* **M0** `T`, `T_length`, and **the run-length characterisation**: `T j` has `1`s exactly at
  positions `2^k − 1` for `k < j`, and zeros elsewhere.  Everything else rests on this.
* **M1** **Lower bound `γ(T_j) ≥ ⌈j/2⌉ + 1`** — the tractable half and the scientifically important
  one (it is what proves the separation).  Route: exhibit the factor set
  `{11} ∪ {1 0^{2^k−1} 1 : k ∈ K}` for a suitable index set `K` of pairwise non-adjacent scales,
  prove each is in `factorUniverse`, prove the coverage sets pairwise disjoint, and apply
  `Packing.card_le_minAttractorSize_of_pairwiseDisjoint`.  To prove a coverage set is exactly an
  interval: show the factor occurs at exactly one place (`List.IsInfix` uniqueness) and then
  `coverageSet` is that occurrence's span.
* **M2** `δ(T_j) = 2` — `≥` from `d_1 = 2`; `≤` from `d_k ≤ 2k` (every factor of length `k` is
  determined by the ≤ 2 nearest `1`-positions and the offsets, mirroring
  `Repetitiveness.distinctFactors_card_le_mul_attractor`).
* **M3** the upper bound `γ(T_j) ≤ ⌈j/2⌉ + 1` — an explicit attractor.  The tool's search suggests
  marking, for `j = 5`, positions `{1,2,7,16,31}`-style: one position per *pair* of scales plus the
  leading `1`.  Derive a scale-free rule and prove it covers every factor.  This is the hard step;
  if it resists, **report M1, M2 and the lower bound only** — that is already the separation.
* **M4** `gamma_unbounded_over_delta` from M1+M2 (`γ ≥ ⌈j/2⌉+1 → ∞` with `δ = 2`).

## Rules

Own only `SortBounds/Projects/PowersOfTwo/`.  `lake env lean` only (oleans in `/tmp`); no `git`, no
`lake build`.  No `sorry`/`admit`/`axiom`/`native_decide`.  `decide` on `T 13` (8192 symbols) is
far too slow — **prove the general statements; use `decide` only on `T 3`, `T 4`, `T 5`** as
sanity anchors.  Read `Repetitiveness/Basic.lean` (`factorOcc`, `distinctFactors`,
`mem_distinctFactors`), `AttractorLP/Gap.lean` (`coverageSet`, `mem_coverageSet`,
`factorUniverse`, `mem_factorUniverse`) and `Packing/Packing.lean`
(`card_le_minAttractorSize_of_pairwiseDisjoint`) before writing.

## Log

* (empty)
