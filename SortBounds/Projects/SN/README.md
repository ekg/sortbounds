# Lane: SN — certified exact minimum comparison counts `S(n)`

**Question.** `S(n)` = fewest comparisons that suffice to sort `n` elements.
Known exactly for `n ≤ 22`; `S(n) = ⌈log₂ n!⌉` for `n ≤ 11`, and the first gap is
`S(12) = 30 > ⌈log₂ 12!⌉ = 29`. The table is computer-assisted folklore with no
machine-checked verification of the *lower* bounds.

**Why it matters.** It is a live open problem (`n ≥ 23`, and the second-order
term), and it is exactly the object our counting theorem half-controls.

## Contract (exact target signatures)

```lean
namespace SortBounds.Projects.SN

open SortBounds

/-- Merge sort (or insertion sort) gives *some* correct tree for every `n`. -/
theorem exists_correct_tree (n : ℕ) : ∃ t : Tree n, Correct (α := ℕ) t

/-- `S n`: the least depth of a correct comparison tree on `n` positions. -/
def S (n : ℕ) : ℕ
theorem S_spec (n) : ∃ t : Tree n, Correct (α := ℕ) t ∧ depth t ≤ S n
theorem S_le_iff (n d) : S n ≤ d ↔ ∃ t : Tree n, Correct (α := ℕ) t ∧ depth t ≤ d

/-- Lower bound: counting (`n! ≤ 2^depth`). -/
theorem S_lower (n) : Nat.clog 2 (Nat.factorial n) ≤ S n

/-- Explicit optimal trees (easy cases). -/
theorem S_zero : S 0 = 0
theorem S_one : S 1 = 0
theorem S_two : S 2 = 1
theorem S_three : S 3 = 3

/-- M2 — **NOT PROVED YET** (kept here as the target, not as a claim). -/
theorem S_eq_clog (n) (h : n ≤ 11) : S n = Nat.clog 2 (Nat.factorial n)

/-- M3 — **NOT PROVED YET** (research-level: `⌈log₂ 12!⌉ = 29 < 30`). -/
theorem S_twelve : S 12 = 30

end SortBounds.Projects.SN
```

**Status: M0 + M1 landed; M2 and M3 are open.** The contract block above lists all
three so the targets stay pinned; only the first six signatures exist in code.

## Milestones

* **M0** `exists_correct_tree` + `S` + `S_spec`/`S_le_iff` + `S_lower`.
  (`S_lower` is `factorial_le_two_pow_depth` plus `Nat.le_clog`; `S n` is
  `Nat.find` over `∃ t, Correct t ∧ depth t ≤ d`.)
* **M1** `S 0, S 1, S 2, S 3` (reuse `tree2` for `n = 2` and the depth-2
  impossibility argument for `n = 3`; `SortBounds/Comparison/Examples.lean`).
* **M2** `S n = ⌈log₂ n!⌉` for `n ≤ 8` by explicit trees built by a *generator*
  (if lane `FordJohnson` has landed, its algorithm gives 10/13/16 for
  `n = 6/7/8`); then `n ≤ 11`.
* **M3** `S 12 = 30` — needs more than counting (`29 < 30`). Research-level;
  document the approach tried. Upper bound `≤ 30` is a concrete tree (easy).

## Rules

Own only `SortBounds/Projects/SN/`. Use `lake env lean`. No `sorry`. If you need
a generator from `FordJohnson`, define your own here rather than importing a
half-finished lane; note the duplication in your Log.

## Prior art

Knuth TAOCP §5.3.1; Wells 1965 (`S(12) = 30`); Peczarski 2004 (`n ≤ 22`);
Stober & Weiß 2022 (`S(16..18)`, refuting Knuth's `S(16) = 45`). No
machine-checked `S(n)` table found.

## Log

* 2026-11-11 — **M0 + M1 landed**, no `sorry` (`Basic.lean`, `Small.lean`;
  validate with `lake env lean SortBounds/Projects/SN/Basic.lean`, and
  `Small.lean` after `Basic` is built).
  * `exists_correct_tree` is proved by a deliberately dumb tree: compare every
    ordered pair of positions (`allPairs`, `pairTree`), then read the sorted
    order off the completed table (`losses` / `sortKey` / `sortPos` /
    `tablePerm`, correctness `tablePerm_sorts`).  Depth is quadratic, so it
    certifies existence and makes `S` well defined, nothing more.  No
    `MergeSort`/`FordJohnson` input was needed, so nothing was duplicated from
    those lanes.
  * `S` is `sInf` of the achievable depths (`Nat.sInf` is spelled `sInf` in
    this Mathlib pin); `S_spec`/`S_le_iff` come from `Nat.sInf_mem` /
    `Nat.sInf_le`, `S_lower` from `factorial_le_two_pow_depth` +
    `Nat.clog_le_iff_le_pow`.
  * M1: `S 0 = 0`, `S 1 = 0`, `S 2 = 1` (via `SortBounds.tree2`),
    `S 3 = 3` (new explicit `tree3`, `depth tree3 = 3`,
    `⌈log₂ 3!⌉ = 3` by counting).
  * Not attempted: **M2** (`S n = ⌈log₂ n!⌉` for `n ≤ 11`) and **M3**
    (`S 12 = 30`).  M2 still needs the generator/optimal-tree construction that
    the milestone notes expect from `FordJohnson` M1, plus correctness proofs
    for trees of depth up to 26; out of scope for this pass.
