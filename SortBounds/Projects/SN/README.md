# Lane: SN — certified exact minimum comparison counts `S(n)`

**Question.** `S(n)` = fewest comparisons that suffice to sort `n` elements. In the code
`S n` is the least **depth** of a correct decision tree; the least worst-case *cost* is
a different (a priori smaller) quantity. For `n = 4, 5` both readings are settled here:
`four_needs_five_comparisons` / `five_needs_seven_comparisons` rule out trees whose
every input costs less, so "fewest comparisons that suffice" is 5 resp. 7 too.
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

/-- M2 — **partly proved**: `S_four` and `S_five` in `Four.lean`/`Five.lean` are
the `n = 4, 5` cases; the general statement is still the target, not a claim. -/
theorem S_four : S 4 = 5
theorem S_five : S 5 = 7
theorem S_eq_clog (n) (h : n ≤ 11) : S n = Nat.clog 2 (Nat.factorial n)

/-- M3 — **NOT PROVED YET** (research-level: `⌈log₂ 12!⌉ = 29 < 30`). -/
theorem S_twelve : S 12 = 30

end SortBounds.Projects.SN
```

**Status: M0 + M1 landed, M2 in progress (`S 4 = 5` and `S 5 = 7` landed),
M3 open.** The contract block above lists all three milestones so the targets stay
pinned; `S_eq_clog` and `S_twelve` do not exist in code yet.

Files: `Basic.lean` (M0), `Small.lean` (M1), `Verify.lean` (tree builders and the
canonical-input correctness reduction), `Four.lean` (`S 4 = 5`), `Five.lean`
(`S 5 = 7`).  Build them in that order (`Verify` before `Four`/`Five`).

## Milestones

* **M0** `exists_correct_tree` + `S` + `S_spec`/`S_le_iff` + `S_lower`.
  (`S_lower` is `factorial_le_two_pow_depth` plus `Nat.le_clog`; `S n` is
  `Nat.find` over `∃ t, Correct t ∧ depth t ≤ d`.)
* **M1** `S 0, S 1, S 2, S 3`: `S 0 = S 1 = 0`, `S 2 = 1` (an explicit one-comparison
tree, cf. `Comparison/Examples.lean`), `S 3 = 3` by counting (`S_lower 3` plus
`Nat.clog 2 6 = 3`) — as the Log records.
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
* 2026-11-11 — **M2, first two cases landed**: `S_four : S 4 = 5` and
  `S_five : S 5 = 7`, no `sorry` (`Verify.lean`, `Four.lean`, `Five.lean`).
  * `Verify.lean` carries the two tools the explicit trees need, both generic in
    `n`:
    * `netTree` folds a fixed comparator sequence (a sorting network) into a
      `Tree`, in wire coordinates, with `netTree_depth : depth (netTree ps π) =
      ps.length`; `swapProd` writes a leaf permutation as a product of
      transpositions.
    * `correct_of_forall_run_xOfPerm : (∀ p, run t (xOfPerm p) = p) → Correct t`.
      This is the load-bearing reduction: `run` depends only on the comparison
      pattern (`run_eq_of_pattern`), and an injective input has the pattern of one
      of the `n!` canonical inputs `xOfPerm p` (`pattern_rankPerm` on the ranking
      permutation `rankPerm`, reused from `SortBounds/Comparison/General.lean`
      rather than re-derived) — so *correctness on the `n!` canonical inputs
      implies correctness*, and those `n!` checks are a finite computation the
      kernel can do (`decide`).
  * `Four.lean`: the upper bound is the classical five-comparator network
    `(0,1),(2,3),(0,2),(1,3),(1,2)` (`tree4`), so depth `= 5` from the length of
    the sequence; `tree4_correct` is the canonical-input check.
  * `Five.lean`: seven comparisons is below the nine comparators of the optimal
    five-wire network, so `tree5` is an adaptive tree (119 internal nodes, `120`
    leaves, depth `7`, every node annotated with the number of orderings still
    consistent with the answers that reach it).  Its skeleton was produced by an
    exhaustive search over knowledge states *outside* Lean (239 states); the
    search is not formalised, but nothing else is taken on trust:
    `tree5_depth = 7`, `tree5_numLeaves = 120` and `tree5_correct` are all
    kernel-checked, the last one again through
    `correct_of_forall_run_xOfPerm`.
  * Deliberate duplication: none.  `Five.lean` does not import the `FordJohnson`
    lane; the tree is a decision tree, not a counted algorithm.
  * `#print axioms` for `S_four`, `S_five`, `tree4_correct`, `tree5_correct`:
    `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
    `Lean.ofReduceBool`.
  * Next for M2: `n = 6` (10 comparisons, `720` canonical inputs) needs the same
    machinery; the `decide` check grows to `720` kernel evaluations of a
    depth-`10` tree, and the tree itself is best taken from a merge-insertion
    construction (`FordJohnson` M1 gives the shape) rather than from a search.
