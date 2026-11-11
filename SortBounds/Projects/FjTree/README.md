# Lane: FjTree — the decision tree of merge-insertion, and optimality for `n ≤ 11`

**Question.** `Projects/SN` proves `S 4 = 5` and `S 5 = 7` by hand-built trees, and
`Projects/FordJohnson` proves the *count* `fjCountJ n` of merge-insertion, with
`fjCountJ n = ⌈log₂ n!⌉` for `4 ≤ n ≤ 11` and `n = 20, 21`. What is missing is the
transfer from the list algorithm to a `Tree n`: the count is only an upper bound on
comparisons *spent*, not on the depth of any tree we have built. This lane builds
that tree, and thereby makes

  `S n = ⌈log₂ n!⌉` for `4 ≤ n ≤ 11` (and `n = 20, 21`)

machine-checked — i.e. **verified optimality of Ford–Johnson** at those sizes.

**Machinery already in place (all landed, build green).**

* `Comparison/Bridge.liftTree` — substitute a family `Perm (Fin n) → Tree (n+1)` into
  the leaves of a prefix tree; `liftTree_correct`, `liftTree_depth_le`.
* `Projects/SortTree.insertTree` — given the prefix order `σ`, binary-search the rank
  of `x (last n)` among `x (σ 0) < … < x (σ (n-1))`; `insertTree_correct`,
  `insertTree_depth_le : ≤ ⌈log₂(n+1)⌉ + 1`, and `insertPerm_sorts`.
* `Projects/FordJohnson.{jac, jacInsertCost, fjCountJ, fjCountJ_eq_clog_factorial}` —
  the Jacobsthal schedule and its count.

**The structural difficulty.** `insertTree` inserts *one* element and hands back a
permutation known only at its leaves; a second insertion must continue from that
leaf with a *different* search window (FJA inserts loser `m` into a window whose size
is `t + s`, fixed by the schedule, not by the prefix sortedness alone). So the
construction is a *sequenced* substitution: `subst` at the same index
(`Tree n → (Perm (Fin n) → Tree n) → Tree n`, a small variant of `liftTree` you may
prove locally) composed along the loser list, each stage being a binary search over
the window dictated by the schedule.

## Contract (exact target signatures)

```lean
namespace SortBounds.Projects.FjTree

open SortBounds

/-- The decision tree of merge-insertion on `n` elements. -/
noncomputable def fjTree : (n : ℕ) → Tree n
theorem fjTree_correct (n : ℕ) : Correct (α := ℕ) (fjTree n)
/-- Depth is at most the count `fjCountJ`, i.e. the count is realised by a tree. -/
theorem fjTree_depth_le (n : ℕ) : depth (fjTree n) ≤ fjCountJ n

/-- Hence the least depth is at most Ford–Johnson's count. -/
theorem S_le_fjCountJ (n : ℕ) : SortBounds.Projects.SN.S n ≤ fjCountJ n

/-- **Verified optimality of merge-insertion for `4 ≤ n ≤ 11`.** -/
theorem S_eq_clog (n : ℕ) (h4 : 4 ≤ n) (h11 : n ≤ 11) :
    SortBounds.Projects.SN.S n = Nat.clog 2 (Nat.factorial n)

end SortBounds.Projects.FjTree
```

`S_le_fjCountJ` needs `SN.S_le_iff` (a tree of depth `d` gives `S n ≤ d`);
`S_eq_clog` then combines it with `SN.S_lower` and
`FordJohnson.fjCountJ_eq_clog_factorial`. Both are one-liners once
`fjTree_depth_le` exists — the whole lane is `fjTree`.

## Milestones

* **M0** scaffolding: an insertion-only tree `insTree n` (binary-insert every
  element in turn) with `insTree_correct` and `depth ≤ n(⌈log₂ n⌉+1)` — this is
  `Projects/SortTree` reproved through the substitution API; it validates the API.
* **M1** pairing + recursive winners: `pairTree` sorts the `n/2` winners and carries
  the losers along (they are determined by the pairing outcomes, so the tree must
  track them at the leaves).
* **M2** loser insertion in Jacobsthal order with the schedule's windows; depth
  bookkeeping against `fjCountJ`'s recurrence.
* **M3** the four contract theorems, and if time permits `n = 20, 21`.

If M2's window bookkeeping defeats you, land M0+M1 plus `fjTree_depth_le` with an
explicit constant slack (e.g. `≤ fjCountJ n + 2·(n/2)`) and report exactly which
invariant broke. Never `sorry`.

## Rules

Own only `SortBounds/Projects/FjTree/`. `lake env lean` only (no `lake build`, no
git, no python for validation; python may emit a certificate that Lean checks).
Importing other lanes is fine — editing them is not.

## Prior art

Ford & Johnson 1959; Knuth TAOCP §5.3.1; exact `S(n)` for `n ≤ 22` (Peczarski
2004; Stober–Weiß 2022 for 16–18). Nothing machine-checked on optimality at these
sizes.

## Log

* (empty)
