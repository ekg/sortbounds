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

* **2026-02** `Basic.lean` — the machinery, and M0.  Same-index substitution
  (`substTree`/`run_substTree`/`depth_substTree_le`/`substTree_correct`), re-indexing
  along an injection (`imageTree`/`run_imageTree`/`depth_imageTree`), insertion of the
  element of slot `q` at rank `j` of a chain of length `c ≤ q` (`insertFun`/`insertAt`,
  with the pointwise lemmas `insertAt_apply_lt/eq/mid/gt`), the rank
  (`rankSet`/`rankAt`, `rankAt_eq_card`, `lt_rankAt_iff`, `rankAt_le_cntWin`) and the
  binary search `binIns` with `binIns_run` (the leaf reached is `insertAt (rankAt ·)`)
  and `binIns_depth_le : ≤ ⌈log₂ (hi-lo+1)⌉`.  M0 is `insTree` with `insTree_correct`
  and `insTree_depth_le : depth ≤ n·(⌈log₂ n⌉+1)` — `Projects/SortTree` reproved through
  the API, which validates it.
* **2026-02** `Setup.lean` — `chainSet`, `cntWin` and
  `rankAt_le_cntWin : rankAt ≤ cntWin W q + (c - m)` (the chain holds all `m` winners
  and at most `c - m` non-winners); the pairing stage `pairAux`/`pairTree` with
  `pairAux_agree` (slots outside the pairs are untouched), `pairAux_decided` (every pair
  is decided, so the winner of pair `k` is in slot `k`) and `pairAux_depth` = `n/2`;
  the transport `transportFun`/`transportPerm`/`transport` with `transport_winner`,
  `transport_loser` (loser of the `o`-th smallest winner to slot `m+o`) and
  `transport_last`.  Pairing `k` with `m+k` (not `2k` with `2k+1`) keeps the layout
  contiguous, so no de-interleaving permutation is needed.
* **2026-02** `Main.lean` — the Jacobsthal batches (`jacLo`, `jacHi`, `jacLo_self`), the
  insertion phase `insBatch`/`insBatches`/`insPhase` with `insBatch_depth` and
  `insBatches_depth : ≤ jacInsertCostAux M fuel k + B` (the batch sum is literally
  `FordJohnson`'s, so there is no sum identity to prove), the level `fjStage` with
  `fjStage_depth : ≤ depth rec + jacInsertCost M`, and the tree
  `fjTreeFuel`/`fjTree n`.  **Landed: `fjTree_depth_le : depth (fjTree n) ≤ fjCountJ n`**
  — the count is realised by a `Tree n`.
* **NOT landed (the one open obligation): `fjTree_correct`, hence neither
  `S_le_fjCountJ` nor `S_eq_clog`.**  Everything except the correctness invariant of the
  insertion phase is in place; below is the exact statement that remains.

### What remains, precisely

`fjTree n` is `pairTree`, then (through `imageTree`) the recursive tree on the winners,
`transport`, then the insertion phase.  Correctness of the first three stages is proved
(`pairTree_spec`, `transport_*`, `substTree_correct`/`run_imageTree`).  What is missing
is the invariant of `insBatches`, to be proved by induction with the recursion (this is
`P` for `Basic.insSeq_sorts`, which is already generic): for the state `σ` at batch `k`,
position `j`, with chain length `c = m + jacLo M k + j`,

  `ChainSorted x σ c`  ∧  `W ⊆ chainSet σ c`  ∧
  `∀ o, jacLo M k + j + o < M → cntWin x W (σ ⟨c+o, _⟩) ≤ pendBound M k j o`

where `W = chainSet ρ m` is the winner set of the pairing state `ρ`,
`pendBound M k j o` is `jacLo M k + o` while `o + j < jacHi M k - jacLo M k` and
`jacHi M k + (o - (jacHi M k - jacLo M k - j))` after, and with the shift lemma
`pendBound M k (j+1) o = pendBound M k j (if o < cnt-j-1 then o else o+1)`.
It is preserved because the pending items after the inserted one keep their slots, and
the window is then exactly wide enough:
`rankAt x σ c q ≤ cntWin + (q - m)`, `cntWin ≤ jacLo + cnt - 1 - j`, so
`rankAt ≤ 2·jacLo + cnt - 1 = jacLo + jacHi - 1 = w`; note `w` is *exactly* the window
of `binIns`, with no slack.  The initial invariant (`k = j = 0`) follows from
`transport_loser` and the pairing fact `x (loser) < x (partner)`; the final one
(`k = j = 0`, `M` batches) from `jacLo_self` gives `c = n`, i.e. `Sorts`.
`binIns` already takes `(c, q)` separately (`c` = chain length, `q` = item slot), which
is the generalisation this invariant needs.
