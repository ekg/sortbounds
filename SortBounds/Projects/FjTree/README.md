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
  the leaves of a prefix tree; `liftTree_correct`, `depth_liftTree_le`.
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
/-- Depth is at most the count `fjCountJ`.  (A depth bound alone is satisfied by
any tree, e.g. `Tree.leaf 1`; the content arrives with `fjTree_correct`.) -/
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
  is decided, so the larger element of pair `k` is in slot `k` — the comparison branch was
  flipped when `fjTree_correct` was proved, see "Two defects" below) and `pairAux_depth` =
  `n/2`;
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
  — the depth of the tree built by `fjTree` is at most the count.  This is *only* a
  depth bound: `Tree.leaf 1` satisfies it too, and it says nothing about sorting until
  `fjTree_correct` lands.
* **2026-02** `Correct.lean` — **`fjTree_correct`**: the tree sorts.  The phase is carried by
  the invariant `Invar x W m M k p σ`
  (batch `k`, position `p`, chain length `chainLen m M k p = m + jacLo M k + p`):
  `ChainSorted x σ c` ∧ `W ⊆ chainSet σ c` ∧ `∀ o, cntWin x W (σ ⟨c+o⟩) ≤ pendBound M k p o`,
  and `pendBound` is exactly `rank - 1` of the item in slot `c+o` (items of the current
  batch first, in *descending* rank, then the later batches in ascending rank).  The whole
  step is `rankAt_le_winWindow`: with `Setup.rankAt_le_cntWin`,
  `cntWin ≤ jacHi - 1 - p` gives `rankAt ≤ (jacHi - 1 - p) + (jacLo + p) = jacLo + jacHi - 1`,
  the window `winWindow` of `binIns`, with no slack.  Preservation is `invar_step` (the
  shift lemmas `pendBound_shift_lo`/`_hi`), the batch is `insBatch_aux` (also the run
  homomorphism `run (insBatch next) = run (next ∘ run (insBatch leaf))`), the phase is
  `insBatches_sorts`/`insPhase_sorts`, the level is `fjStage_sorts` and the induction is
  `fjTreeFuel_correct`.  (`Basic.insSeqAt`/`insSeqAt_run` state the same transfer for a phase
  whose item slot is fixed — landed and green, but `fjTree_correct` does not consume it:
  `insBatch`'s recursion parameter counts the insertions still to come while `insSeqAt`'s
  chain length counts up, so plugging one into the other needs a tree equality that is pure
  bookkeeping.  `insBatch_aux` is that induction in `insBatch`'s own indices.)
  The initial invariant is
  `cntWin_transport_le`: slot `m+o` holds the partner of the `o`-th smallest winner, which is
  *smaller* than that winner, so at most `o` winners lie below it.
* **2026-02** `Optimal.lean` — **`S_le_fjCountJ`**, **`S_eq_clog`** (`4 ≤ n ≤ 11`) and
  `S_eq_clog_large` (`S 20 = ⌈log₂ 20!⌉`, `S 21 = 66`), the last two from
  `FordJohnson.fjCountJ_eq_clog_factorial(_large)` and `SN.S_lower`.  Cross-checked against
  the hand-built trees of `Projects/SN`: `S_eq_clog` at `n = 4,5,6,7,11` gives `5, 7, 10,
  13, 26`, the values of `SN.S_four/S_five/S_six/S_seven`, and `S 21 = 66` is Peczarski's
  exact value.

### Two defects found while proving `fjTree_correct` (both fixed here)

Both were invisible to `fjTree_depth_le`, which only counts comparisons.

1. `Main.insBatch` used `m + jacLo M k + j` as the chain length of the insertion at position
   `j` of a batch, while its recursion parameter `j` counts the insertions *still to come*:
   the last item of a batch was searched for in the *shortest* chain (for `n = 5`, batch 1
   inserted its second item at chain length `3` instead of `4`).  `chainLen` is now indexed
   by the position `p` in the batch, `m + jacLo M k + p`; `insBatch_depth` reproved
   unchanged (the depth bound only uses the window).
2. `Setup.pairAux` put the **smaller** element of each pair in the chain slot, and `fjTree`
   then inserted the *larger* partners into the chain of sorted smaller elements.  With that
   convention the rank of an inserted partner is not bounded by its partner's chain position
   at all — `n = 4`, `x = (0,1,2,3)` gives a tree that inserts the value `2` at rank `0` —
   so the landed `fjTree` was not a correct tree for any `n ≥ 4`.  The comparison branch is
   flipped (`pairAux`, `pairAux_decided`, `pairTree_spec`): the larger element goes into the
   chain, the smaller one is inserted, and the single pairing comparison is the rank bound
   (`x (partner) < x (winner)`, so at most `o` winners lie below the partner of the `o`-th
   smallest winner).  Depth, `fjCountJ` and all four contract signatures are unchanged.

### What remains

Nothing for the contract.  Natural continuations, none of them started here:

* `S_eq_clog` cannot be extended past `n = 11` on the strength of this tree: `fjCountJ` is
  not equal to `⌈log₂ n!⌉` at `n = 12` and `n = 22` (both decided by
  `Optimal.fjCountJ_not_attained`: `30 > 29` and `71 > 70`), while the literature's exact
  values (Peczarski) are `S 12 = 30`, `S 22 = 71`.  `Optimal.S_gap_le_one` checks that the
  gap is at most one for every `n ≤ 22`, and `S_pin` records the resulting pin.
* The missing lower-bound half there is **not** reachable by counting, and this document
  previously suggested otherwise — wrongly.  `12! = 479001600 < 2^29`, and Kraft realizes
  any `L ≤ 2^d` as a full binary tree of depth `≤ d`, so no argument about the number of
  leaves can give `S 12 ≥ 30`.  The known proofs are pruned searches over comparison trees
  (Wells 1971 for `n = 12`; Peczarski 2004 up to `n = 22`), i.e. research-level in Lean.
* The four contract theorems are proved; `S 0 … 3` (`S 0 = S 1 = 0`, `S 2 = 1`, `S 3 = 3`)
  are the SN lane's, and `S n ≤ fjCountJ n` from `S_le_fjCountJ` also holds there (trivially:
  `fjCountJ n = 0` for `n < 2`).
