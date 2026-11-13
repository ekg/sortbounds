# Lane 6 — upgrade T4: `γ ≤ ⌈δ⌉ + 3` is false too

**Why.** `Packing.gamma_delta_add_two_false` refutes `γ ≤ δ + 2` at `n = 32` (`γ = 6`, `δ = 3`).
The programme now has a witness with `γ − δ = 4`, so the refutation should say `+3`, not `+2`.
Smaller witness is better for the kernel, and the best one is **`n = 48`**, not the `n = 96`
record — `n = 48` has `γ = 7`, `δ = 3`, gap `4`, and its packing is a **partition** of the
positions, which is exactly the shape Lean likes.

## The witness (all verified by the supervisor at the definition level)

```
s48 = 010011011100110000001100000000000011000001100001     (n = 48)
attractor   {0, 7, 12, 15, 27, 40, 42}                     -- IsAttractor, verified
packing     seven factors whose coverage sets PARTITION {0..47}:
    "010"        C = {0..2}
    "01101"      C = {3..7}
    "11001"      C = {8..12}
    "10000001"   C = {13..20}
    "10000000"   C = {21..28}
    "0000011000001" C = {29..41}
    "100001"     C = {42..47}
δ = 3        (d_1..d_6 = 2, 4, 8, 12, 15, 18 — so d_4/4 = d_5/5 = d_6/6 = 3, and d_k ≤ 3k
              for k ≥ 25 by `d_k ≤ n-k+1 ≤ 3k`, with k = 7..24 by `decide`)
```

Hence `7 ≤ γ ≤ 7` and `δ = 3`, so `γ ≤ δ + 3` would read `7 ≤ 6`.

## Contract — append to the existing `Packing.lean` (do not rewrite it)

```lean
def s48 : List Bool
def s48Attractor : Finset (Fin s48.length)          -- card 7
theorem s48_attractor : IsAttractor s48 s48Attractor
theorem s48_gamma_ge : 7 ≤ minAttractorSize s48     -- from the packing, via
                                                    -- card_le_minAttractorSize_of_pairwiseDisjoint
theorem s48_gamma : minAttractorSize s48 = 7
theorem s48_delta : deltaQ s48 = 3
theorem gamma_delta_add_three_false : ¬ ∀ s : List Bool,
    (minAttractorSize s : ℚ) ≤ deltaQ s + 3
```

## Reuse, do not rediscover

`Packing.lean` already contains everything structural: `card_le_minAttractorSize_of_pairwiseDisjoint`,
`card_distinctFactors_le_length`, and the `s32_*` proofs are a template for every step here
(including how the row form `isAttractor_iff_coverageSet` is used to certify an attractor at a size
where `isAttractor_iff_check` + `decide` times out).  Copy the `s32` proof shape and change the
data.

## Practical notes

* `decide` at `n = 48` will be slower than the ~95 s it took at `n = 32`.  Raise
  `set_option maxHeartbeats` locally if needed, and **report the wall time of each long `decide`**.
  If a single `decide` exceeds ~20 minutes, stop and report which one — a partial result with
  timings is a valid deliverable.
* For `δ = 3`, mirror `s32_delta_ge`/`s32_delta_le`: `≥` from `(distinctFactors s48 4).card = 12`
  and `≤` from `d_k ≤ 3k` (cases `k ≤ 24` by `decide`, `k ≥ 25` from `card_distinctFactors_le_length`).
* Do not touch `Gap.lean`, `Witness.lean`, `DeltaBound.lean`, or `DeBruijn/`.

## Log

* (empty)
