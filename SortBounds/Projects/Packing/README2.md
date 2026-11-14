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

### 2026-11-13 — landed (worker lane, kernel-checked)

**Everything in the contract landed**, appended to `Packing.lean` as sections M6–M10 (the `s32`
sections M0–M5 are untouched).  Final signatures, all inside
`namespace SortBounds.Projects.Packing`:

```lean
def s48 : List Bool
theorem s48_length : s48.length = 48
def s48Attractor : Finset (Fin s48.length)
theorem s48Attractor_card : s48Attractor.card = 7
theorem s48_covers :
    ∀ f ∈ factorUniverse s48, (coverageSet s48 f ∩ s48Attractor).Nonempty
theorem s48_attractor : IsAttractor s48 s48Attractor
def s48Packing : Finset (List Bool)
theorem s48Packing_card : s48Packing.card = 7
theorem s48_coverageSet_010 / _01101 / _11001 / _10000001 / _10000000 / _0000011000001 / _100001
    : coverageSet s48 <factor> = <that factor's block of positions>
theorem s48Packing_subset : s48Packing ⊆ factorUniverse s48
theorem s48Packing_pairwiseDisjoint :
    ∀ f ∈ s48Packing, ∀ g ∈ s48Packing, f ≠ g →
      Disjoint (coverageSet s48 f) (coverageSet s48 g)
theorem s48_gamma_ge : 7 ≤ minAttractorSize s48
theorem s48_gamma : minAttractorSize s48 = 7
theorem s48_dk_le {k : ℕ} (hk1 : 1 ≤ k) : (distinctFactors s48 k).card ≤ 3 * k
theorem s48_d4 : (distinctFactors s48 4).card = 12   -- 4 · 3: the max of d_k / k
theorem s48_delta_ge : 3 ≤ deltaQ s48
theorem s48_delta_le : deltaQ s48 ≤ 3
theorem s48_delta : deltaQ s48 = 3
theorem gamma_delta_add_three_false : ¬ ∀ s : List Bool,
    (minAttractorSize s : ℚ) ≤ deltaQ s + 3
```

Nothing was weakened: `s48_gamma_ge` really is
`card_le_minAttractorSize_of_pairwiseDisjoint` at the seven-factor packing, `s48_gamma` is
`le_antisymm` against `minAttractorSize_le s48_attractor`, and `δ = 3` is both halves
(`d_4 = 12`, plus `d_k ≤ 3k` for every `k`).  The packing's coverage sets are additionally
transcribed (the seven `s48_coverageSet_*` lemmas) so the **partition** of `{0..47}` is in the
file; disjointness itself is checked against `coverageSet`, not against the transcription, as at
`s32`.

**Timings of the long `decide`s** (`set_option profiler true`, whole file also timed with
`/usr/bin/time`):

| check | tactic execution | kernel type checking |
| --- | --- | --- |
| `s48_covers` (894 rows × 48 positions) | **306 s** | **239 s** |
| `s32_covers` (unchanged, for scale) | 62 s | 51 s |
| `s48Packing_pairwiseDisjoint` | 2.8 s | 1.3 s |
| each `s48_coverageSet_*` | 0.6–1.3 s | < 0.3 s |
| `s48_dk_le` (12 `interval_cases` decides) | 0.15–0.47 s | ≪ 1 s |

Whole file: **559 s wall, 37.6 GB peak RSS** (`lake env lean`, profiler run); a separate run of
a standalone file holding only the `s48` data and `s48_covers` measured 532 s / 37 GB.  No single
`decide` is anywhere near the 20-minute stop rule, but `s48_covers` needs `set_option maxHeartbeats
8000000`: a 306 s tactic cannot fit the file's existing 1 000 000 (which `s32_covers`' 62 s
already spends most of), and 8 000 000 was measured to suffice.  Its **37 GB** is the reason the
module header now warns `lake build`ers — `SortBounds.lean` imports this file.  If that hurts,
split the row check by factor length: `factorUniverse_eq_biUnion` makes it `s.length` independent
`decide`s.

**Independent verification of the witness** (Python, before any Lean): `s48` read back byte for
byte from the Lean literal equal to the string above; `d_k = 2,4,8,12,15,18,21,24,27,30,33,35,
35,35,34,…,1` so `max d_k/k = 3` at `k = 4..11` (hence `δ = 3`, and `d_k ≤ 48-k+1 ≤ 3k` already
for `k ≥ 13`, which is why the Lean split is `k ≤ 12` decided / `k ≥ 13` by position count); the
seven coverage sets are exactly the seven position blocks and partition `{0..47}`; and
`{0,7,12,15,27,40,42}` meets all 894 coverage sets.

**One unrelated edit, for silence:** the file's pre-existing `if_pos` (in
`exists_primalValue_le_minAttractorSize`, the closing theorem of the old part) is now
`ite_eq_left` — the identical lemma under its non-deprecated name.  `lake env lean` on the file is
otherwise silent; that deprecation warning was the only output and it predates this lane.

Not touched, as instructed: `Gap.lean`, `Witness.lean`, `DeltaBound.lean`, `DeBruijn/`, and
`gamma_delta_add_two_false` (kept alongside the new `+3` version).
