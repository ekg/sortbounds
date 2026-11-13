# Lane 5 — Packing: `γ ≤ ⌈δ⌉ + 2` is false, kernel-checked

**Why.** `docs/research/gamma-equals-delta.md` and `gamma-delta-table.md` record the sharpest
surviving conjecture of the programme in the form `γ ≤ ⌈max(δ, P̂)⌉ + 1`, and the weaker
`γ ≤ ⌈δ⌉ + 2` is **already false**: the `n = 32` witness below has `γ = 6`, `δ = 3`.  That is
currently a computation from `tools/attractor`.  Making it a theorem requires the one piece of the
toolchain that is still only Python: **the packing lower bound** (`γ ≥ m` from `m` factors with
pairwise disjoint coverage sets) — the certificate on which every closed bracket in this repository
ultimately rests.

So this lane does double duty: it formalizes the packing certificate, and it uses it to refute a
conjecture with an explicit witness.

## The witness (all data independently verified by the supervisor)

```
text (n = 32)  bbbaaaabbabbaaabbaaaabbaabbaabaa        -- 'a' = true, 'b' = false
attractor      Γ = {0, 10, 12, 17, 24, 28}             -- IsAttractor, definition-level verified
packing        six factors with pairwise DISJOINT definition-level coverage sets:
    "bbb"   C = {0,1,2}
    "bab"   C = {8,9,10}
    "baaab" C = {11,12,13,14,15}
    "baabb" C = {22,23,24,25,26}
    "aba"   C = {28,29,30}
    "aaaa"  C = {3,4,5,6,17,18,19,20}
delta          3        (d_4 = 12, d_5 = 15, and d_k <= 3k for every k <= 32)
```

Hence `6 ≤ γ` (packing) and `γ ≤ 6` (attractor), so `γ = 6 = δ + 3`.

## Where to write

New file `SortBounds/Projects/Packing/Packing.lean`.  Do not modify anything else.

## Contract

```lean
namespace SortBounds.Projects.Packing

open SortBounds.Projects.Repetitiveness SortBounds.Projects.AttractorLP

variable {α : Type*} [DecidableEq α]

/-- **The packing lower bound, in general form.**  If every factor in `F` occurs (so its coverage
set is a legitimate constraint) and the coverage sets of `F` are pairwise disjoint, then any
attractor has at least `F.card` positions. -/
theorem card_le_minAttractorSize_of_pairwiseDisjoint {s : List α} (F : Finset (List α))
    (hF : ∀ f ∈ F, f ∈ AttractorLP.factorUniverse s)
    (hdisj : ∀ f ∈ F, ∀ g ∈ F, f ≠ g → Disjoint (coverageSet s f) (coverageSet s g)) :
    F.card ≤ minAttractorSize s

/-- The instance: `γ = 6` for the witness, both sides. -/
def s32 : List Bool
def s32Attractor : Finset (Fin s32.length)
theorem s32_attractor : IsAttractor s32 s32Attractor     -- by decide, card = 6
theorem s32_gamma_ge : 6 ≤ minAttractorSize s32         -- the packing above
theorem s32_gamma : minAttractorSize s32 = 6
theorem s32_delta : deltaQ s32 = 3

/-- **The refutation**: `γ ≤ ⌈δ⌉ + 2` fails, with `δ` an integer so no ceiling ambiguity. -/
theorem gamma_delta_add_two_false : ¬ ∀ s : List Bool,
    (minAttractorSize s : ℚ) ≤ deltaQ s + 2
```

## Milestones

* **M0** the general packing lemma.  Suggested proof: `isAttractor_iff_coverageSet` gives
  `(coverageSet s f ∩ Γ).Nonempty` for every `f ∈ F`; pick a witness position per factor
  (`Finset.choose`); the chosen positions are distinct because the coverage sets are **disjoint**
  (`Finset.disjoint_left` + `Finset.choose_mem`).  That is an injection `F ↪ Γ`, so `F.card ≤ Γ.card`,
  and then `minAttractorSize ≤ Γ.card` gives the right direction via the minimising attractor.
  Watch the direction: you want `F.card ≤ minAttractorSize s`, so apply the injection to the
  *minimum* attractor (`exists_attractor_card_eq_minAttractorSize`), not to an arbitrary one.
* **M1** `s32`, `s32Attractor`, `s32_attractor` (`isAttractor_iff_check` + `decide`; `n = 32` so
  this may be slow — if `decide` takes more than ~10 minutes, report the time and use a
  manually-guided witness list of uncovered factors instead).
* **M2** the six coverage sets, each proved equal to the explicit set above by `decide`, then
  pairwise disjointness (`Finset.disjoint_left` + `decide` on membership), then `s32_gamma_ge`.
* **M3** `s32_gamma` (`le_antisymm` with `minAttractorSize_le s32_attractor`).
* **M4** `s32_delta : deltaQ s32 = 3`.  Prove the two sides separately: `3 ≤ deltaQ s32` from
  `d_4 = 12` (`2 ^ 2 * 3 = 12`; i.e. `(distinctFactors s32 4).card = 12`, by `decide`, and
  `Finset.le_sup'`), and `deltaQ s32 ≤ 3` from `(distinctFactors s32 k).card ≤ 3 * k` for every
  `k ∈ Icc 1 32` — the case `k ≤ 5` is small; for larger `k` you may need a smarter bound
  (`d_k ≤ n - k + 1 ≤ 3k` holds for `k ≥ 8` since `n = 32`; check `6 ≤ k ≤ 7` by `decide`).
  If the case split fights you, an acceptable fallback is to prove only `2 < deltaQ s32` and
  state the refutation as `5 < minAttractorSize s32` — but say so clearly.
* **M5** `gamma_delta_add_two_false` — instantiate at `s32`: `6 ≤ γ`, `δ = 3`, so
  `γ ≤ δ + 2` would give `6 ≤ 5`.

## Rules

Own only `SortBounds/Projects/Packing/`.  `lake env lean` only; oleans to `/tmp`; no git; no
`lake build`.  No `sorry`/`admit`/`axiom`/`native_decide`.  Read
`SortBounds/Projects/AttractorLP/Gap.lean` (`coverageSet`, `factorUniverse`,
`isAttractor_iff_coverageSet`) and `Repetitiveness/Attractor.lean` (`minAttractorSize`,
`exists_attractor_card_eq_minAttractorSize`) first.

**Do not restate the packing bound for integral covers only** — it must be the general statement
above, since that is what the research notes' brackets rely on.

## Log

**Lane 5 landed. All of M0–M5, no statement weakened, no fallback taken.**  File:
`SortBounds/Projects/Packing/Packing.lean` (`namespace SortBounds.Projects.Packing`), silent under
`lake env lean` in **≈1 m 40 s** wall (98–102 s over four runs; exit 0, no output).  Nothing
outside `Projects/Packing/` and this Log was touched.

### Signatures that compile (verbatim, at the stated types)

```lean
variable {α : Type*} [DecidableEq α]
open SortBounds.Projects.Repetitiveness SortBounds.Projects.AttractorLP

theorem card_le_minAttractorSize_of_pairwiseDisjoint {s : List α} (F : Finset (List α))
    (hF : ∀ f ∈ F, f ∈ AttractorLP.factorUniverse s)
    (hdisj : ∀ f ∈ F, ∀ g ∈ F, f ≠ g → Disjoint (coverageSet s f) (coverageSet s g)) :
    F.card ≤ minAttractorSize s

theorem card_distinctFactors_le_length (s : List α) (k : ℕ) :
    (distinctFactors s k).card ≤ s.length - k + 1          -- auxiliary for M4

def s32 : List Bool
theorem s32_length : s32.length = 32
def s32Attractor : Finset (Fin s32.length)
theorem s32Attractor_card : s32Attractor.card = 6
theorem s32_covers : ∀ f ∈ factorUniverse s32, (coverageSet s32 f ∩ s32Attractor).Nonempty
theorem s32_attractor : IsAttractor s32 s32Attractor

def s32Packing : Finset (List Bool)
theorem s32Packing_card : s32Packing.card = 6
theorem s32_coverageSet_bbb :   coverageSet s32 [false,false,false] = {0,1,2}
theorem s32_coverageSet_bab :   coverageSet s32 [false,true,false] = {8,9,10}
theorem s32_coverageSet_baaab : coverageSet s32 [false,true,true,true,false] = {11,12,13,14,15}
theorem s32_coverageSet_baabb : coverageSet s32 [false,true,true,false,false] = {22,23,24,25,26}
theorem s32_coverageSet_aba :   coverageSet s32 [true,false,true] = {28,29,30}
theorem s32_coverageSet_aaaa :  coverageSet s32 [true,true,true,true] = {3,4,5,6,17,18,19,20}
theorem s32Packing_subset : s32Packing ⊆ factorUniverse s32
theorem s32Packing_pairwiseDisjoint : ∀ f ∈ s32Packing, ∀ g ∈ s32Packing, f ≠ g →
    Disjoint (coverageSet s32 f) (coverageSet s32 g)
theorem s32_gamma_ge : 6 ≤ minAttractorSize s32
theorem s32_gamma : minAttractorSize s32 = 6

theorem s32_dk_le {k : ℕ} (hk1 : 1 ≤ k) : (distinctFactors s32 k).card ≤ 3 * k
theorem s32_d4 : (distinctFactors s32 4).card = 12
theorem deltaQ_eq_sup' {s : List α} (h : 1 ≤ s.length) : deltaQ s = (Icc 1 s.length).sup' _ _
theorem s32_delta_ge : 3 ≤ deltaQ s32
theorem s32_delta_le : deltaQ s32 ≤ 3
theorem s32_delta : deltaQ s32 = 3

theorem gamma_delta_add_two_false : ¬ ∀ s : List Bool,
    (minAttractorSize s : ℚ) ≤ deltaQ s + 2
```

The six coverage-set theorems are written with explicit `⟨i, by decide⟩ : Fin s32.length`
elements; the `{0,1,2}` etc. above abbreviates those.  They reproduce the table in the lane brief
exactly, so the brief's witness data is now kernel-checked, not quoted.

### M0 — the general packing lemma (done first, not weakened)

Proved for arbitrary `α` and an arbitrary `Finset (List α)`: no integrality of the covers, no
bound on `|F|` or on `f.length`, no restriction to the six-factor instance.  **Route differs from
the brief's suggestion** (`Finset.choose`): the file uses the union form instead, which needs no
choice function at all.  `hne : ∀ f ∈ F, (coverageSet s f ∩ Γ).Nonempty` (from
`isAttractor_iff_coverageSet` at the *minimum* attractor `Γ`), `hdisj'` = disjointness inherited by
`C(f) ∩ Γ` (`Disjoint.mono Finset.inter_subset_left`), then

`F.card = Σ_{f∈F} 1 ≤ Σ_{f∈F} |C(f) ∩ Γ| = |⋃_f (C(f) ∩ Γ)| ≤ |Γ| = minAttractorSize s`,

with `Finset.card_biUnion` for the middle equality and `Finset.card_le_card` for the last (each
element of the `biUnion` is a `p` with `p ∈ C(f) ∩ Γ`, so `Finset.mem_inter` gives `p ∈ Γ`).
Same statement, same content as the brief's route, no `Classical.choose` and no injectivity proof
about a choice function.  Direction checked: the union is taken at the minimising attractor
(`exists_attractor_card_eq_minAttractorSize`), giving `F.card ≤ minAttractorSize s`.

### M1 — `s32`, `s32Attractor`, `s32_attractor`

`s32 = bbbaaaabbabbaaabbaaaabbaabbaabaa` (`false` = `b`, `true` = `a`), `s32Attractor =
{0,10,12,17,24,28}`, card checked by `decide`.

**Route taken: not `isAttractor_iff_check`.**  `rw [isAttractor_iff_check]; decide` at `n = 32`
exceeds the default 200 000-heartbeat budget (`error: (deterministic) timeout at 'whnf'`, 27 s in,
i.e. *not finished*), because that form is `(n+1)²` intervals × an `(n+1)²` occurrence search per
interval ≈ 1.2 M reductions.  Instead: `s32_covers` — the row form
`∀ f ∈ factorUniverse s32, (coverageSet s32 f ∩ s32Attractor).Nonempty` of
`isAttractor_iff_coverageSet`, 402 rows × 32 positions — by `decide`, and
`s32_attractor := (isAttractor_iff_coverageSet _).mpr s32_covers`.  **That single `decide` costs
≈ 95 s of the file's 99 s**; the rest of the file is seconds.  It needs
`set_option maxHeartbeats 1000000` (default 200 000 is not enough) and `maxRecDepth 100000`
(cf. `Witness.lean`); the file declares the measured-sufficient values at the top, with a comment
saying so.  The brief's fallback ("manually-guided witness list of uncovered factors") was not
needed.

### M2 — the packing, `γ ≥ 6`

`s32Packing` is the six-factor `Finset`; each coverage set is proved equal to the brief's explicit
set by `decide` (the six `s32_coverageSet_*` theorems).  Disjointness is nevertheless checked
against `coverageSet` itself and not against those transcriptions:
`s32Packing_pairwiseDisjoint` is one `decide` directly on the `Disjoint` form (the `∀ f ∈
s32Packing` bound is finite, so `Decidable` exists; an isolated test file carrying only `s32`,
`s32Packing` and this theorem elaborates in 7 s including the Mathlib import, at the default
heartbeat budget).  `s32Packing ⊆ factorUniverse s32` is proved by exhibiting each `factorOcc` interval
(`⟨0,3⟩`, `⟨8,11⟩`, `⟨11,16⟩`, `⟨22,27⟩`, `⟨28,31⟩`, `⟨3,7⟩`) rather than by `decide`, which
keeps it instant.  Then `s32_gamma_ge` is `card_le_minAttractorSize_of_pairwiseDisjoint` at
`F = s32Packing`.

### M3 — `γ = 6`

`le_antisymm` of `minAttractorSize s32 ≤ s32Attractor.card = 6`
(`minAttractorSize_le s32_attractor`) against `s32_gamma_ge`.  So `γ = P = 6` here: the packing is
optimal at this witness, not merely a lower bound.

### M4 — `δ = 3` (both sides; the `2 < δ` fallback was **not** taken)

* `3 ≤ deltaQ s32`: `s32_d4 : (distinctFactors s32 4).card = 12`, fed to
  `Finset.le_sup'_of_le` at `b = 4`, `(12 : ℚ)/4 = 3`.  (`deltaQ_eq_sup'` unfolds `deltaQ`'s
  `dite` once so both bounds are `sup'` bounds.)
* `deltaQ s32 ≤ 3`: `Finset.sup'_le` + `s32_dk_le {k} (1 ≤ k) : (distinctFactors s32 k).card ≤ 3*k`.
  For that, `k ≤ 8` by `interval_cases` + `decide` (eight small `decide`s), and `k ≥ 9` by the
  new general bound `card_distinctFactors_le_length : d_k ≤ n - k + 1`
  (distinct factors inject into starting positions) with `n = 32`, i.e. `33 - k ≤ 3k ⟺ k ≥ 9`,
  closed by `omega`.
* **Small correction to the brief:** the brief says `d_k ≤ n-k+1 ≤ 3k` "holds for `k ≥ 8`"; at
  `n = 32` it holds for `k ≥ 9` (`k = 8` gives `25 > 24`) — so the split is at 9, and `k = 8` went
  into the decided branch.  `d_8 = 23 ≤ 24` confirms it needs the extra case.

### M5 — the refutation

`gamma_delta_add_two_false : ¬ ∀ s : List Bool, (minAttractorSize s : ℚ) ≤ deltaQ s + 2`,
by instantiating at `s32`, rewriting with `s32_gamma` and `s32_delta` (`6 ≤ 3 + 2`) and
`norm_num`.

### Hardest step

Not M0 and not M4 — **M1**.  The definition-level attractor check at `n = 32` is out of reach of
kernel `decide` in its `isAttractor_iff_check` form (it does not finish inside a 200 000-heartbeat
budget, and the file-level cost of the whole certification is dominated by the one `decide` of
`s32_covers`: ≈ 95 s of 99 s).  Everything else is a thin wrapper: M0 is five lines of `Finset`
bookkeeping, M4 is bookkeeping + `omega`.  Practical lesson for the next instance lane: reduce
`IsAttractor` to the *row* form `isAttractor_iff_coverageSet` before calling `decide` (the
interval form is `(n+1)⁴`-shaped and does not finish even at the default budget), and raise
`maxHeartbeats` before concluding that a finite check is infeasible.

### Trust audit (informational; not wired into `scripts/axioms.lean` by this lane)

`#print axioms` on `card_le_minAttractorSize_of_pairwiseDisjoint`,
`card_distinctFactors_le_length`, `s32_attractor`, `s32Packing_pairwiseDisjoint`, `s32_gamma_ge`,
`s32_gamma`, `s32_delta`, `gamma_delta_add_two_false`: each depends on exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `Lean.ofReduceBool` (`native_decide`).
The file contains no `sorry`, `admit`, `axiom` or `native_decide`.
