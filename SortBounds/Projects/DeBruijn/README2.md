# Lane 2 — DeBruijnK: the `k`-attractor hierarchy is unbounded at every level

**Why.** `docs/research/gamma-vs-gamma2.md` now proves `γ/γₖ → ∞` for **every fixed `k`**
(`γ_k(B_m) ≤ d_k(B_m) = 2^k` and `γ(B_m) ≥ 2^m/m`). Lane 1 machine-checked the `k = 2` case in
the only way that did not require defining `γ_k` (`γ₂ ≤ 4` was kept in prose). This lane makes the
general statement a theorem: it needs `γ_k` defined, which is the actual work.

## Contract

In `SortBounds/Projects/DeBruijn/AttractorK.lean`:

```lean
namespace SortBounds.Projects.DeBruijn

/-- `Γ` covers every factor of length `≤ k`. -/
def IsAttractorK (s : List α) (k : ℕ) (Γ : Finset (Fin s.length)) : Prop

/-- Minimum size of a `k`-attractor (`γ_k`); `k = s.length` recovers `IsAttractor`. -/
noncomputable def minAttractorKSize (s : List α) (k : ℕ) : ℕ

/-- Sanity: the full-length case is the existing definition. -/
theorem isAttractorK_self_iff (s : List α) (Γ : Finset (Fin s.length)) :
    IsAttractorK s s.length Γ ↔ IsAttractor s Γ

/-- **`γ_k ≤ d_k`**: one position inside an occurrence of each distinct `k`-gram. -/
theorem minAttractorKSize_le_card {s : List α} {k : ℕ} (hk : 0 < k) :
    minAttractorKSize s k ≤ (distinctFactors s k).card + s.length

/-- **`γ ≤ γ_k`** (monotone in `k`): covering every factor of length `≤ k` is a stronger
requirement, so the minimum is at least `γ`.  (If this is easier as `γ_k ≤ γ` for `k ≥ n`,
prove that instead and say so — the direction needed below is only `γ_k ≤ d_k`.) -/
theorem minAttractorKSize_le_minAttractorSize_of_le {s : List α} {k : ℕ} (hk : s.length ≤ k) :
    minAttractorKSize s k ≤ minAttractorSize s

/-- **The general separation**, for a de Bruijn word: `2^m/(m·2^k) ≤ γ/γ_k`. -/
theorem gamma_ratio_ge_isDeBruijn {s : List Bool} {k m : ℕ} (hm : 2 ≤ m) (hkm : k ≤ m)
    (h : IsDeBruijn s m) :
    (2 ^ m : ℚ) / (m * 2 ^ k) ≤ (minAttractorSize s : ℚ) / (minAttractorKSize s k : ℚ)

end SortBounds.Projects.DeBruijn
```

`minAttractorKSize` must be **noncomputable** and defined as an infimum over `Finset`s that are
`IsAttractorK`, exactly as `minAttractorSize` is in `Repetitiveness/Attractor.lean` (read that
file first and mirror its style — same `Finset.univ.powerset`/`Nat.find`-free formulation,
same lemma shapes `le_minAttractorSize` / `exists_attractor_card_eq_minAttractorSize`).

## Milestones

* **M0** `IsAttractorK`, `minAttractorKSize`, the two basic lemmas whose shape mirrors
  `Repetitiveness` (`le_minAttractorKSize`, `exists_attractorK_card_eq_minAttractorKSize`).
* **M1** `isAttractorK_self_iff` (may require care: the two predicates differ only in the length
  bound; prove the implication both ways from the factor sets).
* **M2** `minAttractorKSize_le_card` — the counting bound, which is the only ingredient the
  separation needs.  Watch out: `minAttractorKSize ≤ n` is vacuous if you allow any `Γ ⊆ univ`;
  the honest bound is `≤ d_k` *adjusted for the fact that a `k`-gram occurrence may not exist for
  every position* — state the true bound for the strings you need (de Bruijn words have all
  `k`-grams, so `≤ 2^k` suffices directly).  **If the general `≤ d_k + something` is fiddly,
  prove the de Bruijn instance bound `minAttractorKSize s k ≤ 2^k` instead** and drop M2.
* **M3** `gamma_ratio_ge_isDeBruijn`, from `gamma_ge_of_isDeBruijn` (lane 1) and M2's bound.
* **M4** a `decide` instance at `m = 3, k = 2` showing the bound is satisfied.

## Rules

Own only `SortBounds/Projects/DeBruijn/`.  `lake env lean` only; oleans in `/tmp`; no git; no
`lake build`.  No `sorry`/`admit`/`axiom`/`native_decide`.  Read
`SortBounds/Projects/Repetitiveness/Attractor.lean` (and `Basic.lean`) before writing anything —
mirror the existing definition style rather than inventing one.  Report any statement that had to
be weakened, with the reason.

## Log

### 2026-11-13 lane-2 run — `SortBounds/Projects/DeBruijn/AttractorK.lean` (M0–M4 all done)

`lake env lean SortBounds/Projects/DeBruijn/AttractorK.lean` is **silent** (no errors, no
warnings, no `sorry`; `#print axioms` on every theorem: `propext, Classical.choice,
Quot.sound` only).

**Milestones.**

* **M0** `IsAttractorK`, `attractorsK`/`attractorKSizes`/`minAttractorKSize` + the two mirror
  lemmas `minAttractorKSize_le` and `exists_attractorK_card_eq_minAttractorKSize`; also
  `isAttractorK_univ` (well-definedness, as `isAttractor_univ`), `isAttractorK_iff_check`
  (`decide`-ability, as `isAttractor_iff_check`), `isAttractorK_of_le`,
  `isAttractorK_of_isAttractor`, `isAttractorK_take_one` (the `k`-attractor is not the trivial
  "every factor occurs somewhere": a length-1 factor forces its own position).
* **M1** `isAttractorK_self_iff : IsAttractorK s s.length Γ ↔ IsAttractor s Γ`.
* **M2** `minAttractorKSize_le_card_of_extends` — `γ_k ≤ d_k` exactly, provided every factor
  of length `≤ k` occurs at a position `p` with `p + k ≤ |s|` (the general counting bound, with
  its side condition isolated instead of hidden in `+ something`), then the de Bruijn instance
  the separation needs, `minAttractorKSize_le_two_pow : minAttractorKSize s k ≤ 2^k` for
  `IsDeBruijn s m`, `1 ≤ k ≤ m`, and its `k = 2` case `minAttractorKSize_two_le_four`
  (`γ₂(B_m) ≤ 4`, lane 1's prose remark, now a theorem).  M2's escape clause was **not**
  needed.
* **M3** `gamma_ratio_ge_isDeBruijn`.
* **M4** `decide` instances on lane 1's `0001011100`: `dB3AttractorK2 = {0,3,5}` is a
  `2`-attractor (3 positions for `2^2 = 4`), `minAttractorKSize dB3 2 ≤ 2^2`, and the separation
  instantiated at `m = 3, k = 2` (`2/3 ≤ γ/γ_2`).

**Statements changed relative to this contract.**

1. `gamma_ratio_ge_isDeBruijn` gained the hypothesis `(hk : 1 ≤ k)`.  It is not removable:
   at `k = 0` there is no factor of length `≤ 0`, so `γ_0 = 0` (`minAttractorKSize_zero`) and
   the right-hand ratio has denominator `0`, while the left side is positive.
2. `minAttractorKSize_le_card` (`≤ d_k + |s|`, M2's general form) was **not** stated: it is
   superseded by the sharper `minAttractorKSize_le_card_of_extends` (`≤ d_k` exactly, under the
   extension hypothesis) plus `minAttractorKSize_le_two_pow`.  The odd `+ s.length` slack in the
   contract's version is what the side condition absorbs.
3. `minAttractorKSize_le_minAttractorSize_of_le` was proved in the stronger form
   `minAttractorKSize_le_minAttractorSize : minAttractorKSize s k ≤ minAttractorSize s` for
   *every* `k`, not only `k ≥ s.length` (an attractor is a `k`-attractor for every `k`).  Note
   the contract's prose had the direction of the hierarchy backwards (a `k`-attractor covers
   *fewer* factors, so `γ_k ≤ γ`); the inequality actually stated in the contract was right.
   The corresponding monotonicity in `k` is `minAttractorKSize_anti`.

**The one step that was harder than expected.**  "Choose one position inside an occurrence of
 each distinct `k`-gram" (the research note's phrasing) is *wrong* as stated: with `Γ` = the
 starts of the chosen `k`-gram occurrences, a shorter factor `w` that is a *suffix* of the
 window it is drawn from is not covered by any mark, and the naive bound `γ_k ≤ d_k` is false
 — `"ab"` has `d_2 = 1` and `γ_2 = 2` (`ab_minAttractorKSize_two`, machine-checked).  What
 makes the argument work is that the mark is the **start** of the chosen occurrence, and that
 the occurrence of `w` used is one from which a `k`-window can still be formed to the right.
 For de Bruijn words that last fact costs no cyclicity: pad `w` (`|w| = ℓ ≤ k`) on the right to
 an `m`-gram; any occurrence of an `m`-gram starts at `p ≤ |s| - m`, so `p + k ≤ p + m ≤ |s|`.
 No `γ_k ≤ 2^k + (k-1)` tail correction is needed, and no periodicity of the de Bruijn word is
 invoked (the Eulerian-circuit argument that the last `m-1` characters repeat the first is
 *not* needed).
