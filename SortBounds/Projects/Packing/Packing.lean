/-
SortBounds/Projects/Packing/Packing.lean

**The packing lower bound `γ ≥ |F|`, and the refutation of `γ ≤ ⌈δ⌉ + 2` at `n = 32`.**

`docs/research/gamma-delta-table.md` brackets every instance as `[lb, ub]` on `γ`: `ub` from an
exhibited attractor, `lb` from a **packing certificate** — and the packing certificate is the one
piece of that toolchain that was still only `tools/attractor` Python.  A family `F` of factors
whose coverage sets `C(f) = {p : p crosses an occurrence of f}` are pairwise **disjoint** forces
any attractor to have at least one position per factor —

  `γ ≥ P(S)`, `P(S)` = maximum number of factors with pairwise disjoint coverage sets,

because an attractor meets every `C(f)` (`isAttractor_iff_coverageSet`) and disjointness makes
the meeting points distinct.  That is `card_le_minAttractorSize_of_pairwiseDisjoint` below, in
the general form the notes use (any `α` with `DecidableEq`, no integrality or size restriction on
the covers).

The second half of the file is the sharpest concrete instance we have.  For

  `s32 = bbbaaaabbabbaaabbaaaabbaabbaabaa`   (`n = 32`),

the six factors

  `"bbb"   C = {0,1,2}`      `"bab"   C = {8,9,10}`        `"baaab" C = {11,12,13,14,15}`
  `"baabb" C = {22,23,24,25,26}`  `"aba"  C = {28,29,30}`  `"aaaa"  C = {3,4,5,6,17,18,19,20}`

have pairwise disjoint coverage sets, so `γ ≥ 6`; `{0,10,12,17,24,28}` is an attractor, so
`γ ≤ 6`; and `δ = 3` (`d_k = 3k` at `k = 4,5,6,7`, and `d_k ≤ 3k` for every `k ≤ 32`).  Hence
`γ = 6 = δ + 3` and **`γ ≤ ⌈δ⌉ + 2` is false** (`gamma_delta_add_two_false`), which was
previously `tools/attractor` output only.  `δ = 3` is an integer here, so no ceiling convention
enters the statement.

**How the large finite checks are done.**  `IsAttractor` is not decided directly: its
`isAttractor_iff_check` form quantifies over `(n+1)²` intervals and searches `(n+1)²` occurrences
each, ~1.2 M reduction steps at `n = 32` (measured: it does not finish within a default heartbeat
budget).  Instead `isAttractor_iff_coverageSet` reduces the obligation to one nonemptiness test per
factor of the universe (402 rows × 32 positions) — `s32_covers`, decided below in ~95 s of
elaboration.  That row check needs `maxHeartbeats` raised (at the default 200 000 the `decide`
fails) and `maxRecDepth` raised as in `AttractorLP/Witness.lean`; both values below were measured
to suffice.
-/
import Mathlib
import SortBounds.Projects.AttractorLP.Gap

-- `s32_covers` evaluates `coverageSet` for every factor of a length-32 text: deep enough to need
-- a larger recursion budget than the default (cf. `AttractorLP/Witness.lean`), and wide enough to
-- exceed the default 200 000 heartbeats (`decide` then fails at `whnf`, ~30 s in).  Both values
-- were measured to suffice; the whole file then elaborates in ~1 m 40 s.
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SortBounds.Projects.Packing

open SortBounds.Projects.Repetitiveness SortBounds.Projects.AttractorLP

variable {α : Type*} [DecidableEq α]

/-! ### M0 — the packing lower bound

If the coverage sets of the factors of `F` are pairwise disjoint, an attractor needs a distinct
position per factor.  The proof avoids `Classical.choose`: the sets `C(f) ∩ Γ` are pairwise
disjoint nonempty subsets of `Γ`, so `F.card = Σ_{f∈F} 1 ≤ Σ_{f∈F} |C(f) ∩ Γ| = |⋃_f (C(f) ∩ Γ)|
≤ |Γ|`. -/

/-- **The packing lower bound, in general form.**  If every factor in `F` occurs (so its coverage
set is a legitimate constraint) and the coverage sets of `F` are pairwise disjoint, then any
attractor has at least `F.card` positions. -/
theorem card_le_minAttractorSize_of_pairwiseDisjoint {s : List α} (F : Finset (List α))
    (hF : ∀ f ∈ F, f ∈ AttractorLP.factorUniverse s)
    (hdisj : ∀ f ∈ F, ∀ g ∈ F, f ≠ g → Disjoint (coverageSet s f) (coverageSet s g)) :
    F.card ≤ minAttractorSize s := by
  classical
  -- the *minimum* attractor: the bound is about `γ`, not about an arbitrary attractor
  obtain ⟨Γ, hΓ, hcard⟩ := exists_attractor_card_eq_minAttractorSize s
  -- every factor of `F` is met by `Γ` (`isAttractor_iff_coverageSet`), so `C(f) ∩ Γ` is nonempty
  have hne : ∀ f ∈ F, (coverageSet s f ∩ Γ).Nonempty := fun f hf =>
    (isAttractor_iff_coverageSet Γ).mp hΓ f (hF f hf)
  -- and disjointness survives the intersection with `Γ`
  have hdisj' : (F : Set (List α)).PairwiseDisjoint (fun f => coverageSet s f ∩ Γ) :=
    fun f hf g hg hfg =>
      Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left (hdisj f hf g hg hfg)
  have hsum : F.card ≤ ∑ f ∈ F, (coverageSet s f ∩ Γ).card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun f hf => Finset.card_pos.mpr (hne f hf)
  have hsub : F.biUnion (fun f => coverageSet s f ∩ Γ) ⊆ Γ := by
    intro p hp
    obtain ⟨f, -, hpf⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hpf).2
  calc F.card ≤ ∑ f ∈ F, (coverageSet s f ∩ Γ).card := hsum
    _ = (F.biUnion (fun f => coverageSet s f ∩ Γ)).card := (Finset.card_biUnion hdisj').symm
    _ ≤ Γ.card := Finset.card_le_card hsub
    _ = minAttractorSize s := hcard

/-! ### M1 — the instance `s32` (`n = 32`) and its attractor -/

/-- The witness text `bbbaaaabbabbaaabbaaaabbaabbaabaa` (`n = 32`), `'a' = true`, `'b' = false`. -/
def s32 : List Bool :=
  [false, false, false, true, true, true, true, false, false, true, false, false, true, true, true,
    false, false, true, true, true, true, false, false, true, true, false, false, true, true, false,
    true, true]

theorem s32_length : s32.length = 32 := by decide

/-- The attractor `{0, 10, 12, 17, 24, 28}` of `s32`. -/
def s32Attractor : Finset (Fin s32.length) :=
  {⟨0, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨17, by decide⟩, ⟨24, by decide⟩,
    ⟨28, by decide⟩}

theorem s32Attractor_card : s32Attractor.card = 6 := by decide

/-- **`{0,10,12,17,24,28}` meets the coverage set of every factor of `s32`**: the covering
condition row by row (`isAttractor_iff_coverageSet`), one nonemptiness test per factor of
`factorUniverse s32` — the ~90 s check of this file. -/
theorem s32_covers :
    ∀ f ∈ factorUniverse s32, (coverageSet s32 f ∩ s32Attractor).Nonempty := by
  decide

theorem s32_attractor : IsAttractor s32 s32Attractor :=
  (isAttractor_iff_coverageSet s32Attractor).mpr s32_covers

/-! ### M2 — the six-factor packing

The coverage sets are stated explicitly as well as used: they are the certificate
`docs/research/gamma-equals-delta.md` quotes, and the disjointness below is checked against
`coverageSet` itself rather than against these transcriptions. -/

/-- The six factors of the packing: `"bbb"`, `"bab"`, `"baaab"`, `"baabb"`, `"aba"`, `"aaaa"`. -/
def s32Packing : Finset (List Bool) :=
  {[false, false, false], [false, true, false], [false, true, true, true, false],
    [false, true, true, false, false], [true, false, true], [true, true, true, true]}

theorem s32Packing_card : s32Packing.card = 6 := by decide

theorem s32_coverageSet_bbb :
    coverageSet s32 [false, false, false] = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩} := by
  decide

theorem s32_coverageSet_bab :
    coverageSet s32 [false, true, false] =
      {⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩} := by
  decide

theorem s32_coverageSet_baaab :
    coverageSet s32 [false, true, true, true, false] =
      {⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩} := by
  decide

theorem s32_coverageSet_baabb :
    coverageSet s32 [false, true, true, false, false] =
      {⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩} := by
  decide

theorem s32_coverageSet_aba :
    coverageSet s32 [true, false, true] = {⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩} := by
  decide

theorem s32_coverageSet_aaaa :
    coverageSet s32 [true, true, true, true] =
      {⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨17, by decide⟩,
        ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩} := by
  decide

/-- Each of the six factors is a factor of `s32` (its `factorOcc` interval is exhibited), hence a
row of the constraint system `factorUniverse s32`. -/
theorem s32Packing_subset : s32Packing ⊆ factorUniverse s32 := by
  intro f hf
  simp only [s32Packing, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_factorUniverse.mpr ⟨0, 3, by decide, by decide, by decide⟩
  · exact mem_factorUniverse.mpr ⟨8, 11, by decide, by decide, by decide⟩
  · exact mem_factorUniverse.mpr ⟨11, 16, by decide, by decide, by decide⟩
  · exact mem_factorUniverse.mpr ⟨22, 27, by decide, by decide, by decide⟩
  · exact mem_factorUniverse.mpr ⟨28, 31, by decide, by decide, by decide⟩
  · exact mem_factorUniverse.mpr ⟨3, 7, by decide, by decide, by decide⟩

/-- The six coverage sets are pairwise disjoint.  Checked against `coverageSet` itself, not
against the six transcriptions above: the bound `∀ f ∈ s32Packing` is finite, so `decide`
evaluates the twelve coverage sets and the thirty-six intersections. -/
theorem s32Packing_pairwiseDisjoint :
    ∀ f ∈ s32Packing, ∀ g ∈ s32Packing, f ≠ g →
      Disjoint (coverageSet s32 f) (coverageSet s32 g) := by
  decide

/-- **`γ ≥ 6`** for the witness: the packing lemma applied to the six disjoint coverage sets. -/
theorem s32_gamma_ge : 6 ≤ minAttractorSize s32 := by
  have h := card_le_minAttractorSize_of_pairwiseDisjoint s32Packing s32Packing_subset
    s32Packing_pairwiseDisjoint
  rwa [s32Packing_card] at h

/-! ### M3 — `γ = 6` -/

/-- **`γ = 6`**: `{0,10,12,17,24,28}` is an attractor (`≤`) and no attractor is smaller
(`s32_gamma_ge`), so `γ = P = 6` — the packing is optimal here. -/
theorem s32_gamma : minAttractorSize s32 = 6 := by
  refine le_antisymm ?_ s32_gamma_ge
  calc minAttractorSize s32 ≤ s32Attractor.card := minAttractorSize_le s32_attractor
    _ = 6 := s32Attractor_card

/-! ### M4 — `δ = 3`

`d_k` counts distinct length-`k` factors, so `d_k ≤ n - k + 1` always
(`card_distinctFactors_le_length`); at `n = 32` that is `d_k ≤ 3k` for `k ≥ 9`, and the eight
remaining lengths are decided.  The lower bound `3 ≤ δ` is `d_4 = 12`. -/

/-- **`d_k ≤ n - k + 1`**: there are only that many starting positions for a length-`k` factor.
The general position-count bound behind the large-`k` half of `δ ≤ 3` below. -/
theorem card_distinctFactors_le_length (s : List α) (k : ℕ) :
    (distinctFactors s k).card ≤ s.length - k + 1 := by
  have hsub : distinctFactors s k ⊆
      (Finset.range (s.length - k + 1)).image (fun i => (s.drop i).take k) := by
    intro f hf
    obtain ⟨i, hik, rfl⟩ := mem_distinctFactors.mp hf
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  calc (distinctFactors s k).card
      ≤ ((Finset.range (s.length - k + 1)).image (fun i => (s.drop i).take k)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range (s.length - k + 1)).card := Finset.card_image_le
    _ = s.length - k + 1 := Finset.card_range _

/-- **`d_k ≤ 3k` for every `k ≥ 1`** on the witness.  `k ≤ 8` is decided; for `k ≥ 9` the
position count `32 - k + 1 ≤ 3k` suffices. -/
theorem s32_dk_le {k : ℕ} (hk1 : 1 ≤ k) : (distinctFactors s32 k).card ≤ 3 * k := by
  by_cases hk : k ≤ 8
  · interval_cases k <;> decide
  · have h1 := card_distinctFactors_le_length s32 k
    rw [s32_length] at h1
    omega

/-- `d_4 = 12` on the witness — the source of the lower bound `3 ≤ δ`. -/
theorem s32_d4 : (distinctFactors s32 4).card = 12 := by decide

/-- `deltaQ` unfolded at a nonempty string, so that both bounds on it are `sup'` bounds. -/
theorem deltaQ_eq_sup' {s : List α} (h : 1 ≤ s.length) :
    deltaQ s = (Finset.Icc 1 s.length).sup'
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩
      (fun k => ((distinctFactors s k).card : ℚ) / (k : ℚ)) := by
  rw [deltaQ, dite_eq_left h]

theorem s32_delta_ge : 3 ≤ deltaQ s32 := by
  rw [deltaQ_eq_sup' (by decide : 1 ≤ s32.length)]
  refine Finset.le_sup'_of_le (f := fun k => ((distinctFactors s32 k).card : ℚ) / (k : ℚ))
    (b := 4) ?_ ?_
  · rw [s32_length]; decide
  · rw [s32_d4]; norm_num

theorem s32_delta_le : deltaQ s32 ≤ 3 := by
  rw [deltaQ_eq_sup' (by decide : 1 ≤ s32.length)]
  refine Finset.sup'_le _ _ fun k hk => ?_
  obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
  rw [div_le_iff₀ (by exact_mod_cast hk1 : (0 : ℚ) < (k : ℚ))]
  have h := s32_dk_le hk1
  exact_mod_cast h

/-- **`δ = 3`** for the witness. -/
theorem s32_delta : deltaQ s32 = 3 := le_antisymm s32_delta_le s32_delta_ge

/-! ### M5 — the refutation -/

/-- **`γ ≤ ⌈δ⌉ + 2` is false**, witnessed at `n = 32`: there `γ = 6` and `δ = 3`, so the
inequality would read `6 ≤ 5`.  `δ` is an integer at this witness, so the statement needs no
ceiling convention. -/
theorem gamma_delta_add_two_false : ¬ ∀ s : List Bool,
    (minAttractorSize s : ℚ) ≤ deltaQ s + 2 := by
  intro h
  have h32 := h s32
  rw [s32_gamma, s32_delta] at h32
  norm_num at h32

/-! ### The certified bracket, in general form

Both lower bounds the toolchain can certify -- `δ` and a packing -- are `≤ LP*`, and `LP* ≤ γ`.
So the bracket `[max(δ, packing), γ]` that `tools/attractor` reports is a *valid* bracket for the
LP optimum as well: `max(δ, |F|) ≤ LP* ≤ γ`.  The right-hand inequality is `γ ≥ LP*` trivially
(the LP relaxes the integer problem), so we state it as `Σx ≤ γ` for every feasible `x`.
-/

/-- **A packing is an LP lower bound**: because the coverage sets are pairwise disjoint, a
primal-feasible `x` must spend total weight at least `|F|` — one unit on each disjoint set. -/
theorem card_le_primalValue_of_pairwiseDisjoint {s : List α} (F : Finset (List α))
    (hF : ∀ f ∈ F, f ∈ AttractorLP.factorUniverse s)
    (hdisj : ∀ f ∈ F, ∀ g ∈ F, f ≠ g → Disjoint (coverageSet s f) (coverageSet s g))
    {x : Fin s.length → ℚ} (hx : AttractorLP.PrimalFeasible s x) :
    (F.card : ℚ) ≤ ∑ p, x p := by
  classical
  set U : Finset (Fin s.length) := F.biUnion (fun f => coverageSet s f) with hU
  have hpd : Set.PairwiseDisjoint (↑F) (fun f => coverageSet s f) := by
    intro f hf g hg hne
    exact hdisj f (Finset.mem_coe.1 hf) g (Finset.mem_coe.1 hg) hne
  -- the weight on the disjoint union is the sum of the weights on the pieces
  have hsplit : ∑ p ∈ U, x p = ∑ f ∈ F, ∑ p ∈ coverageSet s f, x p := by
    rw [hU, Finset.sum_biUnion hpd]
  have hlow : (F.card : ℚ) ≤ ∑ f ∈ F, ∑ p ∈ coverageSet s f, x p := by
    calc (F.card : ℚ) = ∑ _f ∈ F, (1 : ℚ) := by simp
      _ ≤ ∑ f ∈ F, ∑ p ∈ coverageSet s f, x p :=
          Finset.sum_le_sum fun f hf => hx.2 f (hF f hf)
  calc (F.card : ℚ) ≤ ∑ f ∈ F, ∑ p ∈ coverageSet s f, x p := hlow
    _ = ∑ p ∈ U, x p := hsplit.symm
    _ ≤ ∑ p, x p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) fun p _ _ => hx.1 p

/-- **`LP* ≤ γ`**, in certificate form: the indicator of a minimum attractor is primal feasible and
has value `γ`, so the LP optimum is at most `γ`.  (An *arbitrary* feasible `x` can exceed `γ` —
the all-ones vector does — so this is an existence statement, not a universal one.) -/
theorem exists_primalValue_le_minAttractorSize (s : List α) :
    ∃ x : Fin s.length → ℚ,
      AttractorLP.PrimalFeasible s x ∧ ∑ p, x p ≤ (minAttractorSize s : ℚ) := by
  classical
  obtain ⟨Γ, hΓ, hcard⟩ := exists_attractor_card_eq_minAttractorSize s
  set x : Fin s.length → ℚ := fun p => if p ∈ Γ then 1 else 0 with hxdef
  have hnonneg : ∀ p, (0 : ℚ) ≤ x p := fun p => by
    simp only [hxdef]; split_ifs <;> norm_num
  have hcover : ∀ f ∈ AttractorLP.factorUniverse s, (1 : ℚ) ≤ ∑ p ∈ coverageSet s f, x p := by
    intro f hf
    obtain ⟨p, hp⟩ := (AttractorLP.isAttractor_iff_coverageSet Γ).1 hΓ f hf
    obtain ⟨hpC, hpG⟩ := Finset.mem_inter.1 hp
    have hsingle : x p ≤ ∑ q ∈ coverageSet s f, x q :=
      Finset.single_le_sum (f := x) (fun q _ => hnonneg q) hpC
    have : x p = 1 := by simp only [hxdef]; rw [if_pos hpG]
    rw [this] at hsingle
    exact hsingle
  refine ⟨x, ⟨hnonneg, hcover⟩, ?_⟩
  have hsum : ∑ p : Fin s.length, x p = (Γ.card : ℚ) := by
    have h1 : (Finset.univ.filter (fun p : Fin s.length => p ∈ Γ)) = Γ := by
      ext p; simp
    rw [← Finset.sum_filter]
    rw [h1, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
  rw [hsum, hcard]

end SortBounds.Projects.Packing