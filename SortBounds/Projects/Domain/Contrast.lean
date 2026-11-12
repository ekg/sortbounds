/-
SortBounds/Projects/Domain/Contrast.lean

**The contrast: `log_b U` digit reads versus `Ω(n log n)` comparisons.**

The lower bound of `SortBounds.Comparison.LowerBound` is about comparisons of *keys*: a correct
comparison sort needs `log₂(n!) = Θ(n log n)` of them.  The bound of this lane is about digit reads:
`log_b U` per key, `d` in the model.  This file puts the two side by side with explicit numbers, so
that neither can be mistaken for the other.

* `two_digit_probes` — keys in `Key 2 n` (`U = n ^ 2`, `log_n U = 2`): one probe per key does not
  suffice, two do;
* `radix_cost_le_comparison_cost` — the punchline.  Sorting `N` items keyed by two base-`N` digits
  costs radix sort `2 · (N + N) = 4N` elementary operations and no comparisons at all
  (`radix_passes`), while every correct comparison sort of `N` distinct keys spends at least
  `N/4 · log₂ N` comparisons on some input.  For `N ≥ 2 ^ 16` the *whole* radix cost is no larger
  than that comparison count (with equality at `N = 2 ^ 16`) — the models charge different
  currencies, exactly as `Model.lean`'s separation remark says;
* `wordram_probes` — `w`-bit words (`b = 2 ^ w`), keys of `n` words (`U = 2 ^ (n · w)`): `n` word
  reads per key are necessary and `n` suffice, and `log_b U = n`.
-/
import SortBounds.Projects.Domain.Radix
import SortBounds.Comparison.LowerBound

namespace SortBounds.Projects.Domain

/-! ### Two digits in base `n`: `U = n ^ 2` keys, `2` probes -/

/-- **`U = n ^ 2` keys need exactly `2` probes per key.**  One probe reads one base-`n` digit and
cannot separate the `n ^ 2` keys (`passes_lower`); two suffice (`radixProc`, reading digit `0`
then digit `1`).  Note `log_n (n ^ 2) = 2`. -/
theorem two_digit_probes (n : ℕ) (hn : 2 ≤ n) :
    (∀ (p : ℕ) (P : KeyProc 2 n p), p < 2 → ¬ SortsAllKeys P) ∧
      (∃ P : KeyProc 2 n 2, SortsAllKeys P) ∧
      Fintype.card (Key 2 n) = n ^ 2 ∧
      Real.logb n (Fintype.card (Key 2 n)) = 2 := by
  refine ⟨fun p P hp h => passes_lower hn hp ⟨P, h⟩,
    ⟨radixProc 2 n, radixProc_sortsAllKeys⟩, card_Key 2 n, ?_⟩
  rw [card_Key, Nat.cast_pow, Real.logb_pow, Real.logb_self_eq_one (by exact_mod_cast hn)]
  ring

/-- Radix sort on two base-`n` digits: exactly `2` passes, `4n` elementary operations for `n` items,
no comparisons. -/
theorem two_digit_radix_cost (n : ℕ) :
    ((List.range 2).map (fun _ => passCost n n)).length = 2 ∧ radixCost 2 n n = 4 * n ∧
      radixComparisons 2 n n = 0 := by
  refine ⟨by simp, ?_, rfl⟩
  rw [radixCost]
  ring

/-! ### The contrast with comparison sorting -/

/-- **Structure buys speed, and the two bounds do not contradict each other.**  Take `N` items whose
keys are two base-`N` digits.  Radix sort finishes them in `radixCost 2 N N = 4N` elementary
operations with zero comparisons (`two_digit_radix_cost`), whereas *every* correct comparison sort
of `N` distinct keys has an input on which it makes at least `N/4 · log₂ N` comparisons
(`Comparison.LowerBound.exists_input_cost_ge_quarter`).  For `N ≥ 2 ^ 16` the total radix cost is at
most that comparison count, with equality at `N = 2 ^ 16`.

That is not a paradox: the comparison bound charges *comparisons of keys*, and radix sort makes
none.  A comparison procedure is not a `p`-probe procedure in the sense of this lane — it reads the
order of two positions, not the digits of a key, and it must separate the `N!` arrangements of the
input rather than the `N ^ 2` keys (`Model.lean`, separation remark).  Hence no `log_b U` bound can
be derived for it, and no comparison bound for the probe plan.

**Units, stated plainly**: radix's side of the inequality is the *definition*
`radixCost d n b = d · (n + b)`, not an operation count extracted from `radixSort`; the
comparison side is `cost` on a `Tree`, and one comparison is here charged as at least one
elementary operation.  `65536 = 2 ^ 16` is the exact crossover for the `N / 4` constant —
i.e. `16 ≤ log₂ N` — not an asymptotic artefact. -/
theorem radix_cost_le_comparison_cost (N : ℕ) (hN : 65536 ≤ N) {t : Tree N}
    (ht : Correct (α := ℕ) t) :
    ∃ x : Fin N → ℕ, Function.Injective x ∧ (radixCost 2 N N : ℝ) ≤ (cost t x : ℝ) := by
  obtain ⟨x, hx, hcost⟩ := exists_input_cost_ge_quarter (by omega) ht
  refine ⟨x, hx, le_trans ?_ hcost⟩
  have hlog : (16 : ℝ) ≤ Real.logb 2 N := by
    calc (16 : ℝ) = Real.logb 2 ((2 : ℝ) ^ 16) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
          norm_num
      _ ≤ Real.logb 2 N := by
          have hx : (0 : ℝ) < (2 : ℝ) ^ 16 := by positivity
          have hxy : (2 : ℝ) ^ 16 ≤ (N : ℝ) := by
            norm_num
            exact_mod_cast hN
          exact Real.logb_le_logb_of_le (b := 2) (by norm_num) hx hxy
  have hcost : (radixCost 2 N N : ℝ) = 4 * N := by
    rw [radixCost]
    push_cast
    ring
  rw [hcost]
  have hN' : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

/-! ### The word-RAM corollary -/

/-- **Word-RAM `w`-bit probes.**  A key of `n` words of `w` bits is a point of `Key n (2 ^ w)`, so
`U = (2 ^ w) ^ n = 2 ^ (n · w)`; a word read is a `b`-ary probe with `b = 2 ^ w`.  Then `n` word
reads per key are necessary (`passes_lower`) and `n` suffice (`radixProc` with `w`-bit digits), and
`log_b U = n`: the number of *words*, not of bits.  `Instances.Radix.radixCost` charges
`n · (N + 2 ^ w)` for `N` items, i.e. the `2 ^ w` bucket initialisations of each pass. -/
theorem wordram_probes (n w : ℕ) (hw : 0 < w) :
    (∀ (p : ℕ) (P : KeyProc n (2 ^ w) p), p < n → ¬ SortsAllKeys P) ∧
      (∃ P : KeyProc n (2 ^ w) n, SortsAllKeys P) ∧
      Real.logb ((2 : ℝ) ^ w) (Fintype.card (Key n (2 ^ w))) = (n : ℝ) := by
  have hb : 2 ≤ 2 ^ w :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  refine ⟨fun p P hp h => passes_lower hb hp ⟨P, h⟩,
    ⟨radixProc n (2 ^ w), radixProc_sortsAllKeys⟩, ?_⟩
  have hcast : ((Fintype.card (Key n (2 ^ w)) : ℕ) : ℝ) = ((2 : ℝ) ^ w) ^ n := by
    rw [card_Key]
    push_cast
    ring
  rw [hcast, Real.logb_pow, Real.logb_self_eq_one (one_lt_pow₀ (by norm_num) (by omega))]
  ring

end SortBounds.Projects.Domain
