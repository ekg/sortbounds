/-
SortBounds/Projects/PowersOfTwo/PowersOfTwo.lean

**Lane 7, milestones M0 and M1: the extremal family `T_j` and the packing lower bound
`γ(T_j) ≥ ⌈j/2⌉ + 1`.**

`T_j` is the binary word of length `2^j` whose `i`-th symbol (0-indexed) is `1` exactly when
`i + 1` is a power of two:

```
T_1 = 11            T_2 = 1101            T_3 = 11010001
T_4 = 1101000100000001
```

Equivalently `T_j` is `1` at the positions `2^k - 1`, `0 ≤ k ≤ j` — one `1` per *scale* `k` —
so the zero-runs between consecutive `1`s have lengths `0, 1, 3, 7, 15, … = 2^k - 1`: every run
length occurs **exactly once**.  The scale index convention is `k ≤ j` (hence `j + 1` ones):
this is forced by the README's own examples above (`T_1 = 11` needs both `k = 0` and `k = 1`),
and it is the convention in which the measured values `γ(T_j) = ⌈j/2⌉ + 1` (`j = 3 … 13`,
`docs/research/CONJECTURES.md`, "C-new") hold.  The README's prose writes `k < j`, an off-by-one
against its own table.

Contents:

* **M0** `T`, `oneAt` (the indicator of "`i + 1` is a power of two"), `T_length`, and the
  characterisation `T_getElem_true` of exactly which positions carry a `1` — plus the run-length
  form `T_block`: the window from the `1` at `2^k - 1` to the `1` at `2^{k+1} - 1` is
  `1 0^{2^k-1} 1`, i.e. the gap after scale `k` is exactly `2^k - 1` zeros.
* **M1** `gamma_ge`: `⌈j/2⌉ + 1 ≤ minAttractorSize (T j)` for `3 ≤ j`, from the packing lemma
  `Packing.card_le_minAttractorSize_of_pairwiseDisjoint` applied to `⌈j/2⌉ + 1` factors whose
  coverage sets are pairwise disjoint.

**The packing.**  Each factor below occurs exactly once in `T_j`, so its coverage set is the
single interval spanned by that occurrence:

| factor | length | unique occurrence | coverage |
| --- | --- | --- | --- |
| `blockFactor k = 1 0^{2^k-1} 1` (`k` even, `k ≤ j - 3`) | `2^k + 1` | `2^k - 1` | `[2^k - 1, 2^{k+1} - 1]` |
| `gapFactor j = 1` | `2^{j-2} + 1` | `2^{j-1} - 1` | `[2^{j-2}, 2^{j-1}]` |
| `tailFactor j = 0^{2^{j-2}} 1` | `2^{j-2} + 1` | `2^j - 1` | `[2^j - 2^{j-2} - 1, 2^j - 1]` |

(the `gapFactor` is `0^{2^{j-2}-1} 1 0`, the `blockFactor` of scale `j - 2` shifted one position
right — the leading `1` is replaced by a `0` and a trailing `0` restores the length, which is how
the last *pair* of scales is squeezed into one interval instead of one-per-scale).  Even scales
`0, 2, …, K` give `⌊(j-3)/2⌋ + 1` disjoint intervals ending at `2^{K+1} - 1 ≤ 2^{j-2} - 1`, and
the two extra intervals start at `2^{j-2}` and at `3·2^{j-2} - 1 > 2^{j-1}`: `⌊(j-3)/2⌋ + 3 =
⌈j/2⌉ + 1` pairwise disjoint intervals.

`δ(T_j) = 2` (M2), the upper bound `γ(T_j) ≤ ⌈j/2⌉ + 1` (M3) and
`gamma_unbounded_over_delta` (M4) are **not** in this file; only M0 and M1 are.
-/
import Mathlib
import SortBounds.Projects.Repetitiveness.Basic
import SortBounds.Projects.AttractorLP.Gap
import SortBounds.Projects.Packing.Packing

namespace SortBounds.Projects.PowersOfTwo

open SortBounds.Projects.Repetitiveness SortBounds.Projects.AttractorLP SortBounds.Projects.Packing

/-! ### M0 — the word `T_j` and the positions of its ones -/

/-- `oneAt j i` is `1` iff `i + 1` is a power of two of exponent `≤ j`.  Written as a decidable
test over the *finite* list of admissible exponents, so that `T j` is a computable list and the
`sanity anchors` at the end of M0 can be checked by `decide`. -/
def oneAt (j i : ℕ) : Bool := (List.range (j + 1)).any fun k => i + 1 == 2 ^ k

theorem oneAt_eq_true {j i : ℕ} : oneAt j i = true ↔ ∃ k, k ≤ j ∧ i + 1 = 2 ^ k := by
  simp [oneAt, List.any_eq_true, List.mem_range, beq_iff_eq]

/-- **`T_j`**: the binary word of length `2^j` with a `1` exactly at the positions `2^k - 1`,
`0 ≤ k ≤ j` (`= 2^j` before the end).  `T_0 = 1`, `T_1 = 11`, `T_2 = 1101`, `T_3 = 11010001`. -/
def T (j : ℕ) : List Bool := (List.range (2 ^ j)).map (oneAt j)

@[simp]
theorem T_length (j : ℕ) : (T j).length = 2 ^ j := by simp [T]

/-- **M0: the positions of the ones.**  The `i`-th symbol of `T_j` is `1` iff `i + 1` is a power
of two `2^k` with `k ≤ j`.  This is the characterisation everything else in the lane rests on;
`T_block` below gives the run-length form (the gaps are `2^k - 1` zeros). -/
theorem T_getElem_true {j i : ℕ} (hi : i < (T j).length) :
    (T j)[i] = true ↔ ∃ k, k ≤ j ∧ i + 1 = 2 ^ k := by
  rw [show (T j)[i] = oneAt j i by simp [T], oneAt_eq_true]

/-- The same characterisation with `getElem?`, so that no index bound has to be carried: the
`i`-th symbol is `1` iff `i + 1 = 2^k` for some `k ≤ j`, and there is no `i`-th symbol at all
once `i ≥ 2^j`. -/
theorem T_getElem?_true {j i : ℕ} : (T j)[i]? = some true ↔ ∃ k, k ≤ j ∧ i + 1 = 2 ^ k := by
  by_cases hi : i < (T j).length
  · rw [List.getElem?_eq_getElem hi, T_getElem_true hi]
  · rw [List.getElem?_eq_none (by simpa using hi)]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨k, hk, hk'⟩
    rw [T_length] at hi
    have : 2 ^ k ≤ 2 ^ j := by rw [← hk']; omega
    exact absurd (Nat.pow_le_pow_iff_right (by norm_num) |>.mp this) (by omega)

end SortBounds.Projects.PowersOfTwo
