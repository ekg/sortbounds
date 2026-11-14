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

/-- `oneAt j i` is `1` iff `i + 1` is a power of two of exponent `≤ j`.  A decidable test over
the *finite* list of admissible exponents, so that `T j` is a computable list (the `decide`
anchors at the end of M0 rely on that). -/
def oneAt (j i : ℕ) : Bool := (List.range (j + 1)).any fun k => i + 1 == 2 ^ k
/-- `oneAt` reads: `i + 1 = 2^k` for an admissible exponent `k ≤ j`. -/
theorem oneAt_eq_true {j i : ℕ} : oneAt j i = true ↔ ∃ k, k ≤ j ∧ i + 1 = 2 ^ k := by
  simp [oneAt, List.any_eq_true, List.mem_range, beq_iff_eq]
/-- **`T_j`**: the binary word of length `2^j` with a `1` exactly at the positions `2^k - 1`,
`0 ≤ k ≤ j`.  `T_0 = 1`, `T_1 = 11`, `T_2 = 1101`, `T_3 = 11010001`. -/
def T (j : ℕ) : List Bool := (List.range (2 ^ j)).map (oneAt j)
@[simp] theorem T_length (j : ℕ) : (T j).length = 2 ^ j := by simp [T]
/-- **M0: the positions of the ones.**  The `i`-th symbol of `T_j` is `1` iff `i + 1` is a power
of two `2^k` with `k ≤ j`.  This is the characterisation everything else in the lane rests on;
`T_drop_take_block` below gives the run-length form (the gaps are `2^k - 1` zeros). -/
theorem T_getElem_true {j i : ℕ} (hi : i < (T j).length) :
    (T j)[i] = true ↔ ∃ k, k ≤ j ∧ i + 1 = 2 ^ k := by
  rw [show (T j)[i] = oneAt j i by simp [T], oneAt_eq_true]
/-- The same characterisation in `getElem?` form, so that no index bound has to be carried: the
`i`-th symbol is `1` iff `i + 1 = 2^k` for some `k ≤ j`, and there is no `i`-th symbol at all once
`i ≥ 2^j`. -/
theorem T_getElem?_true {j i : ℕ} : (T j)[i]? = some true ↔ ∃ k, k ≤ j ∧ i + 1 = 2 ^ k := by
  by_cases hi : i < (T j).length
  · rw [List.getElem?_eq_getElem hi, Option.some.injEq, T_getElem_true hi]
  · rw [List.getElem?_eq_none (by simpa using hi)]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨k, hk, hk'⟩
    rw [T_length] at hi
    have hlt : 2 ^ j < 2 ^ k := by omega
    have : j < k := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp hlt
    omega

/-! ### Arithmetic of powers of two -/

/-- `2^k ≤ 2^m` for `k ≤ m`. -/
theorem pow2_le_pow2 {k m : ℕ} (h : k ≤ m) : 2 ^ k ≤ 2 ^ m :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mpr h

/-- `2^k < 2^m` for `k < m`. -/
theorem pow2_lt_pow2 {k m : ℕ} (h : k < m) : 2 ^ k < 2 ^ m :=
  (Nat.pow_lt_pow_iff_right (by norm_num)).mpr h

/-- `2^k + 2^k = 2^(k+1)`. -/
theorem pow2_succ_eq (k : ℕ) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; omega

/-- **No power of two lies strictly between `2^k` and `2^(k+1)`** — what makes every gap length
`2^k - 1` unique to its scale. -/
theorem pow2_no_gap {k m : ℕ} (h1 : 2 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 ^ (k + 1)) : False := by
  have h1' : k < m := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h1
  have h2' : m < k + 1 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h2
  omega

/-- `i + 1` is not a power of two when `2^k - 1 < i < 2^(k+1) - 1`. -/
theorem not_pow2_of_between {k i : ℕ} (h1 : 2 ^ k - 1 < i) (h2 : i < 2 ^ (k + 1) - 1) :
    ¬ ∃ m, i + 1 = 2 ^ m := by
  rintro ⟨m, hm⟩
  exact pow2_no_gap (k := k) (m := m) (by omega) (by omega)

/-! ### The block factor `1 0^{2^k-1} 1` -/

/-- `blockFactor k = 1 0^{2^k-1} 1`: the factor spanned by two consecutive `1`s at scale `k` — the
`1` at position `2^k - 1` and the next one at `2^(k+1) - 1`.  (`blockFactor 0 = 11`.) -/
def blockFactor (k : ℕ) : List Bool := true :: (List.replicate (2 ^ k - 1) false ++ [true])

/-- `blockFactor k` has length `2^k + 1` — one more than the gap, the unit that makes the
coverage sets of scales `2m` and `2m + 2` disjoint (an even-scale span ends at `2^{k+1} - 1`). -/
theorem blockFactor_length (k : ℕ) : (blockFactor k).length = 2 ^ k + 1 := by
  simp [blockFactor]
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- `blockFactor k` starts with its first `1`. -/
theorem blockFactor_getElem?_zero (k : ℕ) : (blockFactor k)[0]? = some true := by
  simp [blockFactor]

/-- … continues with the `2^k - 1` zeros. -/
theorem blockFactor_getElem?_mid {k t : ℕ} (h : t < 2 ^ k - 1) :
    (blockFactor k)[t + 1]? = some false := by
  have h1 : (blockFactor k)[t + 1]? = (List.replicate (2 ^ k - 1) false ++ [true])[t]? := by
    simp [blockFactor]
  rw [h1, List.getElem?_append_left (by simpa using h), List.getElem?_replicate_of_lt h]

/-- … and ends with its second `1`. -/
theorem blockFactor_getElem?_last (k : ℕ) : (blockFactor k)[2 ^ k]? = some true := by
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h : 2 ^ k = (2 ^ k - 1) + 1 := by omega
  rw [h]
  have h1 : (blockFactor k)[(2 ^ k - 1) + 1]? =
      (List.replicate (2 ^ k - 1) false ++ [true])[2 ^ k - 1]? := by simp [blockFactor]
  rw [h1, List.getElem?_append_right (by simp)]
  simp

/-- `blockFactor k` has no symbol from index `2^k + 1` on. -/
theorem blockFactor_getElem?_none {k t : ℕ} (h : 2 ^ k + 1 ≤ t) : (blockFactor k)[t]? = none := by
  rw [List.getElem?_eq_none_iff, blockFactor_length]
  exact h

/-! ### The ones of `T_j` -/

/-- The `1` at position `2^m - 1`, for every scale `m ≤ j`. -/
theorem T_getElem?_one {j m : ℕ} (hm : m ≤ j) : (T j)[2 ^ m - 1]? = some true := by
  rw [T_getElem?_true]
  exact ⟨m, hm, by have := Nat.one_le_two_pow (n := m); omega⟩

/-- A position inside the word whose successor is not a power of two carries a `0`. -/
theorem T_getElem?_zero {j i : ℕ} (hi : i < 2 ^ j) (h : ¬ ∃ m, i + 1 = 2 ^ m) :
    (T j)[i]? = some false := by
  have hlen : i < (T j).length := by rwa [T_length]
  have hne : (T j)[i] ≠ true := by
    intro hc
    obtain ⟨m, -, hm⟩ := (T_getElem_true hlen).mp hc
    exact h ⟨m, hm⟩
  rw [List.getElem?_eq_getElem hlen]
  congr
  cases hb : (T j)[i] <;> simp_all

/-! ### M0 — the run lengths -/

/-- **M0, run-length form**: after the `1` at position `2^k - 1` come exactly `2^k - 1` zeros and
then the next `1`, at `2^(k+1) - 1` — the window `[2^k - 1, 2^(k+1))` is `blockFactor k`. -/
theorem T_drop_take_block {j k : ℕ} (hk : k < j) :
    ((T j).drop (2 ^ k - 1)).take (2 ^ k + 1) = blockFactor k := by
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  refine List.ext_getElem? fun t => ?_
  by_cases ht : t < 2 ^ k + 1
  · rw [List.getElem?_take_of_lt ht, List.getElem?_drop]
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      rw [Nat.add_zero, T_getElem?_one (le_of_lt hk), blockFactor_getElem?_zero]
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have hs : s ≤ 2 ^ k - 1 := by omega
      rcases lt_or_eq_of_le hs with hslt | hseq
      · have hbetween1 : 2 ^ k - 1 < 2 ^ k - 1 + (s + 1) := by omega
        have hbetween2 : 2 ^ k - 1 + (s + 1) < 2 ^ (k + 1) - 1 := by
          have := pow2_succ_eq k
          omega
        have hlim : 2 ^ k - 1 + (s + 1) < 2 ^ j := by
          have := pow2_le_pow2 (k := k + 1) (m := j) (by omega)
          omega
        rw [T_getElem?_zero hlim (not_pow2_of_between hbetween1 hbetween2),
          blockFactor_getElem?_mid hslt]
      · subst hseq
        have hidx : 2 ^ k - 1 + (2 ^ k - 1 + 1) = 2 ^ (k + 1) - 1 := by
          have := pow2_succ_eq k
          omega
        have hlast : 2 ^ k - 1 + 1 = 2 ^ k := Nat.sub_add_cancel hp
        rw [hidx, T_getElem?_one (by omega), hlast, blockFactor_getElem?_last]
  · have hbig : 2 ^ k + 1 ≤ t := by omega
    rw [List.getElem?_eq_none (by rw [List.length_take]; exact le_trans (Nat.min_le_left (2 ^ k + 1) _) hbig),
      blockFactor_getElem?_none hbig]


/-- **M0, occurrence form**: `1 0^{2^k-1} 1` really occurs in `T_j` — at position `2^k - 1`. -/
theorem factorOcc_block {j k : ℕ} (hk : k < j) :
    factorOcc (T j) (2 ^ k - 1) (2 ^ (k + 1)) = blockFactor k := by
  have hstep : 2 ^ (k + 1) = 2 ^ k - 1 + (2 ^ k + 1) := by
    have := pow2_succ_eq k
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  rw [hstep, factorOcc_self, T_drop_take_block hk]

/-! ### Sanity anchors on the definitions (small `decide`s only) -/

/-- `T_3 = 11010001`, as in the lane's README. -/
example : T 3 = [true, true, false, true, false, false, false, true] := by decide

example : T 4 = [true, true, false, true] ++ List.replicate 3 false ++ [true] ++
    List.replicate 7 false ++ [true] := by decide

/-- The gap after the `1` at scale `2` is three zeros, and the factor across it is `1 000 1`. -/
example : factorOcc (T 5) (2 ^ 2 - 1) (2 ^ 3) = [true, false, false, false, true] := by decide

/-! ### The two end factors -/

/-- `gapFactor j = 0^{2^{j-2}-1} 1 0`: the window one position to the right of `blockFactor (j-2)`
— the last `1` of that block replaced by a `0` and one trailing `0` added, which keeps the length
`2^{j-2}+1` and makes the coverage set the *next* interval. -/
def gapFactor (j : ℕ) : List Bool := List.replicate (2 ^ (j - 2) - 1) false ++ [true, false]

/-- `tailFactor j = 0^{2^{j-2}} 1`: the final zero run of `T_j` with the last `1`. -/
def tailFactor (j : ℕ) : List Bool := List.replicate (2 ^ (j - 2)) false ++ [true]

theorem gapFactor_length (j : ℕ) : (gapFactor j).length = 2 ^ (j - 2) + 1 := by
  simp [gapFactor]
  have := Nat.one_le_two_pow (n := j - 2)
  omega

theorem tailFactor_length (j : ℕ) : (tailFactor j).length = 2 ^ (j - 2) + 1 := by
  simp [tailFactor]

theorem gapFactor_getElem?_zero {j t : ℕ} (h : t < 2 ^ (j - 2) - 1) :
    (gapFactor j)[t]? = some false := by
  rw [gapFactor, List.getElem?_append_left (by simpa using h), List.getElem?_replicate_of_lt h]

theorem gapFactor_getElem?_one (j : ℕ) : (gapFactor j)[2 ^ (j - 2) - 1]? = some true := by
  simp [gapFactor]

theorem gapFactor_getElem?_last (j : ℕ) : (gapFactor j)[2 ^ (j - 2)]? = some false := by
  have hp : 1 ≤ 2 ^ (j - 2) := Nat.one_le_two_pow
  have h : (2 ^ (j - 2) - 1) + 1 = 2 ^ (j - 2) := Nat.sub_add_cancel hp
  rw [gapFactor, ← h]
  simp

theorem gapFactor_getElem?_none {j t : ℕ} (h : 2 ^ (j - 2) + 1 ≤ t) : (gapFactor j)[t]? = none := by
  rw [List.getElem?_eq_none_iff, gapFactor_length]
  exact h

theorem tailFactor_getElem?_zero {j t : ℕ} (h : t < 2 ^ (j - 2)) :
    (tailFactor j)[t]? = some false := by
  rw [tailFactor, List.getElem?_append_left (by simpa using h), List.getElem?_replicate_of_lt h]

theorem tailFactor_getElem?_one (j : ℕ) : (tailFactor j)[2 ^ (j - 2)]? = some true := by
  simp [tailFactor]

theorem tailFactor_getElem?_none {j t : ℕ} (h : 2 ^ (j - 2) + 1 ≤ t) : (tailFactor j)[t]? = none := by
  rw [List.getElem?_eq_none_iff, tailFactor_length]
  exact h

/-! ### Arithmetic helpers for the two end factors -/

theorem pow2_half {j : ℕ} (hj : 1 ≤ j) : 2 ^ (j - 1) + 2 ^ (j - 1) = 2 ^ j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

theorem pow2_quarter {j : ℕ} (hj : 2 ≤ j) : 2 ^ (j - 2) + 2 ^ (j - 2) = 2 ^ (j - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  rw [show i + 2 - 1 = i + 1 by omega, show i + 2 - 2 = i by omega, pow_succ]
  ring

/-! ### Occurrences of the two end factors -/

theorem factorOcc_getElem? {α : Type*} (l : List α) (a L t : ℕ) (ht : t < L) :
    (factorOcc l a (a + L))[t]? = l[a + t]? := by
  rw [factorOcc_self, List.getElem?_take_of_lt ht, List.getElem?_drop]

theorem T_drop_take_gap {j : ℕ} (hj : 3 ≤ j) :
    ((T j).drop (2 ^ (j - 2))).take (2 ^ (j - 2) + 1) = gapFactor j := by
  have hq := pow2_quarter (j := j) (by omega)
  have hh := pow2_half (j := j) (by omega)
  have hp : 1 ≤ 2 ^ (j - 2) := Nat.one_le_two_pow
  have hp1 : 1 < 2 ^ (j - 2) := Nat.one_lt_two_pow (by omega)
  refine List.ext_getElem? fun t => ?_
  by_cases ht : t < 2 ^ (j - 2) + 1
  · rw [List.getElem?_take_of_lt ht, List.getElem?_drop]
    by_cases hA : t < 2 ^ (j - 2) - 1
    · rw [T_getElem?_zero (j := j) (i := 2 ^ (j - 2) + t) (by omega)
        (not_pow2_of_between (k := j - 2) (by omega) (by omega)), gapFactor_getElem?_zero hA]
    · by_cases hB : t = 2 ^ (j - 2) - 1
      · subst hB
        have hidx : 2 ^ (j - 2) + (2 ^ (j - 2) - 1) = 2 ^ (j - 1) - 1 := by omega
        rw [hidx, T_getElem?_one (by omega), gapFactor_getElem?_one]
      · have hC : t = 2 ^ (j - 2) := by omega
        subst hC
        have hidx : 2 ^ (j - 2) + 2 ^ (j - 2) = 2 ^ (j - 1) := hq
        rw [hidx, T_getElem?_zero (j := j) (i := 2 ^ (j - 1)) (by omega)
          (not_pow2_of_between (k := j - 1) (by omega) (by omega)), gapFactor_getElem?_last]
  · have hbig : 2 ^ (j - 2) + 1 ≤ t := by omega
    rw [List.getElem?_eq_none (by rw [List.length_take]; exact le_trans (Nat.min_le_left _ _) hbig),
      gapFactor_getElem?_none hbig]

theorem T_drop_take_tail {j : ℕ} (hj : 3 ≤ j) :
    ((T j).drop (2 ^ j - 2 ^ (j - 2) - 1)).take (2 ^ (j - 2) + 1) = tailFactor j := by
  have hq := pow2_quarter (j := j) (by omega)
  have hh := pow2_half (j := j) (by omega)
  have hp : 1 ≤ 2 ^ (j - 2) := Nat.one_le_two_pow
  have hp1 : 1 < 2 ^ (j - 2) := Nat.one_lt_two_pow (by omega)
  refine List.ext_getElem? fun t => ?_
  by_cases ht : t < 2 ^ (j - 2) + 1
  · rw [List.getElem?_take_of_lt ht, List.getElem?_drop]
    by_cases hA : t < 2 ^ (j - 2)
    · rw [T_getElem?_zero (j := j) (i := 2 ^ j - 2 ^ (j - 2) - 1 + t) (by omega)
        (not_pow2_of_between (k := j - 1) (by omega) (by omega)), tailFactor_getElem?_zero hA]
    · have hC : t = 2 ^ (j - 2) := by omega
      subst hC
      have hidx : 2 ^ j - 2 ^ (j - 2) - 1 + 2 ^ (j - 2) = 2 ^ j - 1 := by omega
      rw [hidx, T_getElem?_one (by omega), tailFactor_getElem?_one]
  · have hbig : 2 ^ (j - 2) + 1 ≤ t := by omega
    rw [List.getElem?_eq_none (by rw [List.length_take]; exact le_trans (Nat.min_le_left _ _) hbig),
      tailFactor_getElem?_none hbig]

theorem factorOcc_gap {j : ℕ} (hj : 3 ≤ j) :
    factorOcc (T j) (2 ^ (j - 2)) (2 ^ (j - 1) + 1) = gapFactor j := by
  have hq := pow2_quarter (j := j) (by omega)
  have hstep : 2 ^ (j - 1) + 1 = 2 ^ (j - 2) + (2 ^ (j - 2) + 1) := by
    rw [← hq]; ring
  rw [hstep, factorOcc_self, T_drop_take_gap hj]

theorem factorOcc_tail {j : ℕ} (hj : 3 ≤ j) :
    factorOcc (T j) (2 ^ j - 2 ^ (j - 2) - 1) (2 ^ j) = tailFactor j := by
  have hq := pow2_quarter (j := j) (by omega)
  have hh := pow2_half (j := j) (by omega)
  have hp : 1 ≤ 2 ^ (j - 2) := Nat.one_le_two_pow
  set a := 2 ^ j - 2 ^ (j - 2) - 1 with ha
  have hstep : 2 ^ j = a + (2 ^ (j - 2) + 1) := by rw [ha]; omega
  rw [hstep, factorOcc_self, ha, T_drop_take_tail hj]

end SortBounds.Projects.PowersOfTwo
