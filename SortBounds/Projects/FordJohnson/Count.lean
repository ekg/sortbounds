/-
SortBounds/Projects/FordJohnson/Count.lean

Milestone **M2** of the `FordJohnson` lane, first half: an *explicit, machine-checked*
`O(n log n)` bound for the count of merge-insertion.

`MergeInsertion.lean` states the recurrence `fjCount` of the schedule implemented by
`fjSort`, but says nothing about its growth rate.  Here we bound it:

* `insertAllCost_le`   — `n` binary insertions into a chain that starts with `k` elements
                          cost at most `n * ⌈log₂ (k+n)⌉`;
* `loserCost_le`       — inserting the `⌊n/2⌋` losers into the chain of winners costs at
                          most `m * (⌈log₂ (m+1)⌉ + 1)`;
* `fjCount_le`         — **`fjCount n ≤ n * (⌈log₂ n⌉ + 1)`**, i.e. merge-insertion is an
                          `n log n` algorithm, with an explicit constant.

Note what is *not* claimed here: `fjCount` is the count of the crude schedule of
`MergeInsertion.lean` (every loser is inserted into the whole chain of winners), not the
optimal `F(n)` of the literature.  The logarithm below comes from the `⌊n/2⌋` recursive
`clog` terms and the `⌊n/2⌋` loser insertions; the Jacobsthal-order schedule of
`JacobsthalInsertion.lean` sharpens the same recurrence to the literature's `F(n)`.
-/
import SortBounds.Projects.FordJohnson.MergeInsertion

namespace SortBounds.Projects.FordJohnson

/-! ### The cost of a batch of binary insertions -/

/-- The recursion step of `insertAllCost`. -/
theorem insertAllCost_succ (k n : ℕ) :
    insertAllCost k (n + 1) = Nat.clog 2 (k + 1) + insertAllCost (k + 1) n := by
  simp only [insertAllCost]

/-- **A batch of `n` binary insertions costs at most `n ⌈log₂ (k+n)⌉`.**  The chain grows
from `k` to `k + n` elements while the batch runs, so every single insertion sees at most
`k + n` elements — fewer than `2^(⌈log₂ (k+n)⌉)`, hence costs at most `⌈log₂ (k+n)⌉`. -/
theorem insertAllCost_le (k n : ℕ) : insertAllCost k n ≤ n * Nat.clog 2 (k + n) := by
  induction n generalizing k with
  | zero => simp [insertAllCost]
  | succ n ih =>
    rw [insertAllCost_succ]
    show Nat.clog 2 (k + 1) + insertAllCost (k + 1) n ≤ (n + 1) * Nat.clog 2 (k + n + 1)
    have hmono : Nat.clog 2 (k + 1) ≤ Nat.clog 2 (k + n + 1) :=
      Nat.clog_mono_right 2 (by omega)
    have hrec : insertAllCost (k + 1) n ≤ n * Nat.clog 2 (k + n + 1) := by
      have := ih (k + 1)
      rwa [show k + 1 + n = k + n + 1 by omega] at this
    nlinarith

/-- The comparisons merge-insertion spends inserting the `m` losers, bounded explicitly. -/
theorem loserCost_le (m : ℕ) : loserCost m ≤ m * Nat.clog 2 (m + m) :=
  insertAllCost_le m m

/-- The same bound in the shape `m (⌈log₂ (m+1)⌉ + 1)`. -/
theorem loserCost_le_succ (m : ℕ) : loserCost m ≤ m * (Nat.clog 2 (m + 1) + 1) := by
  have hmono : Nat.clog 2 (m + m) ≤ Nat.clog 2 (m + 1) + 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [clog_two_add m hm]
      exact Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1
  exact (loserCost_le m).trans (Nat.mul_le_mul_left m hmono)

/-! ### Powers of two against `⌈log₂ ·⌉` -/

/-- `2^(⌈log₂ m⌉) ≤ 2m` for `m ≥ 1`: the ceiling never overshoots by a whole factor. -/
theorem pow_clog_two_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ Nat.clog 2 m ≤ m + m := by
  rcases Nat.eq_or_lt_of_le hm with rfl | hm2
  · simp
  · have hpos : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) hm2
    have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hm2
    have hsplit : 2 ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m).pred := by
      conv_lhs => rw [show Nat.clog 2 m = (Nat.clog 2 m).pred + 1 by
        rw [Nat.succ_pred_eq_of_pos hpos]]
      rw [pow_succ']
    rw [hsplit]
    have := Nat.mul_le_mul_left 2 hlt.le
    omega

/-- The odd term of `fjCount` is strictly bigger than `⌈log₂ (n/2)⌉`: adding the unpaired
element does need a fresh bit of search. -/
theorem clog_two_mul_add_lt (m : ℕ) (hm : 1 ≤ m) :
    Nat.clog 2 m < Nat.clog 2 (m + m + 1) := by
  rw [Nat.lt_clog_iff_pow_lt (by norm_num)]
  have h := pow_clog_two_le m hm
  omega

/-- The odd term of `fjCount` overshoots `⌈log₂ (n/2)⌉` by at most two. -/
theorem clog_two_mul_add_one_le (m : ℕ) : Nat.clog 2 (m + m + 1) ≤ Nat.clog 2 m + 2 := by
  have hsplit : Nat.clog 2 (m + m + 1) ≤ Nat.clog 2 ((m + 1) + (m + 1)) :=
    Nat.clog_mono_right 2 (by omega)
  rw [clog_two_add (m + 1) (by omega)] at hsplit
  have hmono : Nat.clog 2 (m + 1) ≤ Nat.clog 2 m + 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [← clog_two_add m hm]
      exact Nat.clog_mono_right 2 (by omega)
  omega

/-! ### The count of merge-insertion is `O(n log n)` -/

/-- **Merge-insertion is an `n log n` algorithm.**  The count `fjCount` of the schedule
implemented by `fjSort` satisfies `fjCount n ≤ n (⌈log₂ n⌉ + 1)`.

Recurrence: `⌊n/2⌋` comparisons pair the elements, the recursive call on the `⌊n/2⌋`
winners costs `⌈log₂ (n/2)⌉ + 1` bits per winner, each of the `⌊n/2⌋` losers costs at most
`⌈log₂ (n/2)⌉ + 1` comparisons, and the unpaired element costs two bits more than
`⌈log₂ (n/2)⌉` at worst — the slack of `2⌊n/2⌋` elements covers it. -/
theorem fjCount_le (n : ℕ) : fjCount n ≤ n * (Nat.clog 2 n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n <;> simp [fjCount]
    · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- `n = 2m`: no unpaired element
        subst hm
        have hm1 : 1 ≤ m := by omega
        have hstep : fjCount (m + m) = m + fjCount m + loserCost m := by
          rw [fjCount]
          rw [if_neg (by omega : ¬ m + m < 2)]
          rw [show (m + m) / 2 = m by omega, show (m + m) % 2 = 0 by omega]
          simp
        rw [hstep]
        have hrec : fjCount m ≤ m * (Nat.clog 2 m + 1) := ih m (by omega)
        have hlos : loserCost m ≤ m * (Nat.clog 2 m + 1) := by
          have := loserCost_le m
          rwa [clog_two_add m hm1] at this
        have hclog : Nat.clog 2 (m + m) = Nat.clog 2 m + 1 := clog_two_add m hm1
        rw [hclog]
        nlinarith
      · -- `n = 2m+1`: the unpaired element costs at most two extra bits
        subst hm
        have hm1 : 1 ≤ m := by omega
        have hstep : fjCount (m + m + 1) =
            m + fjCount m + loserCost m + Nat.clog 2 (m + m + 1) := by
          rw [fjCount]
          rw [if_neg (by omega : ¬ m + m + 1 < 2)]
          rw [show (m + m + 1) / 2 = m by omega, show (m + m + 1) % 2 = 1 by omega]
          simp
        rw [hstep]
        have hrec : fjCount m ≤ m * (Nat.clog 2 m + 1) := ih m (by omega)
        have hlos : loserCost m ≤ m * (Nat.clog 2 m + 1) := by
          have := loserCost_le m
          rwa [clog_two_add m hm1] at this
        have hbig := clog_two_mul_add_lt m hm1
        have hsmall := clog_two_mul_add_one_le m
        nlinarith

end SortBounds.Projects.FordJohnson
