/-
SortBounds/Projects/FordJohnson/Jacobsthal.lean

Milestone **M2** of the `FordJohnson` lane, second half: the *literature's* count `F(n)` of
merge-insertion, as a Jacobsthal-order schedule.

`MergeInsertion.lean`/`Count.lean` bound the schedule in which every loser is inserted into
the whole chain of winners; that is `O(n log n)` but not what Ford and Johnson do.  The real
algorithm inserts the losers in **Jacobsthal order** — rank `1`, then `3, 2`, then `5, 4`,
then `11, 10, … , 6`, … — and each loser is searched for only among the chain elements below
its own partner.  Two things happen:

* the `t`-th item of the order is inserted when `s` items are already in the chain, and only
  `⌈log₂ (t + s + 1)⌉` comparisons are needed (the `t-1` winners below its partner plus the
  `s` inserted elements); inside one Jacobsthal batch `t + s` is *constant*, so the batch
  costs the same per item and the windows stay perfectly balanced;
* the price of that is one extra comparison per item compared with the whole-chain schedule.

This file is the arithmetic half: the Jacobsthal numbers, the cost `jacInsertCost` of the
insertion phase, the recurrence `fjCountJ` (`n/2 + fjCountJ (n/2) + jacInsertCost ⌈n/2⌉`) and
the table

  `fjCountJ 4 = 5`, `7`, `10`, `13`, `16`, `19`, `22`, `26` (= `F 5 … F 11`),

which is exactly the optimal `S(n)` for `n ≤ 11`, together with `fjCountJ n = ⌈log₂ n!⌉`
there.  `JacobsthalInsertion.lean` proves that the algorithm really does sort with that
count; here `fjCountJ` is only arithmetic.
-/
import SortBounds.Projects.FordJohnson.Count

namespace SortBounds.Projects.FordJohnson

/-! ### Jacobsthal numbers -/

/-- The Jacobsthal numbers in the form merge-insertion uses them, `1, 3, 5, 11, 21, 43, …`:
the classical sequence `J₂, J₃, J₄, …` (it starts with a repeated `J₀ = J₁ = 1`, and no
insertion batch is empty, so the repetition is divided out here). -/
def jac : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | k + 2 => jac (k + 1) + 2 * jac k

/-- The first `k` batches of the insertion order hold the ranks `1 … jacPred k`, so `jacPred k`
is both the number of items inserted before batch `k` and the rank of the last item of batch
`k-1`. -/
def jacPred : ℕ → ℕ
  | 0 => 0
  | k + 1 => jac k

theorem jacPred_succ (k : ℕ) : jacPred (k + 1) = jac k := rfl

theorem jac_succ_succ (k : ℕ) : jac (k + 2) = jac (k + 1) + 2 * jac k := rfl

theorem jac_pos (k : ℕ) : 0 < jac k := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k h1 h2 => rw [jac_succ_succ]; omega

/-- Consecutive Jacobsthal numbers increase, so every batch of the insertion order is
nonempty and `⌈n/2⌉` batches always suffice. -/
theorem jac_lt_succ (k : ℕ) : jac k < jac (k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k _ _ =>
    have e1 : jac (k + 2) = jac (k + 1) + 2 * jac k := jac_succ_succ k
    have e2 : jac (k + 3) = jac (k + 2) + 2 * jac (k + 1) := by
      rw [show k + 3 = (k + 1) + 2 by omega, jac_succ_succ]
    have hp := jac_pos (k + 1)
    show jac (k + 2) < jac (k + 3)
    omega

/-- `jac` grows at least linearly: `k + 1 ≤ jac k`, so `M` batches always cover `M` items. -/
theorem le_jac (k : ℕ) : k + 1 ≤ jac k := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k _ h2 =>
    have h := jac_lt_succ (k + 1)
    rw [show k + 2 = k + 1 + 1 by omega, show k + 2 + 1 = k + 1 + 1 + 1 by omega]
    omega

theorem jac_strictMono : StrictMono jac :=
  strictMono_nat_of_lt_succ jac_lt_succ

theorem jacPred_le_jac (k : ℕ) : jacPred k ≤ jac k := by
  cases k with
  | zero => decide
  | succ k => rw [jacPred_succ]; exact le_of_lt (jac_lt_succ k)

/-- The defining identity of the Jacobsthal numbers, in the shape the insertion order uses
it: two consecutive batches together hold `2^(k+1)` ranks. -/
theorem jac_add_succ (k : ℕ) : jac k + jac (k + 1) = 2 ^ (k + 2) := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k _ h2 =>
    rw [show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega] at h2
    have e2 : jac (k + 3) = jac (k + 2) + 2 * jac (k + 1) := by
      rw [show k + 3 = (k + 1) + 2 by omega, jac_succ_succ]
    have e3 : 2 ^ (k + 4) = 2 * 2 ^ (k + 3) := by
      rw [show k + 4 = (k + 3) + 1 by omega, pow_succ']
    show jac (k + 2) + jac (k + 3) = 2 ^ (k + 4)
    omega

/-- Batch `k` searches for its items in a window of at most `2^(k+1)` slots: the `jacPred k`
winners already below the partner plus the `jac k` items in the chain once the batch is
done.  This is where the Jacobsthal numbers get their name: the windows are exact powers of
two, so the binary search that follows is perfectly balanced. -/
theorem jacPred_add_jac_le (k : ℕ) : jacPred k + jac k ≤ 2 ^ (k + 1) := by
  cases k with
  | zero => decide
  | succ k =>
    rw [jacPred_succ]
    have := jac_add_succ k
    rw [show k + 1 + 1 = k + 2 by omega]
    omega

/-! ### The cost of the Jacobsthal insertion phase -/

/-- The comparisons the insertion phase spends: batch `k` inserts the ranks
`jacPred k + 1 … min M (jac k)` — `min M (jac k) - jacPred k` items — and each of them is
searched for in a window of `jacPred k + min M (jac k)` slots (the winners below its partner
plus the items already inserted), so each costs `⌈log₂ (⌈window⌉)⌉`. -/
def jacInsertCostAux (M : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, k =>
    (min M (jac k) - min M (jacPred k))
        * Nat.clog 2 (min M (jacPred k) + min M (jac k))
      + jacInsertCostAux M fuel (k + 1)

/-- **The literature's count of the loser insertions of merge-insertion.**  `M = ⌈n/2⌉` items
(`⌊n/2⌋` losers plus, for odd `n`, the unpaired element) are inserted in Jacobsthal order;
`M` batches always suffice because `jac k ≥ k + 1`. -/
def jacInsertCost (M : ℕ) : ℕ := jacInsertCostAux M M 0

/-- The recurrence of `fjCountJ`, iterated from the bottom.  `fuel` bounds the number of
halvings of `n`; because `n/2 < n`, `fuel = n` is always enough. -/
def fjCountJAux (fuel n : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    if n < 2 then 0 else n / 2 + fjCountJAux fuel (n / 2) + jacInsertCost ((n + 1) / 2)

/-- **`F(n)`, the comparison count of merge-insertion in the literature's form.**

`⌊n/2⌋` comparisons pair the elements, `F(⌊n/2⌋)` sorts the winners recursively, and the
insertion phase costs `jacInsertCost ⌈n/2⌉`: `⌊n/2⌋` losers in Jacobsthal order, plus the
unpaired element of an odd-length input — inserted like a loser, in the same order, but with
no upper bound of its own. -/
def fjCountJ (n : ℕ) : ℕ := fjCountJAux n n

/-- Extra fuel does not change the count: every chain of halvings reaches `1` first. -/
theorem fjCountJAux_congr (n : ℕ) : ∀ fuel₁ fuel₂ : ℕ, n ≤ fuel₁ → n ≤ fuel₂ →
    fjCountJAux fuel₁ n = fjCountJAux fuel₂ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro fuel₁ fuel₂ h₁ h₂
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · rcases fuel₁ with _ | f₁ <;> rcases fuel₂ with _ | f₂ <;> simp [fjCountJAux, hlt]
    · rcases fuel₁ with _ | f₁
      · omega
      rcases fuel₂ with _ | f₂
      · omega
      have hlt : ¬ n < 2 := by omega
      simp only [fjCountJAux, hlt, ite_false]
      rw [ih (n / 2) (by omega) f₁ f₂ (by omega) (by omega)]

/-- The recurrence shape of `fjCountJ`: pair, recurse on the winners, then insert. -/
theorem fjCountJ_le_recurrence (n : ℕ) (hn : 2 ≤ n) :
    fjCountJ n = n / 2 + fjCountJ (n / 2) + jacInsertCost ((n + 1) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show fjCountJAux (m + 1) (m + 1) = (m + 1) / 2 + fjCountJAux ((m + 1) / 2) ((m + 1) / 2)
    + jacInsertCost ((m + 1 + 1) / 2)
  have hlt : ¬ m + 1 < 2 := by omega
  simp only [fjCountJAux, hlt, ite_false]
  rw [fjCountJAux_congr ((m + 1) / 2) m ((m + 1) / 2) (by omega) (by omega)]

/-- Nothing is inserted for a list of at most one element. -/
theorem fjCountJ_eq_zero (n : ℕ) (h : n < 2) : fjCountJ n = 0 := by
  show fjCountJAux n n = 0
  rcases n with _ | _ | n
  · rfl
  · rw [fjCountJAux]
    simp
  · omega

/-! ### The table -/

/-- The cost of the insertion phase, computed. -/
theorem jacInsertCost_table : jacInsertCost 1 = 0 ∧ jacInsertCost 2 = 2 ∧ jacInsertCost 3 = 4
    ∧ jacInsertCost 4 = 7 ∧ jacInsertCost 5 = 10 ∧ jacInsertCost 6 = 14 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The count of merge-insertion on `n = 4 … 11` elements**: `5, 7, 10, 13, 16, 19, 22,
26`.  These are Ford and Johnson's values `F(4) … F(11)`, and they coincide with the optimal
number of comparisons `S(n)` — the information-theoretic bound `⌈log₂ n!⌉` is reached. -/
theorem fjCountJ_table : fjCountJ 4 = 5 ∧ fjCountJ 5 = 7 ∧ fjCountJ 6 = 10 ∧ fjCountJ 7 = 13
    ∧ fjCountJ 8 = 16 ∧ fjCountJ 9 = 19 ∧ fjCountJ 10 = 22 ∧ fjCountJ 11 = 26 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The closed form of the count** (Knuth, TAOCP 5.3.1): `F(n) = Σ_{k=1}^{n} ⌈log₂ ⌈3k/4⌉⌉`,
i.e. the `k`-th element of the insertion sequence is searched for in `⌈3k/4⌉` slots.  Checked
here for every `n ≤ 22`, which covers the whole range where merge-insertion is known to be
optimal. -/
theorem fjCountJ_eq_sum (n : ℕ) (hn : n ≤ 22) :
    fjCountJ n = ∑ k ∈ Finset.range n, Nat.clog 2 ((3 * (k + 1) + 3) / 4) := by
  interval_cases n <;> decide

/-- **Merge-insertion is optimal up to eleven elements**: for `4 ≤ n ≤ 11` its count equals
the information-theoretic lower bound `⌈log₂ n!⌉`, which no comparison sort can beat. -/
theorem fjCountJ_eq_clog_factorial (n : ℕ) (h4 : 4 ≤ n) (h11 : n ≤ 11) :
    fjCountJ n = Nat.clog 2 (Nat.factorial n) := by
  interval_cases n <;> decide

/-- The two further sizes where merge-insertion is known to be optimal: `n = 20` and `n = 21`
(Ford–Johnson themselves; see `docs/PRIOR-ART.md`). -/
theorem fjCountJ_eq_clog_factorial_large : fjCountJ 20 = Nat.clog 2 (Nat.factorial 20)
    ∧ fjCountJ 21 = Nat.clog 2 (Nat.factorial 21) := by
  refine ⟨?_, ?_⟩ <;> decide

end SortBounds.Projects.FordJohnson
