/-
SortBounds/UpperBound.lean

The matching upper bound: an explicit comparison-based sorting algorithm together
with its comparison count.

`SortBounds/Tree.lean` shows that *every* correct comparison sort needs at least
`Nat.factorial n ≤ 2 ^ depth` comparisons in the worst case.  To see that this lower
bound is attained up to a constant, we need an actual algorithm whose comparison
count is `O(n log n)`.  Below we instrument merge sort with a counter: `msortCount`
and `mergeCount` return the number of applications of the comparison `le` together
with the sorted list, and we prove

* the result is sorted (`msortCount_sorted`),
* the result is a permutation of the input (`msortCount_perm`),
* the number of comparisons is at most `2 * n * (Nat.clog 2 n + 1)`,
  where `n` is the length of the input (`msortCount_le`).

Since `2 * n * (⌈log₂ n⌉ + 1) = O(n log n)`, this matches, up to a constant factor, the
`n log n` lower bound `SortBounds.factorial_le_two_pow_depth` proved in `SortBounds/Tree.lean`.
-/
import Mathlib

namespace SortBounds

variable {α : Type*}

/-! ### A merge with a comparison counter -/

/-- `mergeCount le l₁ l₂` merges the lists `l₁` and `l₂` (presumed sorted) and returns
the number of times `le` was applied together with the merged list.  Exactly one
comparison is spent per element that is taken from one of the two input lists. -/
def mergeCount (le : α → α → Bool) : List α → List α → ℕ × List α
  | [], ys => (0, ys)
  | xs, [] => (0, xs)
  | x :: xs, y :: ys =>
    if le x y then
      let r := mergeCount le xs (y :: ys)
      (r.1 + 1, x :: r.2)
    else
      let r := mergeCount le (x :: xs) ys
      (r.1 + 1, y :: r.2)

/-- `mergeCount` computes the ordinary (uncounted) `List.merge`. -/
theorem mergeCount_snd_eq_merge (le : α → α → Bool) (l₁ l₂ : List α) :
    (mergeCount le l₁ l₂).2 = l₁.merge l₂ le := by
  induction l₁ generalizing l₂ with
  | nil => simp [mergeCount]
  | cons x xs ih =>
    induction l₂ with
    | nil => simp [mergeCount]
    | cons y ys ih₂ =>
      simp only [mergeCount, List.merge]
      split_ifs with h
      · simp [ih]
      · simp [ih₂]

/-- Merging produces a permutation of the concatenation of the inputs. -/
theorem mergeCount_perm (le : α → α → Bool) (l₁ l₂ : List α) :
    (mergeCount le l₁ l₂).2.Perm (l₁ ++ l₂) := by
  rw [mergeCount_snd_eq_merge]
  exact List.merge_perm_append le

/-- Merging preserves the total length. -/
theorem mergeCount_length (le : α → α → Bool) (l₁ l₂ : List α) :
    (mergeCount le l₁ l₂).2.length = l₁.length + l₂.length := by
  rw [mergeCount_snd_eq_merge, List.length_merge]

/-- **Merging `l₁` and `l₂` costs at most `l₁.length + l₂.length` comparisons.** -/
theorem mergeCount_counts_le (le : α → α → Bool) (l₁ l₂ : List α) :
    (mergeCount le l₁ l₂).1 ≤ l₁.length + l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp [mergeCount]
  | cons x xs ih =>
    induction l₂ with
    | nil => simp [mergeCount]
    | cons y ys ih₂ =>
      simp only [mergeCount]
      split_ifs with h
      · have h1 := ih (y :: ys)
        simp only [List.length_cons] at h1 ⊢
        omega
      · have h2 := ih₂
        simp only [List.length_cons] at h2 ⊢
        omega

/-! ### Merge sort with a comparison counter -/

/-- `msortCount le l` sorts `l` by merge sort and returns the number of applications
of `le` together with the sorted list.  The list is split into its first
`⌈l.length / 2⌉` elements and the rest, so the recursion has depth `⌈log₂ l.length⌉`. -/
def msortCount (le : α → α → Bool) : List α → ℕ × List α
  | [] => (0, [])
  | [a] => (0, [a])
  | a :: b :: rest =>
    let l := a :: b :: rest
    let k := (l.length + 1) / 2
    let m₁ := msortCount le (l.take k)
    let m₂ := msortCount le (l.drop k)
    let m := mergeCount le m₁.2 m₂.2
    (m₁.1 + m₂.1 + m.1, m.2)
termination_by l => l.length
decreasing_by all_goals simp_wf; omega

/-- Merge sort outputs a permutation of its input (so it neither loses nor duplicates
elements). -/
theorem msortCount_perm (le : α → α → Bool) (l : List α) : (msortCount le l).2.Perm l := by
  induction l using msortCount.induct (le := le) with
  | case1 => simp [msortCount.eq_1]
  | case2 a => simp [msortCount.eq_2]
  | case3 a b rest l k hTake hDrop =>
    rw [msortCount.eq_3]
    simp only
    refine ((mergeCount_perm le _ _).trans (hTake.append hDrop)).trans ?_
    rw [List.take_append_drop]

/-- Merge sort preserves the total length. -/
theorem msortCount_length (le : α → α → Bool) (l : List α) :
    (msortCount le l).2.length = l.length :=
  (msortCount_perm le l).length_eq

/-! ### Correctness -/

section LinearOrder

variable [LinearOrder α]

/-- `Pairwise` for the boolean comparison `decide (· ≤ ·)` and for `(· ≤ ·)` agree. -/
theorem pairwise_decide_le_iff {l : List α} :
    l.Pairwise (fun a b => ((· ≤ ·) : α → α → Bool) a b = true) ↔ l.Pairwise (· ≤ ·) := by
  constructor
  · intro h
    exact h.imp fun hab => by simpa using hab
  · intro h
    exact h.imp fun hab => by simpa using hab

/-- Merging two sorted lists gives a sorted list. -/
theorem mergeCount_pairwise (l₁ l₂ : List α) (h₁ : l₁.Pairwise (· ≤ ·))
    (h₂ : l₂.Pairwise (· ≤ ·)) : (mergeCount (· ≤ ·) l₁ l₂).2.Pairwise (· ≤ ·) := by
  rw [mergeCount_snd_eq_merge]
  refine pairwise_decide_le_iff.1 (List.pairwise_merge (le := (· ≤ ·)) ?_ ?_ l₁ l₂ ?_ ?_)
  · intro a b c hab hbc
    simpa using le_trans (by simpa using hab) (by simpa using hbc)
  · intro a b
    simpa using le_total a b
  · exact pairwise_decide_le_iff.2 h₁
  · exact pairwise_decide_le_iff.2 h₂

/-- **Merge sort outputs a sorted list.** -/
theorem msortCount_sorted (l : List α) : (msortCount (· ≤ ·) l).2.Pairwise (· ≤ ·) := by
  induction l using msortCount.induct (le := ((· ≤ ·) : α → α → Bool)) with
  | case1 => simp [msortCount.eq_1]
  | case2 a => simp [msortCount.eq_2]
  | case3 a b rest l k hTake hDrop =>
    rw [msortCount.eq_3]
    simp only
    exact mergeCount_pairwise _ _ hTake hDrop

end LinearOrder

/-! ### The comparison bound -/

/-- **Merge sort uses at most `n * (⌈log₂ n⌉ + 1)` comparisons**, where `n` is the length
of the input: the two halves of length `⌈n/2⌉` and `⌊n/2⌋` are sorted recursively with
`⌈log₂ n⌉ - 1` levels below them, and merging costs at most `n` comparisons. -/
theorem msortCount_counts_le (le : α → α → Bool) (l : List α) :
    (msortCount le l).1 ≤ l.length * (Nat.clog 2 l.length + 1) := by
  induction l using msortCount.induct (le := le) with
  | case1 => simp [msortCount.eq_1]
  | case2 a => simp [msortCount.eq_2]
  | case3 a b rest l k hTake hDrop =>
    rw [msortCount.eq_3]
    show (msortCount le (l.take k)).1 + (msortCount le (l.drop k)).1 +
        (mergeCount le (msortCount le (l.take k)).2 (msortCount le (l.drop k)).2).1 ≤
      l.length * (Nat.clog 2 l.length + 1)
    have hk : k = (l.length + 1) / 2 := rfl
    have hn : 2 ≤ l.length := by simp [l]
    have htake : (l.take k).length = k := by
      rw [List.length_take, Nat.min_eq_left]; omega
    have hdrop : (l.drop k).length = l.length - k := List.length_drop ..
    have hsum : (l.take k).length + (l.drop k).length = l.length := by omega
    -- the halves have lengths `⌈n/2⌉` and `⌊n/2⌋`, so one level of the recursion is paid for
    have hclog : Nat.clog 2 (l.take k).length + 1 = Nat.clog 2 l.length := by
      have h := Nat.clog_of_two_le (b := 2) (by norm_num) (n := l.length) hn
      rw [h]
      have hk2 : k = (l.length + 2 - 1) / 2 := by rw [hk]; omega
      rw [htake, hk2]
    have hmono : Nat.clog 2 (l.drop k).length + 1 ≤ Nat.clog 2 l.length := by
      have hle : Nat.clog 2 (l.drop k).length ≤ Nat.clog 2 (l.take k).length := by
        refine Nat.clog_mono_right 2 ?_
        rw [hdrop, htake]; omega
      omega
    have hm := mergeCount_counts_le le (msortCount le (l.take k)).2 (msortCount le (l.drop k)).2
    rw [msortCount_length, msortCount_length, hsum] at hm
    have h₁ : (msortCount le (l.take k)).1 ≤ (l.take k).length * Nat.clog 2 l.length := by
      rw [← hclog]; exact hTake
    have h₂ : (msortCount le (l.drop k)).1 ≤ (l.drop k).length * Nat.clog 2 l.length :=
      le_trans hDrop (Nat.mul_le_mul_left _ hmono)
    calc (msortCount le (l.take k)).1 + (msortCount le (l.drop k)).1 +
            (mergeCount le (msortCount le (l.take k)).2 (msortCount le (l.drop k)).2).1
        ≤ (l.take k).length * Nat.clog 2 l.length + (l.drop k).length * Nat.clog 2 l.length +
            l.length := by omega
      _ = l.length * Nat.clog 2 l.length + l.length := by rw [← Nat.add_mul, hsum]
      _ = l.length * (Nat.clog 2 l.length + 1) := by rw [Nat.mul_add, Nat.mul_one]

/-- **The comparison sort `msortCount` costs `O(n log n)` comparisons.**  On a list of
length `n` it performs at most `2 * n * (⌈log₂ n⌉ + 1)` comparisons, an explicit bound of
order `n log n` matching the information-theoretic lower bound of `SortBounds.Comparison.Tree`. -/
theorem msortCount_le [LinearOrder α] (l : List α) :
    (msortCount (· ≤ ·) l).1 ≤ 2 * l.length * (Nat.clog 2 l.length + 1) := by
  refine (msortCount_counts_le _ l).trans ?_
  rw [Nat.mul_assoc]
  exact Nat.le_mul_of_pos_left _ (by norm_num)

end SortBounds
