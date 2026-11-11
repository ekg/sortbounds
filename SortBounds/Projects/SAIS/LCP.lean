/-
SortBounds/Projects/SAIS/LCP.lean

The cost model behind "you only have to compare a few characters" (milestone `M0`).

Sorting the suffixes of a string is *not* the comparison problem of
`SortBounds/Comparison`: a comparison of two suffixes is not an atomic probe, it
inspects characters until the two suffixes differ or one of them ends.  What
makes suffix sorting linear-time in practice is a supply of **lower bounds** on
the longest common prefix (LCP): if the algorithm already knows that suffixes
`i` and `j` agree on their first `k` characters, the comparison may start at
position `k` and never looks at those `k` characters again.

This file makes that precise without touching any suffix-sorting algorithm.

* `suffix s i` — the suffix of `s` starting at position `i` (`s.drop i`);
* `lcp a b` — the length of the longest common prefix of two lists;
* `cmpCounted a b` — a character-by-character comparison of two lists, returning
  both the `Ordering` and the number of characters inspected;
* `cmpCost k a b` / `inspectCount s k i j` — the cost model: comparing `a` with `b`
  while being allowed to skip a known common prefix of length `k` costs
  `1 + lcp (a.drop k) (b.drop k)`, i.e. `1` if `k` is the true LCP;
* `suffix_compare_eq_of_lcp` — skipping a *genuinely* common prefix does not
  change the answer: `cmpFrom s k i j = compare (suffix s i) (suffix s j)`;
* `cmpFrom_lcp_advance` — in particular advancing `k` to the true LCP keeps the
  comparison correct;
* `cmpFrom_inspectCount_le` — the `k` skipped characters cost nothing:
  the guided comparison plus its `k` skipped characters is never dearer than the
  naive one;
* the concrete contrast on `s = List.replicate n a` (all characters equal): every
  pair of distinct suffixes has `lcp (n - max i j)`, so the naive comparison
  inspects `n - max i j + 1` positions while the guided one inspects exactly
  `1` — and `naiveInspectSum` (summed over all pairs `i < j`) exceeds
  `guidedInspectSum` by a factor `(n + 4) / 3`.

Two conventions of the model, stated so that they cannot be read into the theorems:
the supplied `k` is **free** (maintaining LCP lower bounds is a separate cost, borne by
the LCP-array construction, not by the comparison), and one inspection is charged per
*position* compared rather than per character of each suffix.

The statement is *not* that LCP-guided suffix sorting is `O(n log n)`: that needs
a suffix-sorting algorithm plus the LCP array construction, neither of which is
attempted here (correctness of SA-IS is in the Isabelle AFP).  What is proved is
the local accounting principle on which any such bound rests.
-/
import Mathlib

namespace SortBounds.Projects.SAIS

variable {α : Type*}

/-! ### Suffixes -/

/-- The suffix of `s` starting at position `i`.  The index is a plain `ℕ`, so the
definition is total: `suffix s i = []` once `i ≥ s.length`, exactly as `List.drop`.
(`Lane README` indexes suffixes by `Fin s.length`; this is the total version, and every
statement about `Fin`-indexed suffixes is the special case `i < s.length`.) -/
def suffix (s : List α) (i : ℕ) : List α := s.drop i

@[simp] theorem suffix_zero (s : List α) : suffix s 0 = s := by simp [suffix]

@[simp] theorem suffix_def (s : List α) (i : ℕ) : suffix s i = s.drop i := rfl

@[simp] theorem suffix_length (s : List α) (i : ℕ) : (suffix s i).length = s.length - i :=
  List.length_drop

theorem suffix_eq_replicate {a : α} {n i : ℕ} :
    suffix (List.replicate n a) i = List.replicate (n - i) a :=
  List.drop_replicate

theorem drop_succ_eq_tail_drop (l : List α) (k : ℕ) :
    l.drop (k + 1) = (l.drop k).tail := by
  induction l generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ m =>
      simp only [List.drop_succ_cons]
      exact ih m

/-! ### The longest common prefix -/

section Lcp
variable [DecidableEq α]

/-- Length of the longest common prefix of two lists.  Each position is inspected at
most once: the recursion stops at the first mismatch, and at the end of the shorter
list. -/
def lcp : List α → List α → ℕ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => if a = b then lcp as bs + 1 else 0

theorem lcp_cons_cons (a b : α) (as bs : List α) :
    lcp (a :: as) (b :: bs) = if a = b then lcp as bs + 1 else 0 := rfl

@[simp] theorem lcp_nil_left (b : List α) : lcp [] b = 0 := by cases b <;> rfl

@[simp] theorem lcp_nil_right (a : List α) : lcp a [] = 0 := by cases a <;> rfl

theorem lcp_comm (a b : List α) : lcp a b = lcp b a := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      by_cases h : x = y
      · simp [lcp_cons_cons, h, ih]
      · have h' : ¬ y = x := fun hh => h hh.symm
        simp [lcp_cons_cons, h, h']

theorem lcp_le_left (a b : List α) : lcp a b ≤ a.length := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      by_cases h : x = y
      · have := ih ys
        rw [lcp_cons_cons, ite_eq_left h]
        simp only [List.length_cons]; omega
      · rw [lcp_cons_cons, ite_eq_right h]; simp

theorem lcp_le_right (a b : List α) : lcp a b ≤ b.length := by
  rw [lcp_comm]; exact lcp_le_left b a

/-- The two lists agree on their first `lcp a b` characters. -/
theorem take_lcp (a b : List α) : a.take (lcp a b) = b.take (lcp a b) := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      by_cases h : x = y
      · rw [lcp_cons_cons, ite_eq_left h, List.take_succ_cons, List.take_succ_cons, h, ih]
      · rw [lcp_cons_cons, ite_eq_right h]
        simp

/-- Conversely, `lcp` is *maximal*: any common prefix has length at most `lcp a b`
(provided it really is a prefix of both lists, i.e. `k ≤ min a.length b.length`). -/
theorem le_lcp_of_take_eq {a b : List α} {k : ℕ} (hk : k ≤ min a.length b.length)
    (h : a.take k = b.take k) : k ≤ lcp a b := by
  induction a generalizing b k with
  | nil =>
    have hk0 : k ≤ 0 := by simpa using hk
    omega
  | cons x xs ih =>
    cases b with
    | nil =>
      have hk0 : k ≤ 0 := by simpa using hk
      omega
    | cons y ys =>
      match k, hk, h with
      | 0, _, _ => omega
      | k' + 1, hk, h =>
        have hh : x :: xs.take k' = y :: ys.take k' := by
          simpa only [lcp_cons_cons, List.take_succ_cons] using h
        simp only [List.cons.injEq] at hh
        obtain ⟨hxy, hrest⟩ := hh
        have hk' : k' ≤ min xs.length ys.length := by
          simp only [List.length_cons] at hk; omega
        have hrec : k' ≤ lcp xs ys := ih hk' hrest
        rw [lcp_cons_cons, ite_eq_left hxy]
        omega

/-- Two lists agree on their first `k` characters iff `k` is at most their `lcp`, or the
two lists are equal (in which case any `k` works: the longer `take` of `a = b` is a
truncation of the other copy). -/
theorem take_eq_take_iff {a b : List α} {k : ℕ} :
    a.take k = b.take k ↔ k ≤ lcp a b ∨ a = b := by
  constructor
  · intro h
    rcases le_or_gt k (min a.length b.length) with hk | hk
    · exact Or.inl (le_lcp_of_take_eq hk h)
    · -- `k` exceeds the shorter length; equality of the takes then forces `a = b`
      right
      rcases le_or_gt a.length b.length with hab | hab
      · have ha : a.take k = a := List.take_eq_self_iff a |>.mpr (by omega)
        have hlen : a.length = min k b.length := by
          have h2 : (a.take k).length = (b.take k).length := by rw [h]
          rw [ha, List.length_take] at h2
          exact h2
        have hbk : b.length ≤ k := by
          rcases le_or_gt k b.length with h1 | h1
          · rw [Nat.min_eq_left h1] at hlen
            omega
          · exact le_of_lt h1
        rw [ha] at h
        rwa [List.take_eq_self_iff b |>.mpr hbk] at h
      · have hb : b.take k = b := List.take_eq_self_iff b |>.mpr (by omega)
        have hlen : b.length = min k a.length := by
          have h2 : (b.take k).length = (a.take k).length := by rw [h]
          rw [hb, List.length_take] at h2
          exact h2
        have hak : a.length ≤ k := by
          rcases le_or_gt k a.length with h1 | h1
          · rw [Nat.min_eq_left h1] at hlen
            omega
          · exact le_of_lt h1
        rw [hb] at h
        rw [List.take_eq_self_iff a |>.mpr hak] at h
        exact h
  · rintro (hk | rfl)
    · have h1 : (a.take (lcp a b)).take k = a.take k := by
        rw [List.take_take, Nat.min_eq_left hk]
      have h2 : (b.take (lcp a b)).take k = b.take k := by
        rw [List.take_take, Nat.min_eq_left hk]
      rw [← h1, ← h2, take_lcp]
    · rfl

/-- The `lcp` is the whole of the shorter list exactly when the two lists agree on it —
equivalently, when one of them is a prefix of the other. -/
theorem take_min_length (a b : List α) :
    a.take (min a.length b.length) = b.take (min a.length b.length) ↔
      lcp a b = min a.length b.length := by
  constructor
  · intro h
    have hle : min a.length b.length ≤ lcp a b := le_lcp_of_take_eq le_rfl h
    have hge : lcp a b ≤ min a.length b.length := le_min (lcp_le_left a b) (lcp_le_right a b)
    omega
  · intro h
    have := take_lcp a b
    rwa [h] at this

/-- Dropping the first character of both lists shortens the `lcp` by at most one. -/
theorem lcp_tail_tail (a b : List α) : lcp a b ≤ lcp a.tail b.tail + 1 := by
  cases a with
  | nil => simp
  | cons x xs =>
    cases b with
    | nil => simp
    | cons y ys =>
      by_cases h : x = y
      · rw [lcp_cons_cons, ite_eq_left h]; simp
      · rw [lcp_cons_cons, ite_eq_right h]; simp

/-- Prefixing both lists by the same list shifts the `lcp` by its length. -/
theorem lcp_append_left (p x y : List α) :
    lcp (p ++ x) (p ++ y) = p.length + lcp x y := by
  induction p with
  | nil => simp
  | cons c cs ih =>
    rw [List.cons_append, List.cons_append, lcp_cons_cons, ite_eq_left rfl, ih,
      List.length_cons, Nat.add_right_comm]

/-- The `lcp` of suffixes `i` and `j` of `s` is the `lcp` of the two drops. -/
theorem suffix_lcp_def (s : List α) (i j : ℕ) :
    lcp (suffix s i) (suffix s j) = lcp (s.drop i) (s.drop j) := rfl

end Lcp

/-! ### The cost model: a comparison that counts the characters it inspects -/

section Cost
variable [LinearOrder α]

/-- Compare two lists character by character, returning both the `Ordering` and the
number of characters inspected.  One inspection per position examined — positions that
agree are examined, the deciding position too — and a comparison of two empty lists
still counts `1` (an implementation cannot know it has nothing to compare for free). -/
def cmpCounted : List α → List α → Ordering × ℕ
  | [], [] => (Ordering.eq, 1)
  | [], _ :: _ => (Ordering.lt, 1)
  | _ :: _, [] => (Ordering.gt, 1)
  | a :: as, b :: bs =>
      if a = b then
        let r := cmpCounted as bs
        (r.1, r.2 + 1)
      else (compare a b, 1)

theorem cmpCounted_nil_nil : cmpCounted ([] : List α) [] = (Ordering.eq, 1) := rfl

theorem cmpCounted_nil_cons (b : α) (bs : List α) :
    cmpCounted [] (b :: bs) = (Ordering.lt, 1) := rfl

theorem cmpCounted_cons_nil (a : α) (as : List α) :
    cmpCounted (a :: as) [] = (Ordering.gt, 1) := rfl

theorem cmpCounted_cons_cons (a b : α) (as bs : List α) :
    cmpCounted (a :: as) (b :: bs) =
      if a = b then ((cmpCounted as bs).1, (cmpCounted as bs).2 + 1)
      else (compare a b, 1) := rfl

/-- The instrumented comparison computes the same answer as `compare`. -/
theorem cmpCounted_fst (a b : List α) : (cmpCounted a b).1 = compare a b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      by_cases h : x = y
      · rw [cmpCounted_cons_cons, ite_eq_left h, ih, List.compare_cons_cons]
        rw [show compare x y = Ordering.eq from by simp [h], Ordering.eq_then]
      · have hne : compare x y ≠ Ordering.eq := fun hc => h (compare_eq_iff_eq.mp hc)
        rw [cmpCounted_cons_cons, ite_eq_right h, List.compare_cons_cons]
        cases hc : compare x y with
        | lt => rfl
        | gt => rfl
        | eq => exact absurd hc hne

/-- The number of characters inspected is the `lcp` plus the one comparison that
decides the outcome. -/
theorem cmpCounted_snd (a b : List α) : (cmpCounted a b).2 = lcp a b + 1 := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      by_cases h : x = y
      · rw [cmpCounted_cons_cons, ite_eq_left h, lcp_cons_cons, ite_eq_left h, ih]
      · rw [cmpCounted_cons_cons, ite_eq_right h, lcp_cons_cons, ite_eq_right h]

end Cost

/-! ### Skipping a known common prefix -/

section Skipping
variable [LinearOrder α]

/-- Cost model: comparing `a` with `b` while being allowed to skip a common prefix of
length `k` costs one inspection per position examined past the prefix, plus the
comparing inspection that decides the outcome. -/
def cmpCost (k : ℕ) (a b : List α) : ℕ := (cmpCounted (a.drop k) (b.drop k)).2

/-- Compare suffix `i` with suffix `j` of `s`, given that their first `k` characters
agree: the comparison starts at position `k`. -/
def cmpFrom (s : List α) (k i j : ℕ) : Ordering :=
  (cmpCounted ((suffix s i).drop k) ((suffix s j).drop k)).1

/-- The characters inspected by `cmpFrom s k i j`, i.e. `cmpCost` at the two suffixes. -/
def inspectCount (s : List α) (k i j : ℕ) : ℕ :=
  cmpCost k (suffix s i) (suffix s j)

/-- Comparing with a known prefix costs `1 + (the `lcp` past that prefix)`. -/
theorem cmpCost_eq (k : ℕ) (a b : List α) :
    cmpCost k a b = 1 + lcp (a.drop k) (b.drop k) := by
  rw [cmpCost, cmpCounted_snd, Nat.add_comm]

theorem inspectCount_eq (s : List α) (k i j : ℕ) :
    inspectCount s k i j = 1 + lcp ((suffix s i).drop k) ((suffix s j).drop k) := by
  rw [inspectCount, cmpCost_eq, Nat.add_comm]

/-- Comparing the suffixes with no prefix supplied is the plain character-by-character
comparison. -/
@[simp] theorem inspectCount_zero (s : List α) (i j : ℕ) :
    inspectCount s 0 i j = 1 + lcp (suffix s i) (suffix s j) := by
  rw [inspectCount_eq]
  simp

/-! #### Skipping a common prefix does not change the answer -/

/-- Prefixing both sides by the same list does not change the comparison. -/
theorem compare_append_append_left (p x y : List α) :
    compare (p ++ x) (p ++ y) = compare x y := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    rw [List.cons_append, List.cons_append, List.compare_cons_cons,
      show compare c c = Ordering.eq from by simp, Ordering.eq_then]
    exact ih

/-- If the first `k` characters of `a` and `b` agree, then comparing the remainders is
the same as comparing `a` with `b`. -/
theorem compare_drop_drop_of_take_eq {a b : List α} {k : ℕ} (h : a.take k = b.take k) :
    compare (a.drop k) (b.drop k) = compare a b := by
  have ha : a = a.take k ++ a.drop k := (List.take_append_drop k a).symm
  have hb : b = a.take k ++ b.drop k := by rw [h, List.take_append_drop]
  conv_rhs => rw [ha, hb]
  rw [compare_append_append_left]

/-- **Soundness of the cost model**: if suffixes `i` and `j` agree on their first `k`
characters, then skipping them costs nothing in correctness — `cmpFrom s k i j` is the
true comparison of the two suffixes. -/
theorem suffix_compare_eq_of_lcp (s : List α) (k i j : ℕ)
    (h : (suffix s i).take k = (suffix s j).take k) :
    cmpFrom s k i j = compare (suffix s i) (suffix s j) := by
  rw [cmpFrom, cmpCounted_fst]
  exact compare_drop_drop_of_take_eq h

/-- A prefix shorter than the `lcp` is a common prefix. -/
theorem take_eq_of_le_lcp {a b : List α} {k : ℕ} (hk : k ≤ lcp a b) : a.take k = b.take k :=
  take_eq_take_iff.mpr (Or.inl hk)

theorem cmpFrom_eq_compare_of_le_lcp (s : List α) (k i j : ℕ)
    (hk : k ≤ lcp (suffix s i) (suffix s j)) :
    cmpFrom s k i j = compare (suffix s i) (suffix s j) :=
  suffix_compare_eq_of_lcp s k i j (take_eq_of_le_lcp hk)

/-- **Advancing `k` to the true LCP keeps the comparison correct.** -/
theorem cmpFrom_lcp_advance (s : List α) (i j : ℕ) :
    cmpFrom s (lcp (suffix s i) (suffix s j)) i j =
      compare (suffix s i) (suffix s j) :=
  cmpFrom_eq_compare_of_le_lcp s _ i j le_rfl

/-! #### The skipped characters cost nothing -/

/-- Splitting the `lcp` at a common prefix of length `k`. -/
theorem lcp_eq_length_take_add {a b : List α} {k : ℕ} (h : a.take k = b.take k) :
    lcp a b = (a.take k).length + lcp (a.drop k) (b.drop k) := by
  have ha : a = a.take k ++ a.drop k := (List.take_append_drop k a).symm
  have hb : b = a.take k ++ b.drop k := by rw [h, List.take_append_drop]
  conv_lhs => rw [ha, hb]
  rw [lcp_append_left]

/-- Nothing is left to compare once the true `lcp` has been skipped. -/
theorem lcp_drop_lcp (a b : List α) : lcp (a.drop (lcp a b)) (b.drop (lcp a b)) = 0 := by
  have hsplit := lcp_eq_length_take_add (a := a) (b := b) (take_eq_of_le_lcp (le_refl (lcp a b)))
  have hlen : (a.take (lcp a b)).length = lcp a b := by
    rw [List.length_take, Nat.min_eq_left (lcp_le_left a b)]
  rw [hlen] at hsplit
  omega

/-- **The LCP-guided comparison inspects exactly one position**: given the true `lcp`,
`cmpFrom` looks at the deciding position only.  (Correctness of that comparison is
`cmpFrom_lcp_advance`; together they say a guided comparison costs `1`.) -/
theorem inspectCount_lcp (s : List α) (i j : ℕ) :
    inspectCount s (lcp (suffix s i) (suffix s j)) i j = 1 := by
  rw [inspectCount_eq, lcp_drop_lcp]

/-- **Skipping one more character saves at most one inspection**: the model never
credits a comparison with more than it skipped.  (The contrast on `aⁿ` is the case where
each skipped character saves exactly one inspection.) -/
theorem inspectCount_succ_le (s : List α) (k i j : ℕ) :
    inspectCount s k i j ≤ inspectCount s (k + 1) i j + 1 := by
  rw [inspectCount_eq (k := k), inspectCount_eq (k := k + 1),
    drop_succ_eq_tail_drop (suffix s i) k, drop_succ_eq_tail_drop (suffix s j) k]
  have := lcp_tail_tail ((suffix s i).drop k) ((suffix s j).drop k)
  omega

/-- The saving is exact: when the first `k` characters of suffixes `i` and `j` agree
(and `k` really is a prefix of suffix `i`), then the naive comparison spends exactly
those `k` extra inspections. -/
theorem inspectCount_eq_add (s : List α) (k i j : ℕ)
    (h : (suffix s i).take k = (suffix s j).take k) (hk : k ≤ (suffix s i).length) :
    inspectCount s 0 i j = k + inspectCount s k i j := by
  have hsplit := lcp_eq_length_take_add (a := suffix s i) (b := suffix s j) h
  have hlen : ((suffix s i).take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk]
  rw [inspectCount_eq (k := k), inspectCount_zero, hsplit, hlen]
  omega

/-- **The `k` skipped characters cost nothing**: the guided comparison plus the `k`
characters it was allowed to skip are never dearer than the naive comparison. -/
theorem cmpFrom_inspectCount_le (s : List α) (k i j : ℕ)
    (h : (suffix s i).take k = (suffix s j).take k) (hk : k ≤ (suffix s i).length) :
    inspectCount s k i j + k ≤ inspectCount s 0 i j := by
  rw [inspectCount_eq_add s k i j h hk]
  exact Nat.add_comm _ _ |>.le

end Skipping

/-! ### The arithmetic of the two totals -/

/-- Recurrence for `∑ j < n, j * (n + 1 - j)`, obtained by splitting off `j = n`. -/
theorem sum_range_mul_succ (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), j * (n + 2 - j)) =
      (∑ j ∈ Finset.range n, j * (n + 1 - j)) + (∑ j ∈ Finset.range n, j) + 2 * n := by
  rw [Finset.sum_range_succ]
  have hterm : ∀ j ∈ Finset.range n, j * (n + 2 - j) = j * (n + 1 - j) + j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show n + 2 - j = (n + 1 - j) + 1 by omega, Nat.mul_add, Nat.mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    show n * (n + 2 - n) = 2 * n by
      rw [show n + 2 - n = 2 by omega]; omega]

theorem sum_range_id_succ (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), j) = (∑ j ∈ Finset.range n, j) + n :=
  Finset.sum_range_succ _ _

/-- Gauss's formula, stated over `ℤ` so that no truncated subtraction appears. -/
theorem sum_range_id_twice_cast (n : ℕ) :
    2 * ((∑ j ∈ Finset.range n, j : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_id_succ, Nat.cast_add]
    have hn : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hn]
    nlinarith [ih]

/-- `∑ j < n, j * (n + 1 - j)` in closed form, over `ℤ`. -/
theorem sum_range_mul_cast (n : ℕ) :
    6 * ((∑ j ∈ Finset.range n, j * (n + 1 - j) : ℕ) : ℤ) =
      (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) + 4) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_mul_succ, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hn : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hn]
    have hg := sum_range_id_twice_cast n
    nlinarith [ih, hg]

/-! ### The concrete contrast: a string of one repeated character

On `s = List.replicate n a` every character is the same, so two suffixes can only be
told apart by their lengths: the `lcp` of suffixes `i` and `j` is `n - max i j`, the
whole of the shorter one.  The naive comparison therefore inspects `n - max i j + 1`
characters — `Θ(n)` — while the same comparison supplied with the true `lcp` inspects
exactly `1`.

Summed over all pairs `i < j` of suffixes the difference is a whole factor:
`6 · naiveInspectSum = n (n-1) (n+4)` (cubic in `n`) while
`2 · guidedInspectSum = n (n-1)` (quadratic): the naive total is exactly `(n + 4) / 3`
times the guided one.  Both totals sum over the same `n (n-1) / 2` pairs, so the
per-comparison factor `Θ(n)` shows up as a factor `Θ(n)` in the totals.
-/

section Replicate
variable [LinearOrder α]

theorem lcp_replicate (a : α) (p q : ℕ) :
    lcp (List.replicate p a) (List.replicate q a) = min p q := by
  induction p generalizing q with
  | zero => simp
  | succ p ih =>
    cases q with
    | zero => simp
    | succ q =>
      rw [List.replicate_succ, List.replicate_succ, lcp_cons_cons, ite_eq_left rfl, ih,
        Nat.succ_min_succ]

/-- Every pair of suffixes of `aⁿ` shares a prefix of length `n - max i j`. -/
theorem lcp_suffix_replicate (a : α) (n i j : ℕ) :
    lcp (suffix (List.replicate n a) i) (suffix (List.replicate n a) j) = n - max i j := by
  rw [suffix_eq_replicate, suffix_eq_replicate, lcp_replicate, Nat.sub_min_sub_left]

/-- The naive comparison inspects `n - max i j + 1` positions. -/
theorem inspectCount_replicate (a : α) (n i j : ℕ) :
    inspectCount (List.replicate n a) 0 i j = n - max i j + 1 := by
  rw [inspectCount_zero, lcp_suffix_replicate, Nat.add_comm]

/-- The guided comparison — supplied with the true `lcp` — inspects one position. -/
theorem inspectCount_replicate_lcp (a : α) (n i j : ℕ) :
    inspectCount (List.replicate n a) (n - max i j) i j = 1 := by
  rw [← lcp_suffix_replicate a n i j]
  exact inspectCount_lcp _ _ _

/-- The guided comparison is still correct, so its single inspection is enough. -/
theorem cmpFrom_replicate_lcp (a : α) (n i j : ℕ) :
    cmpFrom (List.replicate n a) (n - max i j) i j =
      compare (suffix (List.replicate n a) i) (suffix (List.replicate n a) j) := by
  rw [← lcp_suffix_replicate a n i j]
  exact cmpFrom_lcp_advance _ _ _

/-- The sharpest single instance: comparing the whole string `aⁿ` with its suffix at `1`
costs `n` inspections naively and `1` with the `lcp` supplied. -/
theorem replicate_pair_cost (a : α) (n : ℕ) (hn : 1 ≤ n) :
    inspectCount (List.replicate n a) 0 0 1 = n ∧
      inspectCount (List.replicate n a) (n - 1) 0 1 = 1 := by
  have hmax : max 0 1 = 1 := by norm_num
  constructor
  · rw [inspectCount_replicate, hmax]; omega
  · rw [show n - 1 = n - max 0 1 by rw [hmax]]
    exact inspectCount_replicate_lcp a n 0 1

/-- Inspections spent by the naive comparison, summed over all pairs `i < j` of suffixes
of `aⁿ`. -/
def naiveInspectSum (a : α) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, inspectCount (List.replicate n a) 0 i j

/-- Inspections spent by the `lcp`-guided comparison — each comparison of suffixes
`i < j` is supplied with `n - j`, their true `lcp` — summed over all pairs `i < j`. -/
def guidedInspectSum (a : α) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, inspectCount (List.replicate n a) (n - j) i j

theorem naiveInspectSum_eq (a : α) (n : ℕ) :
    naiveInspectSum a n = ∑ j ∈ Finset.range n, j * (n + 1 - j) := by
  unfold naiveInspectSum
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have hinner : ∀ i ∈ Finset.range j, inspectCount (List.replicate n a) 0 i j = n - j + 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [inspectCount_replicate, Nat.max_eq_right (by omega)]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_id]
  congr 1
  omega

theorem guidedInspectSum_eq (a : α) (n : ℕ) :
    guidedInspectSum a n = ∑ j ∈ Finset.range n, j := by
  unfold guidedInspectSum
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have hinner : ∀ i ∈ Finset.range j, inspectCount (List.replicate n a) (n - j) i j = 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show n - j = n - max i j by rw [Nat.max_eq_right (by omega)]]
    exact inspectCount_replicate_lcp a n i j
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, Nat.cast_id]

/-- **The naive total is cubic**: `6 · naiveInspectSum = n (n-1) (n+4)`. -/
theorem naiveInspectSum_closed (a : α) (n : ℕ) :
    6 * naiveInspectSum a n = n * (n - 1) * (n + 4) := by
  rw [naiveInspectSum_eq]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp
  · have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Nat.cast_sub (show 1 ≤ n by omega)
    refine Nat.cast_injective (R := ℤ) ?_
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, hcast, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_ofNat]
    exact sum_range_mul_cast n

/-- **The guided total is quadratic**: `2 · guidedInspectSum = n (n-1)`. -/
theorem guidedInspectSum_closed (a : α) (n : ℕ) :
    2 * guidedInspectSum a n = n * (n - 1) := by
  rw [guidedInspectSum_eq, mul_comm]
  exact Finset.sum_range_id_mul_two n

/-- **The cubic-vs-quadratic total contrast, exactly**: on a string of `n` equal characters,
comparing every pair of distinct suffixes with the naive comparison inspects exactly
`(n + 4) / 3` times as many characters as the `lcp`-guided comparison. -/
theorem three_mul_naiveInspectSum (a : α) (n : ℕ) :
    3 * naiveInspectSum a n = (n + 4) * guidedInspectSum a n := by
  have h1 := naiveInspectSum_closed a n
  have h2 := guidedInspectSum_closed a n
  have key : 2 * (3 * naiveInspectSum a n) = 2 * ((n + 4) * guidedInspectSum a n) := by
    have h1' : 2 * (3 * naiveInspectSum a n) = n * (n - 1) * (n + 4) := by
      rw [← h1]; ring
    have h2' : 2 * ((n + 4) * guidedInspectSum a n) = n * (n - 1) * (n + 4) := by
      rw [← h2]; ring
    rw [h1', h2']
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) key

/-- Consequently the naive total is at least `n / 3` times the guided total. -/
theorem guidedInspectSum_mul_le (a : α) (n : ℕ) :
    n * guidedInspectSum a n ≤ 3 * naiveInspectSum a n := by
  rw [three_mul_naiveInspectSum]
  exact Nat.mul_le_mul_right _ (by omega)

/-! ### Sanity checks

The theorems above are not vacuous: below are concrete instances, evaluated by the
kernel's own reduction (`decide`). -/

/-- A case where suffixes `0` and `2` of `"aba"` differ but agree on their first
character: the guided comparison (`k = 1`) is the true comparison. -/
example : cmpFrom ['a', 'b', 'a'] 1 0 2
    = compare (suffix ['a', 'b', 'a'] 0) (suffix ['a', 'b', 'a'] 2) := by decide

/-- The naive total on `a⁴` is `16` inspections; the guided total is `6`. -/
example : naiveInspectSum 'a' 4 = 16 := by decide
example : guidedInspectSum 'a' 4 = 6 := by decide

end Replicate

end SortBounds.Projects.SAIS
