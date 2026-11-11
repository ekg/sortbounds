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
  inspects `n - max i j + 1` characters while the guided one inspects exactly
  `1` — and `naiveInspectSum` (summed over all pairs `i < j`) exceeds
  `guidedInspectSum` by a factor `(n + 4) / 3`.

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
      if a = b then ((cmpCounted as bs).1, (cmpCounted as bs).2 + 1)
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

/-- **The LCP-guided comparison inspects exactly one character**: given the true `lcp`,
`cmpFrom` looks at the deciding position only.  (Correctness of that comparison is
`cmpFrom_lcp_advance`; together they say a guided comparison costs `1`.) -/
theorem inspectCount_lcp (s : List α) (i j : ℕ) :
    inspectCount s (lcp (suffix s i) (suffix s j)) i j = 1 := by
  rw [inspectCount_eq, lcp_drop_lcp]

/-- **The `k` skipped characters cost nothing**: the guided comparison plus the `k`
characters it was allowed to skip are never dearer than the naive comparison. -/
theorem cmpFrom_inspectCount_le (s : List α) (k i j : ℕ)
    (h : (suffix s i).take k = (suffix s j).take k) :
    inspectCount s k i j + k ≤ inspectCount s 0 i j := by
  have hsplit := lcp_eq_length_take_add (a := suffix s i) (b := suffix s j) h
  have hlen : ((suffix s i).take k).length ≤ k := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  rw [inspectCount_eq (k := k), inspectCount_zero, hsplit]
  omega

/-- The saving is exact when `k` really is a prefix of both suffixes. -/
theorem inspectCount_eq_add (s : List α) (k i j : ℕ)
    (h : (suffix s i).take k = (suffix s j).take k) (hk : k ≤ (suffix s i).length) :
    inspectCount s 0 i j = k + inspectCount s k i j := by
  have hsplit := lcp_eq_length_take_add (a := suffix s i) (b := suffix s j) h
  have hlen : ((suffix s i).take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk]
  rw [inspectCount_eq (k := k), inspectCount_zero, hsplit, hlen]
  omega

end Skipping
