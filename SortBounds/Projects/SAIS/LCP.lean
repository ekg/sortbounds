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
