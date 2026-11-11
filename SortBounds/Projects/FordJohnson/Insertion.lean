/-
SortBounds/Projects/FordJohnson/Insertion.lean

Milestone **M0** of the `FordJohnson` lane: binary insertion with an exact comparison
counter.

`insertCount x l` finds the position of `x` in the sorted list `l` by bisection on the
*values*: it compares `x` with the middle element of the current window and recurses
into the half that can contain the answer.  Insertion into a window of `k` elements
therefore costs `1 +` (cost of a window of `k/2` or `k - k/2 - 1` elements), which is
`⌈log₂ (k+1)⌉` in the worst case:

* `insertCount_perm`   — the result is a permutation of `x :: l`;
* `insertCount_sorted` — the result is sorted whenever `l` is;
* `insertCount_count`  — the number of comparisons is at most `Nat.clog 2 (l.length + 1)`.

The last proof is where the bisection content sits: splitting a window of `k` elements
around its middle element leaves windows of `k/2` and `k - k/2 - 1` elements, both of
which need one bit less of search than the whole window.
-/
import Mathlib

namespace SortBounds.Projects.FordJohnson

variable {α : Type*}

/-! ### Binary insertion, counted -/

set_option linter.unusedVariables false in
/-- `insertCount x l` inserts `x` into the sorted list `l` by binary search and returns the
number of comparisons spent together with the resulting list.  The window is split at its
middle element: compare `x` with `l[l.length / 2]`; if `x` is smaller the answer lies in
the first half, otherwise in the part after the middle element. -/
def insertCount [LinearOrder α] (x : α) (l : List α) : ℕ × List α :=
  match l with
  | [] => (0, [x])
  | y :: ys =>
    match h : (y :: ys).drop ((y :: ys).length / 2) with
    | [] => (0, x :: y :: ys)
    | a :: bs =>
      if x ≤ a then
        let r := insertCount x ((y :: ys).take ((y :: ys).length / 2))
        (r.1 + 1, r.2 ++ a :: bs)
      else
        let r := insertCount x bs
        (r.1 + 1, (y :: ys).take ((y :: ys).length / 2) ++ a :: r.2)
termination_by l.length
decreasing_by
  · simp_wf
    omega
  · simp_wf
    have hlen : bs.length + 1 = (y :: ys).length - (y :: ys).length / 2 := by
      have := List.length_drop (l := (y :: ys)) (i := (y :: ys).length / 2)
      rw [h] at this
      simpa using this
    simp only [List.length_cons] at hlen ⊢
    omega

/-- The middle index of a nonempty list is a valid position, so the `drop`-is-empty case of
`insertCount` is never reached. -/
theorem drop_half_ne_nil {l : List α} (h : l ≠ []) : l.drop (l.length / 2) ≠ [] := by
  intro hnil
  have hlen : (l.drop (l.length / 2)).length = 0 := by simp [hnil]
  rw [List.length_drop] at hlen
  have hpos : 0 < l.length := List.length_pos_of_ne_nil h
  omega

/-- If `l.drop m = a :: bs` then `bs` is the part of `l` strictly after position `m`. -/
theorem length_tail_drop {l : List α} {m : ℕ} {a : α} {bs : List α} (h : l.drop m = a :: bs) :
    bs.length = l.length - m - 1 := by
  have hlen := List.length_drop (l := l) (i := m)
  rw [h] at hlen
  simp at hlen
  omega

/-- The recursion step of `insertCount` at a nonempty list with nonempty right half. -/
theorem insertCount_drop_cons [LinearOrder α] (x y : α) (ys : List α) {a : α} {bs : List α}
    (h : (y :: ys).drop ((y :: ys).length / 2) = a :: bs) :
    insertCount x (y :: ys) =
      if x ≤ a then
        let r := insertCount x ((y :: ys).take ((y :: ys).length / 2))
        (r.1 + 1, r.2 ++ a :: bs)
      else
        let r := insertCount x bs
        (r.1 + 1, (y :: ys).take ((y :: ys).length / 2) ++ a :: r.2) := by
  rw [insertCount.eq_2, h]

/-! ### Insertion preserves permutations -/

theorem insertCount_perm [LinearOrder α] (x : α) (l : List α) :
    (insertCount x l).2.Perm (x :: l) := by
  induction l using insertCount.induct (x := x) with
  | case1 => rw [insertCount.eq_1]
  | case2 y ys hdrop => rw [insertCount.eq_2, hdrop]
  | case3 y ys a bs hdrop hle ih =>
    rw [insertCount_drop_cons x y ys hdrop, ite_eq_left hle]
    have hsplit : (y :: ys).take ((y :: ys).length / 2) ++ a :: bs = y :: ys := by
      rw [← hdrop, List.take_append_drop]
    refine (ih.append_right (a :: bs)).trans ?_
    rw [List.cons_append]
    exact List.Perm.of_eq (by rw [hsplit])
  | case4 y ys a bs hdrop hnle ih =>
    rw [insertCount_drop_cons x y ys hdrop, ite_eq_right hnle]
    have hsplit : (y :: ys).take ((y :: ys).length / 2) ++ a :: bs = y :: ys := by
      rw [← hdrop, List.take_append_drop]
    refine (List.Perm.append_left _ (ih.cons a)).trans ?_
    refine (List.Perm.append_left _ (List.Perm.swap' x a (List.Perm.refl bs))).trans ?_
    refine List.perm_middle.trans ?_
    exact List.Perm.of_eq (by rw [hsplit])

/-! ### Insertion preserves sortedness -/

theorem insertCount_sorted [LinearOrder α] (x : α) (l : List α) (h : l.Pairwise (· ≤ ·)) :
    (insertCount x l).2.Pairwise (· ≤ ·) := by
  revert h
  induction l using insertCount.induct (x := x) with
  | case1 =>
    intro _
    rw [insertCount.eq_1]
    simp
  | case2 y ys hdrop =>
    exact absurd hdrop (drop_half_ne_nil (l := y :: ys) (by simp))
  | case3 y ys a bs hdrop hle ih =>
    intro hp
    simp only [insertCount_drop_cons x y ys hdrop, ite_eq_left hle]
    have hsplit : (y :: ys).take ((y :: ys).length / 2) ++ a :: bs = y :: ys := by
      rw [← hdrop, List.take_append_drop]
    rw [← hsplit, List.pairwise_append] at hp
    obtain ⟨has, habs, hcross⟩ := hp
    have hcons := List.pairwise_cons.mp habs
    rw [List.pairwise_append]
    refine ⟨ih has, habs, ?_⟩
    intro u hu v hv
    have hmem : u ∈ x :: (y :: ys).take ((y :: ys).length / 2) :=
      (insertCount_perm x _).mem_iff.mp hu
    rcases List.mem_cons.mp hmem with rfl | hu'
    · rcases List.mem_cons.mp hv with rfl | hv'
      · exact hle
      · exact le_trans hle (hcons.1 v hv')
    · exact hcross u hu' v hv
  | case4 y ys a bs hdrop hnle ih =>
    intro hp
    simp only [insertCount_drop_cons x y ys hdrop, ite_eq_right hnle]
    have hsplit : (y :: ys).take ((y :: ys).length / 2) ++ a :: bs = y :: ys := by
      rw [← hdrop, List.take_append_drop]
    rw [← hsplit, List.pairwise_append] at hp
    obtain ⟨has, habs, hcross⟩ := hp
    have hcons := List.pairwise_cons.mp habs
    have halt : a < x := not_le.mp hnle
    have hmem : ∀ v ∈ (insertCount x bs).2, v = x ∨ v ∈ bs := by
      intro v hv
      rcases List.mem_cons.mp ((insertCount_perm x bs).mem_iff.mp hv) with h | h
      · exact Or.inl h
      · exact Or.inr h
    rw [List.pairwise_append]
    refine ⟨has, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨fun v hv => ?_, ih hcons.2⟩
      rcases hmem v hv with rfl | hv'
      · exact le_of_lt halt
      · exact hcons.1 v hv'
    · intro u hu v hv
      have hua : u ≤ a := hcross u hu a (by simp)
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact hua
      · rcases hmem v hv' with rfl | hv''
        · exact le_trans hua (le_of_lt halt)
        · exact hcross u hu v (List.mem_cons_of_mem a hv'')

/-! ### The comparison count of binary insertion -/

/-- `⌈log₂ (n+n)⌉ = ⌈log₂ n⌉ + 1` for `n ≥ 1`. -/
theorem clog_two_add (n : ℕ) (hn : 1 ≤ n) : Nat.clog 2 (n + n) = Nat.clog 2 n + 1 := by
  rw [Nat.clog_of_two_le (b := 2) (by norm_num) (by omega)]
  have h : (n + n + 2 - 1) / 2 = n := by omega
  rw [h]

/-- `⌈log₂ (n+n+1)⌉ = ⌈log₂ (n+1)⌉ + 1` for `n ≥ 1`. -/
theorem clog_two_add_one (n : ℕ) (hn : 1 ≤ n) :
    Nat.clog 2 (n + n + 1) = Nat.clog 2 (n + 1) + 1 := by
  rw [Nat.clog_of_two_le (b := 2) (by norm_num) (by omega)]
  have h : (n + n + 1 + 2 - 1) / 2 = n + 1 := by omega
  rw [h]

/-- The left half of a window of `k > 0` elements still leaves room for one comparison. -/
theorem clog_half_add_one (k : ℕ) (hk : 0 < k) :
    Nat.clog 2 (k / 2 + 1) + 1 ≤ Nat.clog 2 (k + 1) := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hj1 : 1 ≤ j := by omega
    have hk' : k / 2 = j := by omega
    rw [hk', hj, clog_two_add_one j hj1]
  · have hk' : k / 2 = j := by omega
    have hkj : k + 1 = (j + 1) + (j + 1) := by omega
    rw [hk', hkj, clog_two_add (j + 1) (by omega)]

/-- The right half of a window of `k > 0` elements still leaves room for one comparison. -/
theorem clog_split_add_one (k b : ℕ) (hk : 0 < k) (hb : b = k - k / 2 - 1) :
    Nat.clog 2 (b + 1) + 1 ≤ Nat.clog 2 (k + 1) := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hj1 : 1 ≤ j := by omega
    have hk' : k / 2 = j := by omega
    have hb' : b + 1 = j := by omega
    rw [hb', hj, clog_two_add_one j hj1]
    exact Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1
  · have hk' : k / 2 = j := by omega
    have hb' : b + 1 = j + 1 := by omega
    have hkj : k + 1 = (j + 1) + (j + 1) := by omega
    rw [hb', hkj, clog_two_add (j + 1) (by omega)]

/-- **Binary insertion into a window of `k` elements costs at most `⌈log₂ (k+1)⌉`
comparisons.** -/
theorem insertCount_count [LinearOrder α] (x : α) (l : List α) :
    (insertCount x l).1 ≤ Nat.clog 2 (l.length + 1) := by
  suffices H : ∀ k (l : List α), l.length = k → (insertCount x l).1 ≤ Nat.clog 2 (k + 1) from
    H l.length l rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro l hl
    match l with
    | [] =>
      rw [insertCount.eq_1]
      simp
    | y :: ys =>
      subst hl
      have hpos : 0 < (y :: ys).length := by simp
      have htake : ((y :: ys).take ((y :: ys).length / 2)).length = (y :: ys).length / 2 := by
        rw [List.length_take]
        omega
      have ih_take : (insertCount x ((y :: ys).take ((y :: ys).length / 2))).1 ≤
          Nat.clog 2 (((y :: ys).take ((y :: ys).length / 2)).length + 1) :=
        ih _ (by rw [htake]; omega) _ rfl
      rw [htake] at ih_take
      obtain ⟨a, bs, hdrop⟩ : ∃ a bs, (y :: ys).drop ((y :: ys).length / 2) = a :: bs := by
        cases hh : (y :: ys).drop ((y :: ys).length / 2) with
        | nil => exact absurd hh (drop_half_ne_nil (by simp))
        | cons a bs => exact ⟨a, bs, rfl⟩
      have hbs : bs.length = (y :: ys).length - (y :: ys).length / 2 - 1 :=
        length_tail_drop hdrop
      have ih_bs : (insertCount x bs).1 ≤ Nat.clog 2 (bs.length + 1) :=
        ih _ (by omega) bs rfl
      by_cases hle : x ≤ a
      · simp only [insertCount_drop_cons x y ys hdrop, ite_eq_left hle]
        have hstep := clog_half_add_one (y :: ys).length hpos
        omega
      · simp only [insertCount_drop_cons x y ys hdrop, ite_eq_right hle]
        have hstep := clog_split_add_one (y :: ys).length bs.length hpos hbs
        omega

end SortBounds.Projects.FordJohnson
