/-
SortBounds/Projects/SAIS/Chain.lean

**The min property of the LCP array** (milestone `M1a`), in the form in which it is true.

The lane README states it over the *text* interval `[i, j)`:
`lcp (suffix s i) (suffix s j) = (Ico i j).inf' (lcpAt s)`.  `Array.lean` shows that this
is false (`inf'_lcpAt_ne_lcp`: on `"aba"` the text interval `[0, 2)` has minimum `0`, but
suffixes `0` and `2` share one character).  The LCP array's minima are about
*lexicographically* neighbouring suffixes — about a suffix array — and what makes the min
property work is exactly the classical fact that `lcp` is a minimum along a sorted chain:

* `lcp_eq_min_lcp_of_compare_lt` — **the three-list lemma**: for `a < b < c` in
  lexicographic order, `lcp a c = min (lcp a b) (lcp b c)`;
* `compare_lt_of_chain` — strict increase of neighbours makes every pair in the interval
  strictly increasing;
* `lcp_eq_inf'_of_chain` — **the min property**: for a chain `f` that is strictly
  increasing on `[i, j)`, `lcp (f i) (f j) = (Ico i j).inf' fun k => lcp (f k) (f (k+1))`;
* `lcp_suffix_eq_inf'_of_increasing` — the same for the suffixes of a string enumerated by a
  candidate suffix array `π` (so `f k = suffix s (π k)`), and
  `inspectCount_inf'_of_increasing` — **hence an LCP-guided comparison inspects exactly one
  position** (M1b): the LCP array's interval minimum *is* the true LCP, so
  `inspectCount s inf (π i) (π j) = 1`, and by `cmpFrom_lcp_advance` the comparison is also
  correct.

The `i = j` case of the M1a statement has no content and no `inf'`: `Ico i i = ∅` is not
nonempty, and `lcp (suffix s i) (suffix s i) = (suffix s i).length`, which the interval
minimum cannot express.  Every statement below therefore carries `i < j`, which is also
exactly what the README's nonemptiness argument `⟨i, ?_⟩` requires.
-/
import SortBounds.Projects.SAIS.Array

namespace SortBounds.Projects.SAIS

variable {α : Type*} [LinearOrder α]

/-! ### `lcp` along a lexicographically sorted chain -/

/-- **The three-list lemma.**  If `a`, `b`, `c` are strictly increasing in lexicographic
order then the LCP of `a` and `c` is the smaller of the two neighbouring LCPs.  (This is
where the min property comes from: the common prefix of the extremes is cut down by
whichever neighbour pair separates first.) -/
theorem lcp_eq_min_lcp_of_compare_lt {a b c : List α}
    (hab : compare a b = Ordering.lt) (hbc : compare b c = Ordering.lt) :
    lcp a c = min (lcp a b) (lcp b c) := by
  induction a generalizing b c with
  | nil => simp
  | cons x as ih =>
    cases b with
    | nil => simp at hab
    | cons y ys =>
      cases c with
      | nil => simp at hbc
      | cons z cs =>
        rw [List.compare_cons_cons, Ordering.then_eq_lt] at hab hbc
        rcases hab with hxy_lt | ⟨hxy_eq, hxs_lt⟩
        · -- `x < y`
          have hxylt : x < y := compare_lt_iff_lt.mp hxy_lt
          have hxy : x ≠ y := ne_of_lt hxylt
          have hxz : x ≠ z := by
            rcases hbc with hyz_lt | ⟨hyz_eq, -⟩
            · exact ne_of_lt (lt_trans hxylt (compare_lt_iff_lt.mp hyz_lt))
            · rw [compare_eq_iff_eq.mp hyz_eq] at hxylt
              exact ne_of_lt hxylt
          simp [lcp_cons_cons, hxy, hxz]
        · -- `x = y`
          have hxy : x = y := compare_eq_iff_eq.mp hxy_eq
          rcases hbc with hyz_lt | ⟨hyz_eq, hys_lt⟩
          · -- `y < z`
            have hyz : y ≠ z := ne_of_lt (compare_lt_iff_lt.mp hyz_lt)
            have hxz : x ≠ z := by rw [hxy]; exact hyz
            simp [lcp_cons_cons, hxy, hxz, hyz]
          · -- `y = z`, so reduce to the tails
            have hyz : y = z := compare_eq_iff_eq.mp hyz_eq
            have hxz : x = z := hxy.trans hyz
            rw [lcp_cons_cons, lcp_cons_cons, lcp_cons_cons, ite_eq_left hxy, ite_eq_left hxz,
              ite_eq_left hyz, ih hxs_lt hys_lt, ← Nat.succ_min_succ]

/-- Strict increase of neighbours gives strict increase of every pair in the interval. -/
theorem compare_lt_of_chain {f : ℕ → List α} {i n : ℕ} (hin : i < n)
    (h : ∀ k ∈ Finset.Ico i n, compare (f k) (f (k + 1)) = Ordering.lt) :
    compare (f i) (f n) = Ordering.lt := by
  revert hin h
  refine Nat.le_induction ?_ ?_ n (by omega : i + 1 ≤ n)
  · -- `n = i + 1`
    intro _ h
    exact h i (Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_self i⟩)
  · -- `n → n + 1`
    intro m hm ih _ h
    have hrest : ∀ k ∈ Finset.Ico i m, compare (f k) (f (k + 1)) = Ordering.lt :=
      fun k hk => h k (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hk).1,
        by have := (Finset.mem_Ico.mp hk).2; omega⟩)
    have hprev : compare (f i) (f m) = Ordering.lt := ih (by omega) hrest
    have hstep : compare (f m) (f (m + 1)) = Ordering.lt :=
      h m (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    exact Std.TransCmp.lt_of_lt_of_le hprev (by rw [hstep]; decide)

/-- The minimum over `[i, m]` splits off its last point: `min (g m) (inf' over [i, m))`. -/
theorem min_inf'_Ico_succ {β : Type*} [LinearOrder β] (g : ℕ → β) {i m : ℕ} (him : i ≤ m)
    {H : (Finset.Ico i (m + 1)).Nonempty} {H' : (Finset.Ico i m).Nonempty} :
    min (g m) ((Finset.Ico i m).inf' H' g) = (Finset.Ico i (m + 1)).inf' H g := by
  refine le_antisymm ?_ ?_
  · refine Finset.le_inf' H g (fun b hb => ?_)
    have hbm : b ≤ m := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hb).2
    rcases Nat.lt_or_eq_of_le hbm with hlt | heq
    · exact (min_le_right _ _).trans
        (Finset.inf'_le g (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hb).1, hlt⟩))
    · subst heq
      exact min_le_left _ _
  · refine le_min ?_ ?_
    · exact Finset.inf'_le g (Finset.mem_Ico.mpr ⟨him, Nat.lt_succ_self m⟩)
    · exact Finset.le_inf' H' g (fun b hb =>
        Finset.inf'_le g (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hb).1,
          by have := (Finset.mem_Ico.mp hb).2; omega⟩))

/-- **The min property of the LCP array.**  For a chain `f` that is strictly increasing in
lexicographic order on `[i, j)`, the LCP of the two extreme members is the minimum of the
neighbouring LCPs along the chain. -/
theorem lcp_eq_inf'_of_chain {f : ℕ → List α} {i j : ℕ} (hij : i < j)
    (hchain : ∀ k ∈ Finset.Ico i j, compare (f k) (f (k + 1)) = Ordering.lt) :
    lcp (f i) (f j) =
      (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (fun k => lcp (f k) (f (k + 1))) := by
  revert hij hchain
  refine Nat.le_induction ?_ ?_ j (by omega : i + 1 ≤ j)
  · -- one point: the minimum is the single neighbouring LCP
    intro hij hchain
    refine le_antisymm ?_ ?_
    · refine Finset.le_inf' _ _ (fun b hb => ?_)
      have hb' : b = i := by have := (Finset.mem_Ico.mp hb).2; omega
      subst hb'
      exact le_rfl
    · exact Finset.inf'_le _ (Finset.mem_Ico.mpr ⟨le_rfl, hij⟩)
  · -- extend the interval by one point
    intro m hm ih hij hchain
    have hrest : ∀ k ∈ Finset.Ico i m, compare (f k) (f (k + 1)) = Ordering.lt :=
      fun k hk => hchain k (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hk).1,
        by have := (Finset.mem_Ico.mp hk).2; omega⟩)
    have hprev : compare (f i) (f m) = Ordering.lt :=
      compare_lt_of_chain (by omega) hrest
    have hstep : compare (f m) (f (m + 1)) = Ordering.lt :=
      hchain m (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    have hthree := lcp_eq_min_lcp_of_compare_lt hprev hstep
    have hih := ih (by omega) hrest
    rw [hthree, hih, Nat.min_comm]
    exact min_inf'_Ico_succ _ (le_of_lt (by omega))

/-! ### The suffix-array reading (M1a, M1b) -/

/-- **The LCP array's min property**, in the form a suffix array supplies it: `π` lists
suffix *positions* by rank, and if the enumerated suffixes strictly increase then the LCP of
the suffixes at ranks `i < j` is the minimum of the neighbouring LCPs between those ranks. -/
theorem lcp_suffix_eq_inf'_of_increasing (s : List α) (π : ℕ → ℕ) {i j : ℕ} (hij : i < j)
    (hinc : ∀ k ∈ Finset.Ico i j, compare (suffix s (π k)) (suffix s (π (k + 1))) = Ordering.lt) :
    lcp (suffix s (π i)) (suffix s (π j)) =
      (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij)
        (fun k => lcp (suffix s (π k)) (suffix s (π (k + 1)))) :=
  lcp_eq_inf'_of_chain hij hinc

/-- **M1b: a comparison guided by the LCP array inspects exactly one position.**  Between
ranks `i < j` of a strictly increasing enumeration, the interval minimum of the neighbouring
LCPs is the true LCP, so the guided comparison skips all of it. -/
theorem inspectCount_inf'_of_increasing (s : List α) (π : ℕ → ℕ) {i j : ℕ} (hij : i < j)
    (hinc : ∀ k ∈ Finset.Ico i j, compare (suffix s (π k)) (suffix s (π (k + 1))) = Ordering.lt) :
    inspectCount s ((Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij)
        (fun k => lcp (suffix s (π k)) (suffix s (π (k + 1))))) (π i) (π j) = 1 := by
  rw [lcp_suffix_eq_inf'_of_increasing s π hij hinc]
  exact inspectCount_lcp s (π i) (π j)

/-- The guided comparison is also *correct*, so the single inspection decides the answer. -/
theorem cmpFrom_inf'_of_increasing (s : List α) (π : ℕ → ℕ) {i j : ℕ} (hij : i < j)
    (hinc : ∀ k ∈ Finset.Ico i j, compare (suffix s (π k)) (suffix s (π (k + 1))) = Ordering.lt) :
    cmpFrom s ((Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij)
        (fun k => lcp (suffix s (π k)) (suffix s (π (k + 1))))) (π i) (π j) =
      compare (suffix s (π i)) (suffix s (π j)) := by
  rw [lcp_suffix_eq_inf'_of_increasing s π hij hinc]
  exact cmpFrom_lcp_advance s (π i) (π j)

end SortBounds.Projects.SAIS
