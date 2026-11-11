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
* `compare_lt_of_chain_aux` — strict increase of neighbours makes every pair in the interval
  strictly increasing;
* `lcp_eq_inf'_of_chain` — **the min property**: for a chain `f` that is strictly increasing
  on `[i, j)`, `lcp (f i) (f j) = (Ico i j).inf' fun k => lcp (f k) (f (k+1))`;
* `lcp_suffix_eq_inf'_of_increasing` — the same for the suffixes of a string enumerated by a
  candidate suffix array `π` (so `f k = suffix s (π k)`), and
  `inspectCount_inf'_of_increasing` — **hence an LCP-guided comparison inspects exactly one
  position** (M1b): the LCP array's interval minimum *is* the true LCP, so
  `inspectCount s inf (π i) (π j) = 1`, and by `cmpFrom_lcp_advance` the comparison is also
  correct.

The `i = j` case of the M1a statement has no content and no `inf'`: `Ico i i = ∅` is not
nonempty, and `lcp (suffix s i) (suffix s i) = (suffix s i).length`, which no interval
minimum can express.  Every statement below carries `i < j`, which is also exactly what the
README's nonemptiness argument `⟨i, ?_⟩` requires.
-/
import SortBounds.Projects.SAIS.Array

namespace SortBounds.Projects.SAIS

variable {α : Type*} [LinearOrder α]

/-! ### `lcp` along a lexicographically sorted chain -/

/-- The arithmetic of `min` and `+ 1`, in the shape the induction below produces. -/
theorem min_succ_succ (p q : ℕ) : min (p + 1) (q + 1) = min p q + 1 := by omega

/-- **The three-list lemma.**  If `a`, `b`, `c` are strictly increasing in lexicographic
order then the LCP of `a` and `c` is the smaller of the two neighbouring LCPs.  (This is
where the min property comes from: the common prefix of the extremes is cut down by
whichever neighbouring pair separates first.) -/
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
          · -- `y < z`, so the second neighbour separates immediately
            have hyz : y ≠ z := ne_of_lt (compare_lt_iff_lt.mp hyz_lt)
            have hxz : x ≠ z := by rw [hxy]; exact hyz
            simp [lcp_cons_cons, hxy, hyz]
          · -- `x = y = z`: reduce to the tails
            have hyz : y = z := compare_eq_iff_eq.mp hyz_eq
            have hxz : x = z := hxy.trans hyz
            rw [lcp_cons_cons, lcp_cons_cons, lcp_cons_cons, ite_eq_left hxy, ite_eq_left hxz,
              ite_eq_left hyz, ih hxs_lt hys_lt, min_succ_succ]

/-- Strict increase of neighbours gives strict increase of every pair of an interval, for a
chain known to be increasing up to a fixed `N`. -/
theorem compare_lt_of_chain_aux {f : ℕ → List α} {i N : ℕ}
    (hchain : ∀ k ∈ Finset.Ico i N, compare (f k) (f (k + 1)) = Ordering.lt) :
    ∀ n : ℕ, i < n → n ≤ N → compare (f i) (f n) = Ordering.lt
  | 0, hin, _ => absurd hin (by omega)
  | n + 1, hin, hnN => by
    have hn : n ≤ N := by omega
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hin) with hlt | heq
    · have ih := compare_lt_of_chain_aux hchain n hlt hn
      have hstep : compare (f n) (f (n + 1)) = Ordering.lt :=
        hchain n (Finset.mem_Ico.mpr ⟨by omega, hnN⟩)
      exact Std.TransCmp.lt_of_lt_of_le ih (by rw [hstep]; decide)
    · -- `n = i`, one comparison
      subst heq
      exact hchain i (Finset.mem_Ico.mpr ⟨le_rfl, hnN⟩)

/-- Strict increase of neighbours gives strict increase of every pair of the interval. -/
theorem compare_lt_of_chain {f : ℕ → List α} {i n : ℕ} (hin : i < n)
    (hchain : ∀ k ∈ Finset.Ico i n, compare (f k) (f (k + 1)) = Ordering.lt) :
    compare (f i) (f n) = Ordering.lt :=
  compare_lt_of_chain_aux hchain n hin le_rfl

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

/-- The min property, for a chain increasing up to a fixed `N`. -/
theorem lcp_eq_inf'_of_chain_aux {f : ℕ → List α} {i N : ℕ}
    (hchain : ∀ k ∈ Finset.Ico i N, compare (f k) (f (k + 1)) = Ordering.lt) :
    ∀ n : ℕ, ∀ hin : i < n, n ≤ N →
      lcp (f i) (f n) =
        (Finset.Ico i n).inf' (Finset.nonempty_Ico.mpr hin) (fun k => lcp (f k) (f (k + 1)))
  | 0, hin, _ => absurd hin (by omega)
  | n + 1, hin, hnN => by
    have hn : n ≤ N := by omega
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hin) with hlt | heq
    · -- at least two points: split off the last one
      have hrest : ∀ k ∈ Finset.Ico i n, compare (f k) (f (k + 1)) = Ordering.lt :=
        fun k hk => hchain k (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hk).1, by
          have := (Finset.mem_Ico.mp hk).2; omega⟩)
      have hih := lcp_eq_inf'_of_chain_aux hrest n hlt le_rfl
      have hprev : compare (f i) (f n) = Ordering.lt := compare_lt_of_chain_aux hchain n hlt hn
      have hstep : compare (f n) (f (n + 1)) = Ordering.lt :=
        hchain n (Finset.mem_Ico.mpr ⟨by omega, hnN⟩)
      rw [lcp_eq_min_lcp_of_compare_lt hprev hstep, hih, Nat.min_comm]
      exact min_inf'_Ico_succ (fun k => lcp (f k) (f (k + 1))) (le_of_lt hlt)
    · -- one point: the minimum is the single neighbouring LCP
      subst heq
      refine le_antisymm ?_ ?_
      · refine Finset.le_inf' _ _ (fun b hb => ?_)
        have hb' : b = i := by
          obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hb
          omega
        subst hb'
        exact le_rfl
      · exact Finset.inf'_le _ (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)

/-- **The min property of the LCP array.**  For a chain `f` that is strictly increasing in
lexicographic order on `[i, j)`, the LCP of the two extremes is the minimum of the
neighbouring LCPs along the chain. -/
theorem lcp_eq_inf'_of_chain {f : ℕ → List α} {i j : ℕ} (hij : i < j)
    (hchain : ∀ k ∈ Finset.Ico i j, compare (f k) (f (k + 1)) = Ordering.lt) :
    lcp (f i) (f j) =
      (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (fun k => lcp (f k) (f (k + 1))) :=
  lcp_eq_inf'_of_chain_aux hchain j hij le_rfl

/-! ### The README's text-order statement, with the hypothesis it is missing

`Array.lean` refutes the min property over the *text* interval.  What it needs is exactly that
the text interval is itself increasing — then the text-order LCP array is the LCP array of that
run of suffixes, and the min property holds verbatim.  (`"aba"` fails this: suffix `1` is
greater than suffix `0`.) -/

/-- **The min property in text order**, for a text interval whose suffixes increase: the
README's M1a statement, repaired by the hypothesis `h` that the neighbouring suffixes of the
interval are strictly increasing. -/
theorem lcp_eq_inf'_lcpAt_of_increasing {s : List α} {i j : ℕ} (hij : i < j)
    (h : ∀ k ∈ Finset.Ico i j, compare (suffix s k) (suffix s (k + 1)) = Ordering.lt) :
    lcp (suffix s i) (suffix s j) =
      (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s) :=
  lcp_eq_inf'_of_chain (f := fun k => suffix s k) hij h

/-- Consequently the README's M1b statement holds under the same hypothesis: the guided
comparison inspects exactly one position. -/
theorem inspectCount_inf'_lcpAt_of_increasing {s : List α} {i j : ℕ} (hij : i < j)
    (h : ∀ k ∈ Finset.Ico i j, compare (suffix s k) (suffix s (k + 1)) = Ordering.lt) :
    inspectCount s ((Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s)) i j = 1 := by
  rw [← lcp_eq_inf'_lcpAt_of_increasing hij h]
  exact inspectCount_lcp s i j

/-- A witness for the repaired text-order statement: on `"aab"` the interval `[0, 2)` is
increasing, and `lcp (suffix 0) (suffix 2) = 0` is the minimum `min 1 0` of the two text-order
LCP entries — not the first of them on its own. -/
theorem aab_text_min_property :
    lcp (suffix ['a', 'a', 'b'] 0) (suffix ['a', 'a', 'b'] 2) =
      (Finset.Ico 0 2).inf' (Finset.nonempty_Ico.mpr (by decide)) (lcpAt (α := Char) ['a', 'a', 'b']) := by
  refine lcp_eq_inf'_lcpAt_of_increasing (by decide) ?_
  intro k hk
  have hk' : k = 0 ∨ k = 1 := by
    have := Finset.mem_Ico.mp hk
    omega
  rcases hk' with rfl | rfl <;> decide

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
  rw [← lcp_suffix_eq_inf'_of_increasing s π hij hinc]
  exact inspectCount_lcp s (π i) (π j)

/-- The guided comparison is also *correct*, so that single inspection decides the answer. -/
theorem cmpFrom_inf'_of_increasing (s : List α) (π : ℕ → ℕ) {i j : ℕ} (hij : i < j)
    (hinc : ∀ k ∈ Finset.Ico i j, compare (suffix s (π k)) (suffix s (π (k + 1))) = Ordering.lt) :
    cmpFrom s ((Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij)
        (fun k => lcp (suffix s (π k)) (suffix s (π (k + 1))))) (π i) (π j) =
      compare (suffix s (π i)) (suffix s (π j)) := by
  rw [← lcp_suffix_eq_inf'_of_increasing s π hij hinc]
  exact cmpFrom_lcp_advance s (π i) (π j)

/-! ### Non-vacuity

The hypotheses are satisfiable and the conclusion is not the trivial one: on `"banana"` the
suffix array is `[5, 3, 1, 0, 4, 2]`, its LCP array is `[1, 3, 0, 0, 2]`, and the minimum
over the ranks `[1, 4)` is `min 3 (min 0 0) = 0`, which is the LCP of suffixes `3` and `4`. -/

theorem banana_min_property :
    lcp (suffix ['b', 'a', 'n', 'a', 'n', 'a'] 3) (suffix ['b', 'a', 'n', 'a', 'n', 'a'] 4) =
      (Finset.Ico 1 4).inf' (Finset.nonempty_Ico.mpr (by decide))
        (fun k => lcp (suffix ['b', 'a', 'n', 'a', 'n', 'a'] ([5, 3, 1, 0, 4, 2].getD k 0))
          (suffix ['b', 'a', 'n', 'a', 'n', 'a'] ([5, 3, 1, 0, 4, 2].getD (k + 1) 0))) := by
  have hinc : ∀ k ∈ Finset.Ico 1 4,
      compare (suffix ['b', 'a', 'n', 'a', 'n', 'a'] ([5, 3, 1, 0, 4, 2].getD k 0))
        (suffix ['b', 'a', 'n', 'a', 'n', 'a'] ([5, 3, 1, 0, 4, 2].getD (k + 1) 0)) =
        Ordering.lt := by
    intro k hk
    have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by
      have := (Finset.mem_Ico.mp hk); omega
    rcases hk' with rfl | rfl | rfl <;> decide
  exact lcp_suffix_eq_inf'_of_increasing _ _ (by decide) hinc

end SortBounds.Projects.SAIS
