/-
SortBounds/Projects/SAIS/Array.lean

The LCP array of a string taken in **text order**: `lcpAt s i` is the LCP of the
neighbouring suffixes `i` and `i + 1`.  This file proves what that array is good for and
what it is *not* good for.

* `inf'_lcpAt_le_lcp` — the text-order LCP array is a **sound lower bound**: for `i < j`,
  the minimum of `lcpAt` over the text interval `[i, j)` never exceeds the true
  `lcp` of the two suffixes.  (A sliding-window chain: if every neighbouring pair agrees
  on its first `m` characters, then suffix `i` and suffix `j` agree on their first `m`
  characters too.)
* `cmpFrom_inf'_lcpAt` — hence the minimum is a *legal* skip for the cost model:
  guiding the comparison with it does not change the answer.
* `inspectCount_inf'_lcpAt` / `inspectCount_inf'_lcpAt_eq_one_iff` — the guided comparison
  inspects exactly `1 + (lcp - inf)` positions, i.e. exactly **one** if and only if the
  bound `inf` is tight.
* `inf'_lcpAt_ne_lcp` — the bound is *not* always tight: the reverse inequality fails, so
  the min property of the lane README (`M1 target`, M1a) is **false in text order**.  For
  `s = "aba"`, `i = 0`, `j = 2`, the minimum over `{0, 1}` is `0` (each neighbouring pair
  differs at its very first character) while `lcp (suffix 0) (suffix 2) = 1`.  The min
  property is a statement about *lexicographically* neighbouring suffixes, i.e. about a
  suffix array, and it is proved in `Chain.lean`.

One convention, inherited from `LCP.lean`: suffixes are indexed by plain naturals and
`suffix s i = s.drop i` is total, so `lcpAt s i` is defined for every `i`, and `lcpAt s i = 0`
once `i ≥ s.length`.
-/
import SortBounds.Projects.SAIS.LCP

namespace SortBounds.Projects.SAIS

variable {α : Type*}

/-- **Sliding windows.**  If every `m`-window of `s` starting in `[i, j)` agrees with the
next one, then the `m`-windows at `i` and at `j` agree. -/
theorem take_drop_chain {s : List α} {m : ℕ} {i j : ℕ} (hij : i ≤ j)
    (h : ∀ k ∈ Finset.Ico i j, (s.drop k).take m = (s.drop (k + 1)).take m) :
    (s.drop i).take m = (s.drop j).take m := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ n hin ih =>
    have hstep : (s.drop n).take m = (s.drop (n + 1)).take m :=
      h n (Finset.mem_Ico.mpr ⟨hin, Nat.lt_succ_self n⟩)
    have hrest : ∀ k ∈ Finset.Ico i n, (s.drop k).take m = (s.drop (k + 1)).take m :=
      fun k hk => h k (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hk).1,
        by have := (Finset.mem_Ico.mp hk).2; omega⟩)
    exact (ih hrest).trans hstep

/-! ### The LCP array in text order -/

section LcpAt
variable [DecidableEq α]

/-- `lcpAt s i` is the LCP of the neighbouring suffixes `i` and `i + 1`, i.e. the `i`-th
entry of the LCP array of `s` read in *text* order. -/
def lcpAt (s : List α) (i : ℕ) : ℕ := lcp (suffix s i) (suffix s (i + 1))

theorem lcpAt_def (s : List α) (i : ℕ) :
    lcpAt s i = lcp (suffix s i) (suffix s (i + 1)) := rfl

/-- The entry is a prefix of both suffixes it compares. -/
theorem lcpAt_le_left (s : List α) (i : ℕ) : lcpAt s i ≤ (suffix s i).length :=
  lcp_le_left _ _

theorem lcpAt_le_right (s : List α) (i : ℕ) : lcpAt s i ≤ (suffix s (i + 1)).length :=
  lcp_le_right _ _

/-- **The text-order LCP array is a sound lower bound.**  For `i < j`, the minimum of
`lcpAt` over the text interval `[i, j)` is at most the LCP of suffixes `i` and `j`. -/
theorem inf'_lcpAt_le_lcp {s : List α} {i j : ℕ} (hij : i < j) :
    (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s) ≤
      lcp (suffix s i) (suffix s j) := by
  have hmem_i : i ∈ Finset.Ico i j := Finset.mem_Ico.mpr ⟨le_rfl, hij⟩
  have hmem_j : j - 1 ∈ Finset.Ico i j := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hlen : (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s) ≤
      min (suffix s i).length (suffix s j).length := by
    have h1 : (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s) ≤ lcpAt s i :=
      Finset.inf'_le _ hmem_i
    have h2 : (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s) ≤ lcpAt s (j - 1) :=
      Finset.inf'_le _ hmem_j
    have h3 : lcpAt s i ≤ (suffix s i).length := lcpAt_le_left s i
    have h4 : lcpAt s (j - 1) ≤ (suffix s j).length := by
      have h := lcpAt_le_right s (j - 1)
      rwa [show (j - 1) + 1 = j by omega] at h
    exact le_min (h1.trans h3) (h2.trans h4)
  refine le_lcp_of_take_eq hlen ?_
  have hstep : ∀ k ∈ Finset.Ico i j,
      (suffix s k).take ((Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s)) =
        (suffix s (k + 1)).take
          ((Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s)) := by
    intro k hk
    have hle : (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s) ≤
        lcp (suffix s k) (suffix s (k + 1)) := Finset.inf'_le (f := lcpAt s) hk
    exact take_eq_take_iff.mpr (Or.inl hle)
  exact take_drop_chain (le_of_lt hij) hstep

end LcpAt

/-! ### What that bound does to a comparison -/

section Cost
variable [LinearOrder α]

/-- **The bound can be used as a skip.**  Guiding the comparison of suffixes `i` and `j`
with the text-order LCP minimum does not change its answer. -/
theorem cmpFrom_inf'_lcpAt (s : List α) {i j : ℕ} (hij : i < j) :
    cmpFrom s ((Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s)) i j =
      compare (suffix s i) (suffix s j) :=
  cmpFrom_eq_compare_of_le_lcp s _ i j (inf'_lcpAt_le_lcp hij)

/-- The characters the text-order bound lets the comparison skip are really skipped: the
guided count plus the bound is the naive count. -/
theorem inspectCount_inf'_lcpAt_add (s : List α) {i j : ℕ} (hij : i < j) :
    inspectCount s ((Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s)) i j +
        (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s) =
      inspectCount s 0 i j := by
  have hmem : i ∈ Finset.Ico i j := Finset.mem_Ico.mpr ⟨le_rfl, hij⟩
  have hlen : (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s) ≤
      (suffix s i).length :=
    (Finset.inf'_le (s := Finset.Ico i j) (lcpAt s) hmem).trans (lcpAt_le_left s i)
  have h := inspectCount_eq_add s _ i j (take_eq_of_le_lcp (inf'_lcpAt_le_lcp hij)) hlen
  omega

/-- **The guided comparison inspects `1 + (lcp - inf)` positions**: one for the deciding
position, one for each character past the supplied bound. -/
theorem inspectCount_inf'_lcpAt (s : List α) {i j : ℕ} (hij : i < j) :
    inspectCount s ((Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s)) i j =
      1 + (lcp (suffix s i) (suffix s j) -
        (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s)) := by
  have h := inspectCount_inf'_lcpAt_add s hij
  have hle := inf'_lcpAt_le_lcp (s := s) hij
  have h0 : inspectCount s 0 i j = 1 + lcp (suffix s i) (suffix s j) := inspectCount_zero s i j
  omega

/-- **Exactly one inspection iff the bound is tight.**  The text-order bound saves every
character it covers and nothing more, so a comparison costs the minimum `1` precisely when
the interval minimum really is the LCP. -/
theorem inspectCount_inf'_lcpAt_eq_one_iff (s : List α) {i j : ℕ} (hij : i < j) :
    inspectCount s ((Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s)) i j = 1 ↔
      (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr hij) (lcpAt s) =
        lcp (suffix s i) (suffix s j) := by
  have h := inspectCount_inf'_lcpAt (s := s) hij
  have hle := inf'_lcpAt_le_lcp (s := s) hij
  constructor
  · intro h1
    rw [h1] at h
    omega
  · intro h1
    rw [h]
    omega

end Cost

/-! ### The min property is false in text order

The lane README's `M1 target` states the min property over the text interval `[i, j)`.
That statement is refutable, and the refutation is the honest companion of
`inf'_lcpAt_le_lcp`: the text-order minimum is only a lower bound. -/

section Refutation
variable [DecidableEq α]

/-- On `"aba"` suffixes `0` and `2` share one character. -/
theorem lcp_suffix_aba : lcp (suffix ['a', 'b', 'a'] 0) (suffix ['a', 'b', 'a'] 2) = 1 := by
  simp [suffix, lcp]

/-- Yet the text-order minimum over `[0, 2)` is `0`: suffixes `0` and `1`, and suffixes `1`
and `2`, differ immediately. -/
theorem inf'_lcpAt_aba : (Finset.Ico 0 2).inf' (Finset.nonempty_Ico.mpr (by decide))
    (lcpAt (α := Char) ['a', 'b', 'a']) = 0 := by
  have hle : (Finset.Ico 0 2).inf' (Finset.nonempty_Ico.mpr (by decide))
      (lcpAt (α := Char) ['a', 'b', 'a']) ≤ 0 := by
    have h := Finset.inf'_le (s := Finset.Ico 0 2) (f := lcpAt (α := Char) ['a', 'b', 'a'])
      (b := 1) (Finset.mem_Ico.mpr ⟨by decide, by decide⟩)
    simpa [lcpAt, suffix, lcp] using h
  omega

/-- **The min property of the README fails in text order.**  The text interval `[0, 2)` of
`"aba"` has minimum `0`, but `lcp (suffix 0) (suffix 2) = 1`. -/
theorem inf'_lcpAt_ne_lcp :
    (Finset.Ico 0 2).inf' (Finset.nonempty_Ico.mpr (by decide))
        (lcpAt (α := Char) ['a', 'b', 'a']) ≠
      lcp (suffix ['a', 'b', 'a'] 0) (suffix ['a', 'b', 'a'] 2) := by
  rw [inf'_lcpAt_aba, lcp_suffix_aba]
  decide

/-- The same failure, restated existentially: the two sides of the README's M1a differ for
some string and some interval, so no proof of it exists. -/
theorem exists_inf'_lcpAt_ne_lcp :
    ∃ (s : List Char) (i j : ℕ) (h : i < j),
      (Finset.Ico i j).inf' (Finset.nonempty_Ico.mpr h) (lcpAt s) ≠
        lcp (suffix s i) (suffix s j) :=
  ⟨['a', 'b', 'a'], 0, 2, by decide, inf'_lcpAt_ne_lcp⟩

end Refutation

end SortBounds.Projects.SAIS
