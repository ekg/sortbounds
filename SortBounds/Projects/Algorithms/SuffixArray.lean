/-
SortBounds/Projects/Algorithms/SuffixArray.lean

**Job 2 of this lane: the suffix array, the BWT and the run count `r`.**

`r` (the number of runs in the BWT) is the measure that decides index choice in practice
(Gagie–Navarro–Prezza, J. ACM 2020), and computing it needs a suffix array.  This file builds
the **correct, slow** one and nothing faster:

* `suffixArray s : List ℕ` — the suffixes of `s` in lexicographic order, as start positions;
* `suffixArray_perm` — it is a permutation of `List.range s.length` (a sort, not a filter);
* `suffixArray_sorted` — pairwise lexicographically increasing (`List.lt`, i.e. `Lex (· < ·)`);
* `bwt s : List α` — the last column read off the suffix array;
* `numRuns s : ℕ` — the number of maximal blocks of equal letters of `bwt s`.

**Cost, stated not claimed.**  `suffixArray` is `List.mergeSort` with a comparison that is
itself a lexicographic comparison of two suffixes: `O(n log n)` suffix comparisons, each
`O(n)` character inspections in the worst case, so **`O(n² log n)` character work and `O(n²)`
total** for a text of length `n`.  That is deliberate — this lane is about being executable and
correct, and the prefix-doubling / SA-IS (`O(n)`, Nong–Zhang–Chan 2009; DC3,
Kärkkäinen–Sanders 2003) algorithms are the roadmap, not a claim made here.  `bwt` and
`numRuns` are one linear pass each on top of that.

**The order.**  Suffixes are compared by Mathlib's lexicographic order on `List α`
(`List.instLinearOrder`, from `Lex (· < ·)`): at the first differing character the smaller
character wins, and a proper prefix is smaller than what extends it — which is the suffix order
of suffix-array literature.  Ties are worth one remark: two *distinct* positions of one word
never have equal suffixes (`suffix_injOn`, their lengths differ), so `compare … = Ordering.eq`
never occurs in `suffixArray s` and the strict statement `suffixArray_sorted` loses nothing.

Said in `List.lt` and not through `compare`: `List α` carries *two* `Ord` instances — core's
`List.instOrd` (`List.compareLex compare`) and the one bundled in `List.instLinearOrder` — so a
statement about `compare` has to pick one, and the bridge `compare … = Ordering.lt ↔ · < ·`
(`compare_lt_iff_lt`) exists only for the second (`Std.LawfulOrderOrd (List α)` is not an
instance for the first).  `suffixArray_sorted` is that statement in the form the kernel accepts.

**The BWT convention.**  `bwt s` uses the **wrap-around convention**: for the row of the suffix
starting at `0` the preceding character is `s[n-1]`, i.e. `s` is read cyclically.  (The other
convention inserts a sentinel `$` smaller than every letter, which makes the last column one
character *longer* than the text; we keep the text's length so that `bwt_length` is an
equality, and say so here rather than pretend the two conventions give the same number.)  The
run count `r` is therefore the run count of *this* column; comparing it against `r` computed
with a sentinel needs the sentinel and is not attempted in this file.
-/
import Mathlib
import SortBounds.Projects.SAIS.LCP
import SortBounds.Projects.Algorithms.Texts

namespace SortBounds.Projects.Algorithms

open SortBounds.Projects.SAIS (suffix)

variable {α : Type*} [LinearOrder α]

/-! ### The order on suffixes -/

/-- Is the suffix at `i` lexicographically at most the suffix at `j`?  A `Bool`, so that
`List.mergeSort` can use it; the relation is the lexicographic order on words described in the
file header. -/
def suffixLE (s : List α) (i j : ℕ) : Bool := decide (suffix s i ≤ suffix s j)

theorem suffixLE_eq_true {s : List α} {i j : ℕ} :
    suffixLE s i j = true ↔ suffix s i ≤ suffix s j :=
  by
  rw [suffixLE]
  exact decide_eq_true_iff

omit [LinearOrder α] in
/-- **Suffixes at distinct positions are distinct.**  Their lengths are `n - i` and `n - j`,
which differ when `i ≠ j` and both positions are inside the word.  This is why the suffix array
has no ties to break. -/
theorem suffix_injOn {s : List α} {i j : ℕ} (hi : i ≤ s.length) (hj : j ≤ s.length)
    (h : suffix s i = suffix s j) : i = j := by
  have hlen : s.length - i = s.length - j := by
    have := congrArg List.length h
    simpa using this
  omega

/-! ### The suffix array -/

/-- **The suffix array**: the suffixes of `s` in lexicographic order, as start positions, by
`List.mergeSort` on the comparison `suffixLE s`.  `O(n² log n)` character work — see the file
header; this is the simple version, not SA-IS. -/
def suffixArray (s : List α) : List ℕ :=
  (List.range s.length).mergeSort (suffixLE s)

@[simp]
theorem length_suffixArray (s : List α) : (suffixArray s).length = s.length := by
  rw [suffixArray, List.length_mergeSort, List.length_range]

/-- **The suffix array is a permutation of `List.range s.length`**: it lists every start position
exactly once (so it is a sort of the positions, not a selection of some of them). -/
theorem suffixArray_perm (s : List α) : (suffixArray s).Perm (List.range s.length) :=
  List.mergeSort_perm _ _

theorem suffixArray_nodup (s : List α) : (suffixArray s).Nodup :=
  (suffixArray_perm s).symm.nodup List.nodup_range

theorem mem_suffixArray {s : List α} {i : ℕ} : i ∈ suffixArray s ↔ i < s.length := by
  rw [(suffixArray_perm s).mem_iff, List.mem_range]

/-- The sort relation is a total, transitive `Bool` relation, so `mergeSort` returns a list that is
nondecreasing in suffix order: every pair of entries, in array order, compares `≤`. -/
theorem suffixArray_pairwise (s : List α) :
    (suffixArray s).Pairwise (fun i j => suffix s i ≤ suffix s j) := by
  have h := List.pairwise_mergeSort (l := List.range s.length) (le := suffixLE s)
    (fun i j k hij hjk => by
      rw [suffixLE_eq_true] at hij hjk ⊢
      exact le_trans hij hjk)
    (fun i j => by
      rw [Bool.or_eq_true, suffixLE_eq_true, suffixLE_eq_true]
      exact le_total (suffix s i) (suffix s j))
  exact h.imp fun hij => suffixLE_eq_true.mp hij

/-- **The suffix array is sorted**: for every pair `i < j` of array positions, the suffix at
`(suffixArray s)[i]` is strictly smaller than the suffix at `(suffixArray s)[j]` (`List.Pairwise` is
the all-pairs condition, not just the consecutive one).  Strict, because no two distinct positions
have equal suffixes (`suffix_injOn`) — the `≤` form is `suffixArray_pairwise`. -/
theorem suffixArray_sorted (s : List α) :
    (suffixArray s).Pairwise (fun i j => suffix s i < suffix s j) := by
  rw [List.pairwise_iff_getElem]
  have hle := suffixArray_pairwise s
  rw [List.pairwise_iff_getElem] at hle
  intro i j hi hj hij
  have hi' : (suffixArray s)[i] < s.length := mem_suffixArray.mp (List.getElem_mem hi)
  have hj' : (suffixArray s)[j] < s.length := mem_suffixArray.mp (List.getElem_mem hj)
  have hne : (suffixArray s)[i] ≠ (suffixArray s)[j] := by
    intro he
    exact absurd ((suffixArray_nodup s).getElem_inj.mp he) (by omega)
  have hne' : suffix s ((suffixArray s)[i]) ≠ suffix s ((suffixArray s)[j]) := by
    intro he
    exact hne (suffix_injOn (by omega) (by omega) he)
  exact lt_of_le_of_ne (hle i j hi hj hij) hne'

/-! ### Uniqueness: the sorted order is the suffix array -/

/-- **A strictly ordered permutation is unique**: if two permutations of the same multiset are
both pairwise `R`-increasing and `R` is antisymmetric, they are equal.  (`R` need not be total:
antisymmetry is enough, because the head of a `Pairwise R` list is `R`-below its tail, so the two
heads must coincide.) -/
theorem eq_of_pairwise_perm {β : Type*} {R : β → β → Prop}
    (hantisymm : ∀ a b, R a b → ¬ R b a) :
    ∀ {l₁ l₂ : List β}, l₁.Perm l₂ → l₁.Pairwise R → l₂.Pairwise R → l₁ = l₂
  | [], l₂, hperm, _, _ => (List.perm_nil.mp hperm.symm).symm
  | _ :: _, [], hperm, _, _ => absurd (List.perm_nil.mp hperm) (by simp)
  | a :: l₁', b :: l₂', hperm, h₁, h₂ => by
    have hmin₁ : ∀ x ∈ l₁', R a x := (List.pairwise_cons.mp h₁).1
    have hmin₂ : ∀ x ∈ l₂', R b x := (List.pairwise_cons.mp h₂).1
    have ha : a ∈ b :: l₂' := hperm.mem_iff.mp List.mem_cons_self
    have hb : b ∈ a :: l₁' := hperm.mem_iff.mpr List.mem_cons_self
    have hba : b = a := by
      rcases List.mem_cons.mp ha with h | h
      · exact h.symm
      · rcases List.mem_cons.mp hb with h' | h'
        · exact h'
        · exact absurd (hmin₁ b h') (hantisymm a b · (hmin₂ a h))
    subst hba
    have ih := eq_of_pairwise_perm hantisymm (List.perm_cons b |>.mp hperm)
      (List.pairwise_cons.mp h₁).2 (List.pairwise_cons.mp h₂).2
    rw [ih]

/-- **The suffix array is the *only* sorted list of positions**: any permutation of `List.range
s.length` that is pairwise increasing in suffix order equals `suffixArray s`.  With
`suffixArray_perm` and `suffixArray_sorted` this characterizes the suffix array completely, and it
is what makes concrete values provable in the kernel — `suffixArray` itself is defined by
`List.mergeSort`, which the kernel does not reduce (`#eval` only). -/
theorem suffixArray_unique {s : List α} {l : List ℕ} (hperm : l.Perm (List.range s.length))
    (hsorted : l.Pairwise (fun i j => suffix s i < suffix s j)) : l = suffixArray s :=
  eq_of_pairwise_perm (R := fun i j => suffix s i < suffix s j)
    (fun _ _ h => lt_asymm h) (hperm.trans (suffixArray_perm s).symm) hsorted
    (suffixArray_sorted s)

/-- `0` appears in the suffix array of a nonempty word — the empty suffix, the smallest one. -/
theorem zero_mem_suffixArray {s : List α} (hs : s ≠ []) : 0 ∈ suffixArray s := by
  rw [mem_suffixArray]
  cases s with
  | nil => exact absurd rfl hs
  | cons _ _ => simp

/-! ### The last column (BWT) -/

/-- **`bwt s`: the last column of the sorted suffixes**, in the wrap-around convention: for each
start position `j` of `suffixArray s`, the character of `s` that precedes `j` when `s` is read
cyclically, i.e. `s[(j + n - 1) % n]` (`s[n-1]` when `j = 0`).  Written with `drop`/`take` rather
than a `Fin` index so that the definition needs no proof term: `#eval` — and rewriting with a known
suffix array — both work.  Cost: one pass over the suffix array, `O(n)` on top of it. -/
def bwt (s : List α) : List α :=
  ((suffixArray s).map fun j => (s.drop ((j + s.length - 1) % s.length)).take 1).flatten

omit [LinearOrder α] in
/-- Flattening a map that produces singletons preserves length. -/
theorem length_flatten_map_eq {l : List ℕ} {f : ℕ → List α} (h : ∀ j ∈ l, (f j).length = 1) :
    (l.map f).flatten.length = l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    rw [h a (by simp), ih fun j hj => h j (by simp [hj])]
    omega

/-- **The last column has the text's length** — the reason for the wrap-around convention: with a
sentinel it would be `n + 1`.  Each suffix position contributes exactly one character, because
`j < n` makes the wrapped index a valid position of `s`. -/
theorem bwt_length (s : List α) : (bwt s).length = s.length := by
  rw [bwt, length_flatten_map_eq (fun j hj => ?_), length_suffixArray]
  have hjs : j < s.length := mem_suffixArray.mp hj
  have hpos : 0 < s.length := by omega
  rw [List.length_take, List.length_drop]
  have := Nat.mod_lt (j + s.length - 1) hpos
  omega

/-! ### The number of runs `r` -/

/-- The number of maximal blocks of equal letters of a word. -/
def numRunsOf : List α → ℕ
  | [] => 0
  | [_] => 1
  | a :: b :: t => (if a = b then 0 else 1) + numRunsOf (b :: t)

/-- **`r`: the number of runs in the BWT** of `s` — the measure that decides index choice in
practice (Gagie–Navarro–Prezza 2020).  Computed from `bwt s`, hence from the suffix array: this
is the slow `O(n² log n)` route, not `O(n)`/SA-IS. -/
def numRuns (s : List α) : ℕ := numRunsOf (bwt s)

@[simp]
theorem numRunsOf_nil : numRunsOf ([] : List α) = 0 := rfl

/-- A nonempty word has at least one run. -/
theorem numRunsOf_pos : ∀ {l : List α}, l ≠ [] → 0 < numRunsOf l
  | [], h => absurd rfl h
  | [_], _ => by simp [numRunsOf]
  | a :: b :: t, _ => by
    have ih : 0 < numRunsOf (b :: t) := numRunsOf_pos (by simp)
    simp only [numRunsOf]
    split <;> omega

/-- `r` is at most the number of characters it counts runs of: the run count is a count of
block starts. -/
theorem numRunsOf_le_length : ∀ l : List α, numRunsOf l ≤ l.length
  | [] => le_rfl
  | [_] => le_rfl
  | a :: b :: t => by
    have ih : numRunsOf (b :: t) ≤ (b :: t).length := numRunsOf_le_length (b :: t)
    simp only [numRunsOf, List.length_cons] at ih ⊢
    split <;> omega

/-- **`r ≤ n`**: the run count of the last column is bounded by the text's length. -/
theorem numRuns_le_length (s : List α) : numRuns s ≤ s.length := by
  rw [numRuns, ← bwt_length]
  exact numRunsOf_le_length (bwt s)

/-- **`r ≥ 1` for every nonempty text** — the run count is not degenerate. -/
theorem numRuns_pos {s : List α} (hs : s ≠ []) : 0 < numRuns s := by
  refine numRunsOf_pos ?_
  intro h
  apply hs
  have hlen : (bwt s).length = 0 := by rw [h]; rfl
  rw [bwt_length, List.length_eq_zero_iff] at hlen
  exact hlen

/-! ### Running the suffix array, the BWT and `r`

`#eval` runs these through the compiler.  `decide` could not: `List.mergeSort` is well-founded
recursion, so the kernel does not reduce `suffixArray s`.  Concrete values are therefore *proved*
through `suffixArray_unique` (state the candidate list, check permutation and sortedness by
`decide`, get equality) — see `suffixArray_mississippi` below — and only the texts whose suffix
array is not spelled out are `#eval` only.  Deciding with the native code generator instead is
forbidden in this repository (`make check` greps for it), so `decide` in the kernel is the only
route. -/

#eval suffixArray ([] : List Char)
#eval suffixArray mississippi
#eval bwt mississippi
#eval numRuns mississippi
#eval suffixArray (['a', 'b', 'a', 'b', 'a'] : List Char)
#eval bwt (['a', 'b', 'a', 'b', 'a'] : List Char)
#eval numRuns (['a', 'b', 'a', 'b', 'a'] : List Char)
#eval numRuns (['a', 'a', 'a'] : List Char)
#eval numRuns (fibWord 6)
#eval numRuns (fibWord 8)
#eval bwt (fibWord 6)

/-- The last column of the empty text is empty: a one-line check that `bwt` does not conjure a
character out of the wrap-around when there is no character to wrap. -/
theorem bwt_nil (α : Type*) [LinearOrder α] : bwt ([] : List α) = [] := by
  simp [bwt, suffixArray]

/-- **The suffix array of `"mississippi"`, proved** (not only `#eval`ed): `[10, 7, 4, 1, 0, 9, 8,
6, 3, 5, 2]` is a permutation of `range 11` and pairwise increasing in suffix order, so by
`suffixArray_unique` it *is* `suffixArray mississippi`. -/
theorem suffixArray_mississippi :
    suffixArray mississippi = [10, 7, 4, 1, 0, 9, 8, 6, 3, 5, 2] := by
  refine (suffixArray_unique (s := mississippi) ?_ ?_).symm
  · decide
  · decide

/-- **The last column of `"mississippi"`, proved**: with the suffix array known, `bwt` reduces.  The
textbook BWT of `"mississippi$"` is `ipssm$pissii`; deleting the `$` row and replacing `$` by the
wrap-around character `i` gives this word (see the convention note in the file header). -/
theorem bwt_mississippi :
    bwt mississippi = ['p', 's', 's', 'm', 'i', 'p', 'i', 's', 's', 'i', 'i'] := by
  rw [bwt, suffixArray_mississippi]
  decide

/-- **`r = 8` on `"mississippi"`, proved**: the runs of `pssmipissii` are `p | ss | m | i | p | i |
ss | ii`.  (The textbook last column of `mississippi$` is `ipssm$pissii`, `9` runs.  Ours is that
word with the first entry — the row-`0` character, the one preceding the sentinel — deleted and `$`
replaced by that same character `i`; the deleted entry was a run by itself, which is the one run of
difference here.) -/
theorem numRuns_mississippi : numRuns mississippi = 8 := by
  rw [numRuns, bwt_mississippi]
  decide

/-- `r` of the empty text is `0`: nothing to compress. -/
theorem numRuns_nil (α : Type*) [LinearOrder α] : numRuns ([] : List α) = 0 := by
  simp [numRuns, bwt_nil]

end SortBounds.Projects.Algorithms
