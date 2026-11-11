/-
SortBounds/Projects/XY/PairSums.lean

Sorting `X + Y`: the input object is the *multiset of pairwise sums* of two
finite sets `X, Y ⊂ ℕ` of size `n`, so the output alone has `n²` entries.  That
forces `Ω(n²)` *output*, and the generic `N`-item comparison bound gives
`log₂((n·m)!)` for a procedure that only sees the sums as `N = n·m` unordered
values.  It does **not** bound the `X + Y` problem: additive structure restricts
which orderings of the `n·m` sums are realizable, and Fredman (1976) gives a
scheme with `O(n²)` comparisons.  That escape is exactly the point of this lane.

This file (milestone `M0`) sets up that object and the counting facts that go
with it:

* `pairSums X Y` — the multiset `{x + y | x ∈ X, y ∈ Y}`, with multiplicity;
* `pairSums_card_le` — at most `X.card * Y.card` *distinct* sums (the multiset
  has exactly `X.card * Y.card` entries, `pairSums_card`);
* the `b = 2` instance of `Core.Branching`: a procedure that runs at most `c`
  binary tests has at most `2 ^ c` distinct transcripts, hence cannot separate
  more than `2 ^ c` inputs;
* the output-size observation, in its honest form: any comparison tree that
  sorts *every* `N = n·m`-element input with distinct values has depth
  `≥ log₂ ((n·m)!)`.  This is the generic bound re-indexed; it is **not** a bound
  on the `X + Y` problem (see Fredman 1976).
-/
import SortBounds.Core.Branching
import SortBounds.Comparison.Tree

namespace SortBounds.Projects.XY

variable {c : ℕ}

/-- The multiset of pairwise sums: each pair `(x, y) ∈ X × Y` contributes one
entry `x + y`, so entries repeat exactly when different pairs have equal sums. -/
def pairSums (X Y : Finset ℕ) : Multiset ℕ :=
  X.val.bind fun x => Y.val.map fun y => x + y

theorem pairSums_mem {X Y : Finset ℕ} {a : ℕ} :
    a ∈ pairSums X Y ↔ ∃ x ∈ X, ∃ y ∈ Y, x + y = a := by
  simp [pairSums]

/-- The multiset of pairwise sums has exactly `X.card * Y.card` entries. -/
theorem pairSums_card (X Y : Finset ℕ) : (pairSums X Y).card = X.card * Y.card := by
  simp [pairSums, Multiset.card_bind]

/-- **Number of distinct sums.**  Collapsing multiplicities can only lose
entries, so there are at most `X.card * Y.card` distinct pairwise sums. -/
theorem pairSums_card_le (X Y : Finset ℕ) :
    (pairSums X Y).toFinset.card ≤ X.card * Y.card :=
  (Multiset.toFinset_card_le _).trans (le_of_eq (pairSums_card X Y))

/-- **Bits per probe, `b = 2`.**  A set of pairwise non-prefix transcripts of at
most `c` binary tests has at most `2 ^ c` elements: `c` comparisons carry at most
`c` bits, so they separate at most `2 ^ c` distinct inputs.  This is
`Core.Branching.card_le_pow_of_prefixFree` at `b = 2`. -/
theorem transcripts_card_le_pow_two (P : Finset (List (Fin 2)))
    (hpre : ∀ p ∈ P, ∀ q ∈ P, p <+: q → p = q) (hlen : ∀ p ∈ P, p.length ≤ c) :
    P.card ≤ 2 ^ c :=
  card_le_pow_of_prefixFree (b := 2) P hpre hlen

/-- **The generic `N`-item bound, re-indexed.**  Any comparison tree that sorts
*every* `N = X.card * Y.card`-element input with distinct values has
`Nat.factorial N ≤ 2 ^ depth`.  This is `Comparison.Tree.factorial_le_two_pow_depth`
at `N = X.card * Y.card`; it says nothing about sums specifically, because a
correct sorter for `X + Y` need only handle the (much fewer) orderings that sums
can actually realize. -/
theorem factorial_mul_card_le_two_pow_depth {X Y : Finset ℕ}
    (t : Tree (pairSums X Y).card) (h : Correct (α := ℕ) t) :
    Nat.factorial (X.card * Y.card) ≤ 2 ^ depth t := by
  rw [← pairSums_card]
  exact factorial_le_two_pow_depth h

/-- The logarithmic form of `factorial_mul_card_le_two_pow_depth`: a tree that
sorts all `N = n·m` distinct-valued inputs needs `≥ log₂((n·m)!)` comparisons.
Again a statement about the generic problem, not about `X + Y`. -/
theorem log2_factorial_mul_card_le_depth {X Y : Finset ℕ}
    (t : Tree (pairSums X Y).card) (h : Correct (α := ℕ) t) :
    Real.logb 2 (Nat.factorial (X.card * Y.card) : ℝ) ≤ (depth t : ℝ) :=
  logb_le_of_le_pow (b := 2) (c := depth t) (by norm_num) (Nat.factorial_pos _)
    (factorial_mul_card_le_two_pow_depth t h)

end SortBounds.Projects.XY
