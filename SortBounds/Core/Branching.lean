/-
SortBounds/Core/Branching.lean

The reusable heart of every lower bound in this repository: **bits per probe**.

An algorithm that decides among `N` outcomes by a sequence of steps, where each
step has at most `b` possible results, needs at least `log_b N` steps — provided
distinct outcomes are separated by distinct transcripts.  The comparison-sorting
bound is the case `b = 2`; radix sorting uses `b` buckets per pass, an algebraic
decision tree uses the three signs, a word-RAM read of a `w`-bit word has
`b = 2 ^ w`, and so on.  This file contains only the combinatorial content, with
no reference to sorting:

> a prefix-free set of words over an alphabet of size `b`, all of length at most
> `c`, has at most `b ^ c` elements.

Recipe for using it: exhibit a map from inputs to `List (Fin b)` (the transcript
of the algorithm's steps on that input) that is injective on the inputs whose
transcripts are pairwise non-prefix (i.e. on inputs the algorithm
*distinguishes*), with `length = cost`.  Then `#inputs ≤ b ^ cost`, and
`log_b #inputs ≤ cost`.  `SortBounds.Comparison.Aggregate` is the `b = 2`
instance for comparison trees, with the transcripts read off the tree.
-/
import Mathlib

namespace SortBounds

variable {b c : ℕ} [NeZero b]

/-- The word `p` padded with `0`s to length `c`.  Used to encode a prefix-free set
of short words as a subset of all `c`-letter words. -/
def padTo (c : ℕ) (p : List (Fin b)) : Fin c → Fin b :=
  fun i => if h : (i : ℕ) < p.length then p.get ⟨i, h⟩ else 0

theorem padTo_apply_lt {p : List (Fin b)} {i : Fin c} (h : (i : ℕ) < p.length) :
    padTo c p i = p.get ⟨i, h⟩ := dite_eq_left h

theorem padTo_apply_ge {p : List (Fin b)} {i : Fin c} (h : p.length ≤ (i : ℕ)) :
    padTo c p i = 0 := dite_eq_right (Nat.not_lt.mpr h)

/-- Padding to a common length is injective on prefix-free sets of short words. -/
theorem padTo_injOn_of_prefixFree (P : Finset (List (Fin b)))
    (hpre : ∀ p ∈ P, ∀ q ∈ P, p <+: q → p = q)
    (hlen : ∀ p ∈ P, p.length ≤ c) : Set.InjOn (padTo c) (P : Set (List (Fin b))) := by
  intro p hp q hq heq
  have hp' : p.length ≤ c := hlen p hp
  have hq' : q.length ≤ c := hlen q hq
  rcases le_total p.length q.length with hle | hle
  · -- `p` is a prefix of `q`: compare letters position by position
    have hget : ∀ n, n < p.length → p[n]? = q[n]? := by
      intro n hn
      have hn' : n < q.length := lt_of_lt_of_le hn hle
      have h1 := congrFun heq ⟨n, lt_of_lt_of_le hn hp'⟩
      rw [padTo_apply_lt (p := p) hn, padTo_apply_lt (p := q) hn'] at h1
      rw [List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hn']
      simpa using h1
    have htake : p = q.take p.length := by
      apply List.ext_getElem?
      intro n
      rw [List.getElem?_take]
      by_cases hn : n < p.length
      · simp only [hn, ite_true]; exact hget n hn
      · have hnone : p[n]? = none := List.getElem?_eq_none (by omega)
        simp only [hn, ite_false, hnone]
    refine hpre p hp q hq ⟨q.drop p.length, ?_⟩
    rw [htake, List.length_take, Nat.min_eq_left hle, List.take_append_drop]
  · -- symmetric
    have hget : ∀ n, n < q.length → q[n]? = p[n]? := by
      intro n hn
      have hn' : n < p.length := lt_of_lt_of_le hn hle
      have h1 := congrFun heq ⟨n, lt_of_lt_of_le hn hq'⟩
      rw [padTo_apply_lt (p := q) hn, padTo_apply_lt (p := p) hn'] at h1
      rw [List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hn']
      simpa using h1.symm
    have htake : q = p.take q.length := by
      apply List.ext_getElem?
      intro n
      rw [List.getElem?_take]
      by_cases hn : n < q.length
      · simp only [hn, ite_true]; exact hget n hn
      · have hnone : q[n]? = none := List.getElem?_eq_none (by omega)
        simp only [hn, ite_false, hnone]
    refine (hpre q hq p hp ⟨p.drop q.length, ?_⟩).symm
    rw [htake, List.length_take, Nat.min_eq_left hle, List.take_append_drop]

/-- **Bits per probe, counting form.**  A prefix-free set of words over an
alphabet of size `b`, each of length at most `c`, has at most `b ^ c` elements. -/
theorem card_le_pow_of_prefixFree (P : Finset (List (Fin b)))
    (hpre : ∀ p ∈ P, ∀ q ∈ P, p <+: q → p = q)
    (hlen : ∀ p ∈ P, p.length ≤ c) : P.card ≤ b ^ c := by
  calc P.card = (P.image (padTo c)).card :=
        (Finset.card_image_of_injOn (padTo_injOn_of_prefixFree P hpre hlen)).symm
    _ ≤ (Finset.univ : Finset (Fin c → Fin b)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = b ^ c := by simp

omit [NeZero b] in
/-- **Bits per probe, logarithmic form.**  If `N ≤ b ^ c` and `1 < b`, then
`log_b N ≤ c`: `c` steps with `b` outcomes each carry at most `c · log₂ b` bits. -/
theorem logb_le_of_le_pow {N : ℕ} (hb : 1 < b) (hN : 0 < N) (h : N ≤ b ^ c) :
    Real.logb b N ≤ (c : ℝ) := by
  rw [Real.logb_le_iff_le_rpow (show (1 : ℝ) < (b : ℝ) by exact_mod_cast hb)
    (by exact_mod_cast hN)]
  calc (N : ℝ) ≤ (b : ℝ) ^ c := by exact_mod_cast h
    _ = (b : ℝ) ^ (c : ℝ) := by rw [Real.rpow_natCast]

end SortBounds
