/-
SortBounds/Projects/Repetitiveness/Count.lean

**M1, part 2: `d_k ≤ k · g` for a straight-line program of `g` rules.**

A length-`k` factor of `s = G.expand root`, with `k ≥ 2`, straddles the concatenation point
of some rule (`SLP.exists_straddle`).  The window is then determined by the rule and by the
offset `d ∈ [1, k-1]` of its start before that concatenation point — the word is one of the
`k` candidates `slpWindow G k X d` attached to `X`.  With one concatenation point per rule,
`d_k ≤ k · size`.

`k = 1` is genuinely separate: a single character does not straddle anything, and the count
is instead "one candidate per rule's expansion, truncated to length `1`"
(`SLP.exists_term_of_mem`), giving `d_1 ≤ size`.

**Side condition.**  As in M0, the statement needs `1 ≤ k` and is false at `k = 0` (the
empty word is a factor, but `0 · size = 0`).  No upper bound is needed.

The counting is again packaged as a containment in an explicit `Finset.image` of the
candidate set `Fin size × Fin k`, so `Finset.card_image_le` does the work and no injectivity
of a choice function is needed.
-/
import Mathlib
import SortBounds.Projects.Repetitiveness.Basic
import SortBounds.Projects.Repetitiveness.Attractor
import SortBounds.Projects.Repetitiveness.Grammar

namespace SortBounds.Projects.Repetitiveness

variable {α : Type*} [DecidableEq α]

/-- **`d_1 ≤ g`**: every character of `s` is a terminal of some rule, so there are at most
`size` distinct characters. -/
theorem distinctFactors_one_card_le_slp {s : List α} (G : SLP α) (hG : G.expands s) :
    (distinctFactors s 1).card ≤ G.size := by
  obtain ⟨root, hroot⟩ := hG
  obtain rfl : s = G.expand root := hroot.symm
  have hsub : distinctFactors (G.expand root) 1 ⊆
      (Finset.univ : Finset (Fin G.size)).image (fun j => (G.expand j).take 1) := by
    intro f hf
    obtain ⟨i, hik, hf'⟩ := mem_distinctFactors.mp hf
    have hi : i < (G.expand root).length := by omega
    obtain ⟨j, hj⟩ := SLP.exists_term_of_mem G root (List.getElem_mem hi)
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩
    have hexp : G.expand j = [(G.expand root)[i]] := SLP.expand_of_term hj
    rw [hexp, ← hf', List.take_one_drop_eq_of_lt_length hi]
    rfl
  calc (distinctFactors (G.expand root) 1).card
      ≤ ((Finset.univ : Finset (Fin G.size)).image (fun j => (G.expand j).take 1)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin G.size)).card := Finset.card_image_le
    _ = G.size := by simp

/-- **The SLP counting lemma.**  A grammar of `size` rules has at most `k · size` distinct
factors of length `k`: a length-`k` factor is one of the `k` candidates attached to one of
the `size` rules. -/
theorem distinctFactors_card_le_mul_slp {s : List α} (G : SLP α) (hG : G.expands s) (k : ℕ)
    (hk : 1 ≤ k) : (distinctFactors s k).card ≤ k * G.size := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · -- `k = 1`: one candidate per rule
    have hk1' : k = 1 := by omega
    subst hk1'
    have h := distinctFactors_one_card_le_slp G hG
    simpa using h
  · -- `k ≥ 2`: one candidate per (rule, offset)
    classical
    obtain ⟨root, hroot⟩ := hG
    have hsub : distinctFactors s k ⊆
        (Finset.univ : Finset (Fin G.size × Fin k)).image
          (fun x => SLP.slpWindow G k x.1 x.2.val) := by
      intro f hf
      obtain ⟨i, hik, hf'⟩ := mem_distinctFactors.mp hf
      obtain ⟨X, A, B, hX, d, -, hdk, heq⟩ :=
        SLP.exists_straddle G root i k (by rw [hroot]; exact hik) hk2
      refine Finset.mem_image.mpr ⟨(X, ⟨d, hdk⟩), Finset.mem_univ _, ?_⟩
      rw [SLP.slpWindow_of_concat hX k d, heq, hroot, ← hf']
    calc (distinctFactors s k).card
        ≤ ((Finset.univ : Finset (Fin G.size × Fin k)).image
            (fun x => SLP.slpWindow G k x.1 x.2.val)).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin G.size × Fin k)).card := Finset.card_image_le
      _ = G.size * k := by simp
      _ = k * G.size := Nat.mul_comm _ _

/-- `d_k / k ≤ g`, the literal form of KNP's `d_k(S)/k ≤ γ` for a grammar of size `g`. -/
theorem dk_div_le_slp {s : List α} (G : SLP α) (hG : G.expands s) {k : ℕ} (hk : 1 ≤ k) :
    (distinctFactors s k).card / k ≤ G.size :=
  Nat.div_le_of_le_mul (distinctFactors_card_le_mul_slp G hG k hk)

/-- **`δ ≤ g`**: the substring complexity of `s` is at most the size of any grammar for `s`. -/
theorem substringComplexity_le_slp {s : List α} (G : SLP α) (hG : G.expands s) :
    substringComplexity s ≤ G.size := by
  refine Finset.sup_le ?_
  intro k hk
  obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hk
  exact dk_div_le_slp G hG h1

/-! ### A concrete grammar, as a sanity check on `expands` and the count -/

/-- The `ababa` grammar: `0 = a`, `1 = b`, `2 = ab`, `3 = abab`, `4 = ababa`, so `size = 5`
(and `ababa` itself has substring complexity `2`, so the grammar is far from optimal — the
point of the example is that `expands` is inhabited and the count applies). -/
def ababaSLP : SLP Char where
  size := 5
  rule := fun i =>
    match i.val with
    | 0 => .inl 'a'
    | 1 => .inl 'b'
    | 2 => .inr (⟨0, by decide⟩, ⟨1, by decide⟩)
    | 3 => .inr (⟨2, by decide⟩, ⟨2, by decide⟩)
    | _ => .inr (⟨3, by decide⟩, ⟨0, by decide⟩)
  ref_lt := by decide

/-! The expansion of each rule, computed from the unfolding lemmas (the kernel cannot
reduce `expand`, which is a well-founded recursion). -/

theorem ababaSLP_expand_zero : ∀ (h : 0 < ababaSLP.size), ababaSLP.expand ⟨0, h⟩ = ['a'] := fun h => by
  rw [SLP.expand_of_term (G := ababaSLP) (i := ⟨0, h⟩) (a := 'a')
    (by rfl : ababaSLP.rule ⟨0, h⟩ = .inl 'a')]

theorem ababaSLP_expand_one : ∀ (h : 1 < ababaSLP.size), ababaSLP.expand ⟨1, h⟩ = ['b'] := fun h => by
  rw [SLP.expand_of_term (G := ababaSLP) (i := ⟨1, h⟩) (a := 'b')
    (by rfl : ababaSLP.rule ⟨1, h⟩ = .inl 'b')]

theorem ababaSLP_expand_two : ∀ (h : 2 < ababaSLP.size), ababaSLP.expand ⟨2, h⟩ = ['a', 'b'] := fun h => by
  rw [SLP.expand_of_concat (G := ababaSLP) (i := ⟨2, h⟩) (A := ⟨0, by decide⟩)
    (B := ⟨1, by decide⟩) (by rfl : ababaSLP.rule ⟨2, h⟩ = .inr (⟨0, by decide⟩, ⟨1, by decide⟩))]
  rw [ababaSLP_expand_zero, ababaSLP_expand_one]
  rfl

theorem ababaSLP_expand_three : ∀ (h : 3 < ababaSLP.size), ababaSLP.expand ⟨3, h⟩ = ['a', 'b', 'a', 'b'] :=
  fun h => by
  rw [SLP.expand_of_concat (G := ababaSLP) (i := ⟨3, h⟩) (A := ⟨2, by decide⟩)
    (B := ⟨2, by decide⟩) (by rfl : ababaSLP.rule ⟨3, h⟩ = .inr (⟨2, by decide⟩, ⟨2, by decide⟩))]
  rw [ababaSLP_expand_two]
  rfl

theorem ababaSLP_expand_four :
    ∀ (h : 4 < ababaSLP.size), ababaSLP.expand ⟨4, h⟩ = ['a', 'b', 'a', 'b', 'a'] := fun h => by
  rw [SLP.expand_of_concat (G := ababaSLP) (i := ⟨4, h⟩) (A := ⟨3, by decide⟩)
    (B := ⟨0, by decide⟩) (by rfl : ababaSLP.rule ⟨4, h⟩ = .inr (⟨3, by decide⟩, ⟨0, by decide⟩))]
  rw [ababaSLP_expand_three, ababaSLP_expand_zero]
  rfl

/-- `ababaSLP` really is a grammar for `ababa`. -/
theorem ababaSLP_expands : ababaSLP.expands ababa :=
  ⟨⟨4, by decide⟩, ababaSLP_expand_four _⟩

/-- The bound at `k = 3` for the concrete grammar: `d_3 = 2 ≤ 15`. -/
example : (distinctFactors ababa 3).card ≤ 3 * ababaSLP.size :=
  distinctFactors_card_le_mul_slp ababaSLP ababaSLP_expands 3 (by norm_num)

/-- The `k = 0` side condition is not removable for grammars either. -/
example : ¬ ((distinctFactors ababa 0).card ≤ 0 * ababaSLP.size) := by decide

/-- `δ ≤ g` for the example: `substringComplexity ababa = 2 ≤ 5`. -/
example : substringComplexity ababa ≤ ababaSLP.size :=
  substringComplexity_le_slp ababaSLP ababaSLP_expands

end SortBounds.Projects.Repetitiveness
