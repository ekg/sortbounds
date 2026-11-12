/-
SortBounds/Projects/Repetitiveness/Grammar.lean

**M1, part 1: straight-line programs and their expansion.**

The model is the standard one — a grammar with `size` rules `0, …, size-1`, each rule being
either a terminal or the concatenation of *two strictly earlier* rules:

```lean
structure SLP (α : Type*) where
  size : ℕ
  rule : Fin size → α ⊕ (Fin size × Fin size)
  ref_lt : ∀ (i A B : Fin size), rule i = .inr (A, B) → A.val < i.val ∧ B.val < i.val
```

Requiring the children to have smaller *indices* is exactly acyclicity, with the
topological order built into the data (any acyclic SLP can be renumbered that way), and it
gives a well-founded recursion for the expansion without carrying an explicit rank.

`G.expands s` means: some rule of `G` expands to `s`.

The mathematical content of the file is `exists_straddle`: **a factor of length `k ≥ 2` of
an expansion straddles the concatenation point of some rule.**  Descend the derivation of
the factor: at a rule `i = A B` the window is either inside `A`, inside `B`, or straddles
the junction, and the first two cases recurse into a strictly earlier rule; a terminal rule
is a single character, where a window of length `≥ 2` cannot fit.  This is what makes the
"at most `k · g` factors" count possible: a `k`-window straddling the junction of rule `X`
starts at an offset `d ∈ [1, k-1]` *before* that junction, so it is one of `k` words
attached to `X` — `slpWindow G k X d` — and there is one junction per rule.
-/
import Mathlib
import SortBounds.Projects.Repetitiveness.Basic

namespace SortBounds.Projects.Repetitiveness

/-- A straight-line program over `α`: `size` rules, each a terminal or the concatenation of
two earlier rules.  `size` is the number of rules, the SLP measure `g`. -/
structure SLP (α : Type*) where
  /-- The number of rules. -/
  size : ℕ
  /-- Rule `i`: a terminal, or the concatenation of two earlier rules. -/
  rule : Fin size → α ⊕ (Fin size × Fin size)
  /-- Acyclicity: the two children of a concatenation have strictly smaller indices. -/
  ref_lt : ∀ (i A B : Fin size), rule i = .inr (A, B) → A.val < i.val ∧ B.val < i.val

namespace SLP

variable {α : Type*}

/-- The string a rule expands to. -/
noncomputable def expand (G : SLP α) : Fin G.size → List α :=
  WellFounded.fix (InvImage.wf Fin.val Nat.lt_wfRel.wf) (fun i rec =>
    match h : G.rule i with
    | .inl a => [a]
    | .inr (A, B) => rec A (G.ref_lt i A B h).1 ++ rec B (G.ref_lt i A B h).2)

/-- **`G` expands `s`**: some rule of `G` derives exactly `s`.  Naming the root
existentially loses nothing for the counting lemma, which bounds by `size` (the number of
rules) rather than by anything about which rule is the start rule. -/
def expands (G : SLP α) (s : List α) : Prop := ∃ root : Fin G.size, G.expand root = s

@[simp]
theorem expand_of_term {G : SLP α} {i : Fin G.size} {a : α} (h : G.rule i = .inl a) :
    G.expand i = [a] := by
  rw [expand, WellFounded.fix_eq]
  split
  case h_1 a' heq =>
    rw [h] at heq
    obtain rfl := Sum.inl.inj heq
    rfl
  case h_2 A' B' heq =>
    rw [h] at heq
    exact absurd heq (by simp)

theorem expand_of_concat {G : SLP α} {i A B : Fin G.size} (h : G.rule i = .inr (A, B)) :
    G.expand i = G.expand A ++ G.expand B := by
  rw [expand, WellFounded.fix_eq]
  split
  case h_1 a heq =>
    rw [h] at heq
    exact absurd heq (by simp)
  case h_2 A' B' heq =>
    rw [h] at heq
    obtain ⟨rfl, rfl⟩ := Sum.inr.inj heq
    rfl

/-- **Every character of an expansion is a terminal of some rule.**  (Used for the `k = 1`
count, where a length-1 factor can be anywhere but the number of distinct characters is at
most the number of rules.) -/
theorem exists_term_of_mem (G : SLP α) :
    ∀ (i : Fin G.size) {a : α}, a ∈ G.expand i → ∃ j : Fin G.size, G.rule j = .inl a := by
  refine WellFounded.fix (InvImage.wf Fin.val Nat.lt_wfRel.wf)
    (C := fun i => ∀ {a : α}, a ∈ G.expand i → ∃ j : Fin G.size, G.rule j = .inl a) ?_
  intro i ih a ha
  match hrule : G.rule i with
  | Sum.inl a' =>
    rw [expand_of_term hrule] at ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact ⟨i, hrule⟩
  | Sum.inr pr =>
    obtain ⟨A, B⟩ := pr
    rw [expand_of_concat hrule, List.mem_append] at ha
    rcases ha with ha | ha
    · exact ih A (G.ref_lt i A B hrule).1 ha
    · exact ih B (G.ref_lt i A B hrule).2 ha

/-- The candidate word attached to a rule and an offset: the length-`k` window of `X`'s
expansion whose start lies `d` positions *before* the concatenation point of `X` (i.e. it
starts inside the first child and, for `d < k`, crosses into the second).  Only
concatenation rules give a meaningful candidate; for a terminal rule the value is junk
(`[]`) and never used. -/
noncomputable def slpWindow (G : SLP α) (k : ℕ) (X : Fin G.size) (d : ℕ) : List α :=
  match G.rule X with
  | .inl _ => []
  | .inr (A, _) => (G.expand X).drop ((G.expand A).length - d) |>.take k

theorem slpWindow_of_concat {G : SLP α} {X A B : Fin G.size} (h : G.rule X = .inr (A, B))
    (k d : ℕ) :
    slpWindow G k X d = List.take k (List.drop ((G.expand A).length - d) (G.expand X)) := by
  simp [slpWindow, h]

/-- **A length-`k` window (`k ≥ 2`) of an expansion straddles some concatenation point.**
The witness rule `X` is a concatenation rule, the window starts `d ∈ [1, k-1]` positions
before `X`'s concatenation point, and the same length-`k` window already occurs inside
`X`'s own expansion, at that offset. -/
theorem exists_straddle (G : SLP α) :
    ∀ (i : Fin G.size) (p k : ℕ), p + k ≤ (G.expand i).length → 2 ≤ k →
      ∃ (X A B : Fin G.size) (_ : G.rule X = .inr (A, B)) (d : ℕ),
        1 ≤ d ∧ d < k ∧
          List.take k (List.drop ((G.expand A).length - d) (G.expand X))
            = List.take k (List.drop p (G.expand i)) := by
  refine WellFounded.fix (InvImage.wf Fin.val Nat.lt_wfRel.wf)
    (C := fun i => ∀ (p k : ℕ), p + k ≤ (G.expand i).length → 2 ≤ k →
      ∃ (X A B : Fin G.size) (_ : G.rule X = .inr (A, B)) (d : ℕ),
        1 ≤ d ∧ d < k ∧
          List.take k (List.drop ((G.expand A).length - d) (G.expand X))
            = List.take k (List.drop p (G.expand i))) ?_
  intro i ih p k hpk hk
  match hrule : G.rule i with
  | Sum.inl a =>
    -- a terminal expands to one character, so a window of length `≥ 2` does not fit
    rw [expand_of_term hrule] at hpk
    simp only [List.length_singleton] at hpk
    omega
  | Sum.inr pr =>
    obtain ⟨A, B⟩ := pr
    have hAB : G.expand i = G.expand A ++ G.expand B := expand_of_concat hrule
    have hlt := G.ref_lt i A B hrule
    by_cases h1 : p + k ≤ (G.expand A).length
    · -- the window sits inside the left child: recurse there
      obtain ⟨X, A', B', hX, d, hd, hdk, heq⟩ := ih A hlt.1 p k h1 hk
      refine ⟨X, A', B', hX, d, hd, hdk, ?_⟩
      rw [heq, hAB, List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
    · by_cases h2 : (G.expand A).length ≤ p
      · -- the window sits inside the right child: recurse there, at a shifted offset
        have hB : p - (G.expand A).length + k ≤ (G.expand B).length := by
          rw [hAB, List.length_append] at hpk
          omega
        obtain ⟨X, A', B', hX, d, hd, hdk, heq⟩ :=
          ih B hlt.2 (p - (G.expand A).length) k hB hk
        refine ⟨X, A', B', hX, d, hd, hdk, ?_⟩
        rw [heq, hAB, List.drop_append, List.drop_eq_nil_iff.mpr h2, List.nil_append]
      · -- the window straddles the junction of this very rule
        have hpk' : (G.expand A).length < p + k := by omega
        refine ⟨i, A, B, hrule, (G.expand A).length - p, by omega, by omega, ?_⟩
        have harith : (G.expand A).length - ((G.expand A).length - p) = p := by omega
        rw [harith]

end SLP

end SortBounds.Projects.Repetitiveness
