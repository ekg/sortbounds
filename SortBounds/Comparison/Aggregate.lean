/-
SortBounds/Aggregate.lean

Two "counting" facts about the comparison model: for any set of inputs whose
computed leaves are pairwise distinct,

* at most `2^c` of them make at most `c` comparisons, and
* the weights `(1/2)^(number of comparisons)` sum to at most `1`.

Both are proved by a single structural induction on the decision tree (split the
input set by the answer at the root).  Consequences (`WorstCase.lean`,
`Average.lean`): some input makes at least `log₂(n!)` comparisons, and the
*expected* number of comparisons over a uniformly random ordering is at least
`log₂(n!)`.
-/
import SortBounds.Comparison.Tree

namespace SortBounds

open Finset

variable {n : ℕ}

theorem run_node (i j : Fin n) (l r : Tree n) (x : Fin n → ℕ) :
    run (Tree.node i j l r) x = if x i < x j then run l x else run r x := rfl

theorem cost_node (i j : Fin n) (l r : Tree n) (x : Fin n → ℕ) :
    cost (Tree.node i j l r) x = 1 + (if x i < x j then cost l x else cost r x) := rfl

/-- Injectivity hypothesis: distinct permutations in `S` are separated by the
leaves their canonical inputs reach.  A correct sorting tree satisfies this for
`S = univ` (`separated_of_correct`). -/
def Separated (t : Tree n) (S : Finset (Equiv.Perm (Fin n))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, run t (xOfPerm p) = run t (xOfPerm q) → p = q

theorem separated_of_correct {t : Tree n} (h : Correct (α := ℕ) t) :
    Separated t Finset.univ := by
  intro p _ q _ heq
  have hp : run t (xOfPerm p) = p :=
    Sorts.unique (xOfPerm_injective p) (h (xOfPerm p) (xOfPerm_injective p)) (xOfPerm_sorts p)
  have hq : run t (xOfPerm q) = q :=
    Sorts.unique (xOfPerm_injective q) (h (xOfPerm q) (xOfPerm_injective q)) (xOfPerm_sorts q)
  rw [hp, hq] at heq
  exact heq

theorem separated_mono {t : Tree n} {S S' : Finset (Equiv.Perm (Fin n))} (h : Separated t S)
    (hsub : S' ⊆ S) : Separated t S' :=
  fun p hp q hq => h p (hsub hp) q (hsub hq)

/-- **`2^c` bound.**  Among inputs whose computed leaves are distinct, at most
`2^c` make at most `c` comparisons. -/
theorem card_le_pow_of_cost_le (t : Tree n) (S : Finset (Equiv.Perm (Fin n))) (c : ℕ)
    (hsep : Separated t S) (hcost : ∀ p ∈ S, cost t (xOfPerm p) ≤ c) :
    S.card ≤ 2 ^ c := by
  induction t generalizing S c with
  | leaf σ =>
    have h1 : S.card ≤ 1 := by
      apply Finset.card_le_one.2
      intro p hp q hq
      exact hsep p hp q hq rfl
    exact le_trans h1 (Nat.one_le_two_pow)
  | node i j l r ihl ihr =>
    classical
    set S₁ := S.filter (fun p => xOfPerm p i < xOfPerm p j) with hS₁
    set S₂ := S.filter (fun p => ¬ xOfPerm p i < xOfPerm p j) with hS₂
    have hcard : S.card = S₁.card + S₂.card := by
      rw [hS₁, hS₂, ← Finset.card_filter_add_card_filter_not (s := S)
        (p := fun p => xOfPerm p i < xOfPerm p j)]
    rcases c with _ | c
    · -- no input fits in zero comparisons below an internal node
      have hzero : S.card = 0 := by
        by_contra hne
        obtain ⟨p, hp⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
        have := hcost p hp
        rw [cost_node] at this
        have : 1 ≤ cost (Tree.node i j l r) (xOfPerm p) := by
          rw [cost_node]; omega
        omega
      rw [hzero]; exact Nat.zero_le _
    · have hsep₁ : Separated l S₁ := by
        intro p hp q hq he
        have h1 : xOfPerm p i < xOfPerm p j := (Finset.mem_filter.1 hp).2
        have h2 : xOfPerm q i < xOfPerm q j := (Finset.mem_filter.1 hq).2
        refine hsep p (Finset.filter_subset _ _ hp) q (Finset.filter_subset _ _ hq) ?_
        rw [run_node, ite_eq_left h1, run_node, ite_eq_left h2, he]
      have hsep₂ : Separated r S₂ := by
        intro p hp q hq he
        have h1 : ¬ xOfPerm p i < xOfPerm p j := (Finset.mem_filter.1 hp).2
        have h2 : ¬ xOfPerm q i < xOfPerm q j := (Finset.mem_filter.1 hq).2
        refine hsep p (Finset.filter_subset _ _ hp) q (Finset.filter_subset _ _ hq) ?_
        rw [run_node, ite_eq_right h1, run_node, ite_eq_right h2, he]
      have h₁ : S₁.card ≤ 2 ^ c := by
        refine ihl S₁ c hsep₁ ?_
        intro p hp
        have hmem : p ∈ S := Finset.filter_subset _ _ hp
        have hlt : xOfPerm p i < xOfPerm p j := (Finset.mem_filter.1 hp).2
        have hc := hcost p hmem
        rw [cost_node, ite_eq_left hlt] at hc
        omega
      have h₂ : S₂.card ≤ 2 ^ c := by
        refine ihr S₂ c hsep₂ ?_
        intro p hp
        have hmem : p ∈ S := Finset.filter_subset _ _ hp
        have hlt : ¬ xOfPerm p i < xOfPerm p j := (Finset.mem_filter.1 hp).2
        have hc := hcost p hmem
        rw [cost_node, ite_eq_right hlt] at hc
        omega
      rw [hcard]
      calc S₁.card + S₂.card ≤ 2 ^ c + 2 ^ c := Nat.add_le_add h₁ h₂
        _ = 2 ^ (c + 1) := by ring

/-- **Weight bound.**  For inputs whose computed leaves are pairwise distinct,
the weights `(1/2)^(number of comparisons)` sum to at most `1`. -/
theorem sum_pow_cost_le_one (t : Tree n) (S : Finset (Equiv.Perm (Fin n)))
    (hsep : Separated t S) :
    ∑ p ∈ S, (1 / 2 : ℝ) ^ cost t (xOfPerm p) ≤ 1 := by
  induction t generalizing S with
  | leaf σ =>
    have h1 : S.card ≤ 1 := by
      apply Finset.card_le_one.2
      intro p hp q hq
      exact hsep p hp q hq rfl
    have : ∑ p ∈ S, (1 / 2 : ℝ) ^ cost (Tree.leaf σ) (xOfPerm p) = S.card := by
      simp [cost]
    rw [this]
    have : (S.card : ℝ) ≤ 1 := by exact_mod_cast h1
    simpa using this
  | node i j l r ihl ihr =>
    classical
    set S₁ := S.filter (fun p => xOfPerm p i < xOfPerm p j) with hS₁
    set S₂ := S.filter (fun p => ¬ xOfPerm p i < xOfPerm p j) with hS₂
    have hsplit : ∑ p ∈ S, (1 / 2 : ℝ) ^ cost (Tree.node i j l r) (xOfPerm p)
        = ∑ p ∈ S₁, (1 / 2 : ℝ) ^ cost (Tree.node i j l r) (xOfPerm p)
        + ∑ p ∈ S₂, (1 / 2 : ℝ) ^ cost (Tree.node i j l r) (xOfPerm p) := by
      rw [hS₁, hS₂, Finset.sum_filter_add_sum_filter_not (s := S)
        (p := fun p => xOfPerm p i < xOfPerm p j)]
    have h₁ : ∑ p ∈ S₁, (1 / 2 : ℝ) ^ cost (Tree.node i j l r) (xOfPerm p) ≤ 1 / 2 := by
      have : ∀ p ∈ S₁, (1 / 2 : ℝ) ^ cost (Tree.node i j l r) (xOfPerm p)
          = (1 / 2) * (1 / 2 : ℝ) ^ cost l (xOfPerm p) := by
        intro p hp
        have hlt : xOfPerm p i < xOfPerm p j := (Finset.mem_filter.1 hp).2
        rw [cost_node, ite_eq_left hlt, pow_add]
        norm_num
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
      have hsep₁ : Separated l S₁ := by
        intro p hp q hq he
        have h1 : xOfPerm p i < xOfPerm p j := (Finset.mem_filter.1 hp).2
        have h2 : xOfPerm q i < xOfPerm q j := (Finset.mem_filter.1 hq).2
        refine hsep p (Finset.filter_subset _ _ hp) q (Finset.filter_subset _ _ hq) ?_
        rw [run_node, ite_eq_left h1, run_node, ite_eq_left h2, he]
      have := ihl S₁ hsep₁
      nlinarith
    have h₂ : ∑ p ∈ S₂, (1 / 2 : ℝ) ^ cost (Tree.node i j l r) (xOfPerm p) ≤ 1 / 2 := by
      have : ∀ p ∈ S₂, (1 / 2 : ℝ) ^ cost (Tree.node i j l r) (xOfPerm p)
          = (1 / 2) * (1 / 2 : ℝ) ^ cost r (xOfPerm p) := by
        intro p hp
        have hlt : ¬ xOfPerm p i < xOfPerm p j := (Finset.mem_filter.1 hp).2
        rw [cost_node, ite_eq_right hlt, pow_add]
        norm_num
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
      have hsep₂ : Separated r S₂ := by
        intro p hp q hq he
        have h1 : ¬ xOfPerm p i < xOfPerm p j := (Finset.mem_filter.1 hp).2
        have h2 : ¬ xOfPerm q i < xOfPerm q j := (Finset.mem_filter.1 hq).2
        refine hsep p (Finset.filter_subset _ _ hp) q (Finset.filter_subset _ _ hq) ?_
        rw [run_node, ite_eq_right h1, run_node, ite_eq_right h2, he]
      have := ihr S₂ hsep₂
      nlinarith
    rw [hsplit]
    linarith

end SortBounds
