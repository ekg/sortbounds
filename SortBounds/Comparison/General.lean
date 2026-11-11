/-
SortBounds/General.lean

The lower bound for value types other than `ℕ`.

`Tree.run`/`Tree.cost` depend only on the *comparison pattern* of the input
(`run_eq_of_pattern`, `cost_eq_of_pattern`), so a comparison sort behaves the
same on `α`-valued inputs as on the corresponding `ℕ`-valued ones.  Hence the
`Ω(n log n)` bound transfers from `ℕ` to any linear order containing `n` values
in increasing order — `ℚ`, `ℝ`, `ℤ`, lexicographically ordered strings, or any
type with at least `n` elements (`exists_input_cost_ge_of_finset`).
-/
import SortBounds.Comparison.WorstCase
import SortBounds.Comparison.Stirling

namespace SortBounds

open Finset

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- The number of input values strictly below `x i`, as an element of `Fin n`. -/
def rank (x : Fin n → α) (i : Fin n) : Fin n :=
  ⟨(univ.filter fun j => x j < x i).card, by
    have hsub : (univ.filter fun j => x j < x i) ⊆ univ.erase i := by
      intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk
      simp only [mem_erase, mem_univ, and_true]
      rintro rfl
      exact lt_irrefl _ hk
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin] at hcard
    have := i.isLt
    omega⟩

theorem rank_val (x : Fin n → α) (i : Fin n) :
    (rank x i : ℕ) = (univ.filter fun j => x j < x i).card := rfl

/-- `rank` is strictly monotone in the value. -/
theorem rank_lt_rank {x : Fin n → α} {i j : Fin n} (h : x i < x j) : rank x i < rank x j := by
  rw [Fin.lt_def, rank_val, rank_val]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact lt_trans hk h
  · intro heq
    have hmem : i ∈ univ.filter (fun k => x k < x i) := by
      rw [heq]
      simp only [mem_filter, mem_univ, true_and]
      exact h
    simp only [mem_filter, mem_univ, true_and] at hmem
    exact lt_irrefl _ hmem

theorem rank_injective {x : Fin n → α} (hx : Function.Injective x) :
    Function.Injective (rank x) := by
  intro i j hij
  rcases lt_trichotomy (x i) (x j) with h | h | h
  · exact absurd hij (ne_of_lt (rank_lt_rank h))
  · exact hx h
  · exact absurd hij.symm (ne_of_lt (rank_lt_rank h))

/-- `rank` as a bijection of `Fin n` (injective endomaps of a finite type are bijective). -/
noncomputable def rankEquiv (x : Fin n → α) (hx : Function.Injective x) : Fin n ≃ Fin n :=
  Equiv.ofBijective (rank x) ⟨rank_injective hx,
    Finite.injective_iff_surjective.1 (rank_injective hx)⟩

/-- The ranking permutation of an injective input: `rankPerm x k` is the position
of the `k`-th smallest value of `x`. -/
noncomputable def rankPerm (x : Fin n → α) (hx : Function.Injective x) : Equiv.Perm (Fin n) :=
  (rankEquiv x hx).symm

theorem rank_rankPerm {x : Fin n → α} (hx : Function.Injective x) (k : Fin n) :
    rank x (rankPerm x hx k) = k := by
  rw [rankPerm]
  change (rankEquiv x hx) ((rankEquiv x hx).symm k) = k
  exact Equiv.apply_symm_apply _ k

/-- `rankPerm` sorts `x`. -/
theorem sorts_rankPerm {x : Fin n → α} (hx : Function.Injective x) : Sorts x (rankPerm x hx) := by
  intro k l hkl
  have hk : rank x (rankPerm x hx k) < rank x (rankPerm x hx l) := by
    rw [rank_rankPerm hx, rank_rankPerm hx]; exact hkl
  rcases lt_trichotomy (x (rankPerm x hx k)) (x (rankPerm x hx l)) with h | h | h
  · exact h
  · rw [hx h] at hk
    exact absurd hk (lt_irrefl _)
  · exact absurd (rank_lt_rank h) (lt_asymm hk)

/-- The comparison pattern of `x` is the pattern of the canonical `ℕ`-valued
input indexed by its ranking permutation. -/
theorem pattern_rankPerm {x : Fin n → α} (hx : Function.Injective x) (i j : Fin n) :
    x i < x j ↔ xOfPerm (rankPerm x hx) i < xOfPerm (rankPerm x hx) j := by
  have hp : ∀ k, xOfPerm (rankPerm x hx) k = (rank x k : ℕ) := fun k => rfl
  rw [hp i, hp j, rank_val, rank_val]
  constructor
  · intro h
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩
    · intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk ⊢
      exact lt_trans hk h
    · intro heq
      have hmem : i ∈ univ.filter (fun k => x k < x i) := by
        rw [heq]
        simp only [mem_filter, mem_univ, true_and]
        exact h
      simp only [mem_filter, mem_univ, true_and] at hmem
      exact lt_irrefl _ hmem
  · intro h
    rcases lt_trichotomy (x i) (x j) with h' | h' | h'
    · exact h'
    · rw [h'] at h
      exact absurd h (lt_irrefl _)
    · exact absurd (rank_lt_rank h') (lt_asymm h)

/-- **Correctness of a comparison sort depends only on the value type up to the
comparison pattern**: if `t` sorts all inputs of `α`, it sorts all inputs of `ℕ`. -/
theorem correct_of_orderEmb (a : Fin n ↪o α) {t : Tree n} (h : Correct (α := α) t) :
    Correct (α := ℕ) t := by
  intro x hx
  classical
  set p := rankPerm x hx with hp
  set y : Fin n → α := fun i => a (p.symm i) with hy_def
  have hy : Function.Injective y := a.injective.comp p.symm.injective
  -- `y` is sorted along `p`, so the tree must output `p` on `y`
  have h1 : Sorts y (run t y) := h y hy
  have h2 : Sorts y p := by
    intro k l hkl
    show a (p.symm (p k)) < a (p.symm (p l))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact a.strictMono hkl
  have hrun : run t y = p := Sorts.unique hy h1 h2
  -- `x` and `y` have the same comparison pattern, so the same output
  have hpat : ∀ i j, x i < x j ↔ y i < y j := by
    intro i j
    have h3 : x i < x j ↔ xOfPerm p i < xOfPerm p j := pattern_rankPerm hx i j
    have h4 : xOfPerm p i < xOfPerm p j ↔ y i < y j := by
      show ((p.symm i : Fin n) : ℕ) < ((p.symm j : Fin n) : ℕ) ↔ a (p.symm i) < a (p.symm j)
      exact (a.strictMono.lt_iff_lt).symm
    exact h3.trans h4
  rw [show run t x = run t y from run_eq_of_pattern t hpat, hrun]
  exact sorts_rankPerm hx

/-- **The `Ω(n log n)` bound for any value type**: on a linear order containing
`n` values in increasing order, some injective input needs at least `log₂(n!)`
comparisons. -/
theorem exists_input_cost_ge_of_orderEmb (a : Fin n ↪o α) {t : Tree n}
    (h : Correct (α := α) t) :
    ∃ y : Fin n → α, Function.Injective y ∧
      Real.logb 2 (Nat.factorial n) ≤ (cost t y : ℝ) := by
  classical
  have hN : Correct (α := ℕ) t := correct_of_orderEmb a h
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (f := fun p : Equiv.Perm (Fin n) => cost t (xOfPerm p)) Finset.univ_nonempty
  refine ⟨fun i => a (p.symm i), a.injective.comp p.symm.injective, ?_⟩
  have hpat : ∀ i j, (fun i => a (p.symm i)) i < (fun i => a (p.symm i)) j ↔
      xOfPerm p i < xOfPerm p j := by
    intro i j
    show a (p.symm i) < a (p.symm j) ↔ ((p.symm i : Fin n) : ℕ) < ((p.symm j : Fin n) : ℕ)
    exact a.strictMono.lt_iff_lt
  rw [cost_eq_of_pattern t hpat, ← hp]
  exact logb_factorial_le_worstCase hN

/-- **`Ω(n log n)` for any value type** (with the explicit `n/4 · log₂ n` bound). -/
theorem exists_input_cost_ge_quarter_of_orderEmb (hn : 64 ≤ n) (a : Fin n ↪o α) {t : Tree n}
    (h : Correct (α := α) t) :
    ∃ y : Fin n → α, Function.Injective y ∧
      (n : ℝ) * Real.logb 2 n / 4 ≤ (cost t y : ℝ) := by
  obtain ⟨y, hy, hcost⟩ := exists_input_cost_ge_of_orderEmb a h
  exact ⟨y, hy, le_trans (logb_factorial_ge_quarter n hn) hcost⟩

/-- Any type with at least `n` elements satisfies the hypothesis of
`exists_input_cost_ge_of_orderEmb`. -/
theorem exists_input_cost_ge_of_finset {s : Finset α} (hs : s.card = n) {t : Tree n}
    (h : Correct (α := α) t) :
    ∃ y : Fin n → α, Function.Injective y ∧
      Real.logb 2 (Nat.factorial n) ≤ (cost t y : ℝ) :=
  exists_input_cost_ge_of_orderEmb (s.orderEmbOfFin hs) h

end SortBounds
