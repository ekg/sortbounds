/-
SortBounds/Projects/BestCase/Connected.lean

**The comparison graph of a correct sort is connected.**  This is the perturbation
argument: if the pairs compared on the path of `x` did not connect all of `Fin n`,
one could take a block `B` of positions closed under comparison (a union of
components of the comparison graph), push every element of `B` far above
everything else, and get an input `x'` that

* answers every question on the path exactly as `x` did (`run_eq_of_add_const`), so
  the tree reaches the same leaf `r`, and
* is still injective (`injective_add_of_two_values`), so `Correct` applies to it,

yet the relative order of two positions is reversed, and no single permutation can
sort both orders (`symm_lt_of_sorts` + `no_cross_pair`).  Hence no such block
exists.
-/
import SortBounds.Projects.BestCase.Compared

namespace SortBounds.Projects.BestCase

open SortBounds

variable {n : ℕ}

/-! ### Two orders cannot share one output permutation -/

/-- If `r` sorts the injective input `x`, then `r` lists the positions in
increasing order of `x`: `x a < x b` forces `a` before `b` in `r`. -/
theorem symm_lt_of_sorts {x : Fin n → ℕ} {r : Equiv.Perm (Fin n)} (h : Sorts x r) {a b : Fin n}
    (hab : x a < x b) : r.symm a < r.symm b := by
  have hiff := h.lt_iff_lt (a := r.symm a) (b := r.symm b)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hiff
  exact hiff.mp hab

/-! ### Perturbing a comparison-closed block of positions -/

/-- **Answers on the path are preserved by a block-constant perturbation.**  If
every pair the path compares lies inside `B` or outside `B`, and `c` is constant on
`B` and on its complement, then adding `c` to `x` changes no answer along the path,
so the tree reaches the same leaf as before. -/
theorem run_eq_of_add_const (t : Tree n) (x : Fin n → ℕ) (c : Fin n → ℕ) {B : Set (Fin n)}
    (hB : ∀ i j, s(i, j) ∈ comparedPairs t x → (i ∈ B ↔ j ∈ B))
    (hc : ∀ i j, (i ∈ B ↔ j ∈ B) → c i = c j) :
    run t x = run t fun i => x i + c i := by
  refine run_eq_of_agree t x (fun i => x i + c i) ?_
  intro i j hmem
  have hbij := hB i j hmem
  have hij := hc i j hbij
  rw [hij]
  omega

/-- If `c` takes only the two values `0` and a value `C` bigger than every `x i`,
then adding `c` keeps an injective input injective: positions carrying `C` end up
entirely above those carrying `0`. -/
theorem injective_add_of_two_values {x c : Fin n → ℕ} (hx : Function.Injective x) {C : ℕ}
    (hC : ∀ i, x i < C) (hc : ∀ i, c i = 0 ∨ c i = C) :
    Function.Injective fun i => x i + c i := by
  intro p q hpq
  change x p + c p = x q + c q at hpq
  rcases hc p with hp | hp <;> rcases hc q with hq | hq <;> rw [hp, hq] at hpq
  · exact hx (by omega)
  · exact absurd hpq (by have := hC p; omega)
  · exact absurd hpq (by have := hC q; omega)
  · exact hx (by omega)

/-- **A comparison-closed block cannot separate two positions whose values are in
increasing order.**  If `i` is in `B`, `j` outside it, and `x i < x j`, then
pushing `B` above everything yields an injective input `x'` with `x' j < x' i`
that reaches the same leaf — and that leaf cannot sort both. -/
theorem no_cross_pair {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) {B : Set (Fin n)}
    (hB : ∀ i j, s(i, j) ∈ comparedPairs t x → (i ∈ B ↔ j ∈ B))
    {i j : Fin n} (hi : i ∈ B) (hj : j ∉ B) (hlt : x i < x j) : False := by
  classical
  let C : ℕ := Finset.univ.sup x + 1
  let c : Fin n → ℕ := fun k => if k ∈ B then C else 0
  have hC : ∀ k, x k < C := by
    intro k
    have := Finset.le_sup (f := x) (Finset.mem_univ k)
    show x k < Finset.univ.sup x + 1
    omega
  have hcIn : ∀ k : Fin n, k ∈ B → c k = C := by
    intro k hk
    show ite (k ∈ B) C 0 = C
    rw [ite_eq_left hk]
  have hcOut : ∀ k : Fin n, k ∉ B → c k = 0 := by
    intro k hk
    show ite (k ∈ B) C 0 = 0
    rw [ite_eq_right hk]
  have hc : ∀ k, c k = 0 ∨ c k = C := by
    intro k
    by_cases hk : k ∈ B
    · exact Or.inr (hcIn k hk)
    · exact Or.inl (hcOut k hk)
  have hcc : ∀ p q : Fin n, (p ∈ B ↔ q ∈ B) → c p = c q := by
    intro p q hpq
    by_cases hp : p ∈ B
    · rw [hcIn p hp, hcIn q (hpq.mp hp)]
    · rw [hcOut p hp, hcOut q (fun hq => hp (hpq.mpr hq))]
  have hrun : run t x = run t (fun k => x k + c k) := run_eq_of_add_const t x c hB hcc
  have hinj : Function.Injective fun k => x k + c k := injective_add_of_two_values hx hC hc
  have hsort₁ : Sorts x (run t x) := h x hx
  have hsort₂ : Sorts (fun k => x k + c k) (run t x) := by
    rw [hrun]
    exact h (fun k => x k + c k) hinj
  have hlt' : (fun k => x k + c k) j < (fun k => x k + c k) i := by
    show x j + c j < x i + c i
    rw [hcOut j hj, hcIn i hi]
    have := hC j
    omega
  have h₁ := symm_lt_of_sorts hsort₁ hlt
  have h₂ := symm_lt_of_sorts hsort₂ hlt'
  exact absurd h₂ (not_lt.mpr (le_of_lt h₁))

/-! ### Connectivity -/

/-- **The comparison graph is preconnected.**  For a correct tree and an injective
input, every two positions are joined by a chain of compared pairs.  (The empty
case `n = 0` is preconnected for the same reason it is vacuously correct.) -/
theorem preconnected_comparisonGraph {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) : (comparisonGraph t x).Preconnected := by
  by_contra hcon
  have hcon' : ∃ u v : Fin n, ¬ (comparisonGraph t x).Reachable u v := by
    simpa only [SimpleGraph.Preconnected, not_forall] using hcon
  obtain ⟨u, v, huv⟩ := hcon'
  set B : Set (Fin n) := {w | (comparisonGraph t x).Reachable u w} with hBdef
  have hu : u ∈ B := SimpleGraph.Reachable.refl u
  have hv : v ∉ B := huv
  have hne : u ≠ v := fun he => hv (he ▸ hu)
  -- every compared pair lies inside `B` or outside it
  have hB : ∀ a b, s(a, b) ∈ comparedPairs t x → (a ∈ B ↔ b ∈ B) := by
    intro a b hmem
    by_cases hab : a = b
    · rw [hab]
    · have hadj : (comparisonGraph t x).Adj a b :=
        (SimpleGraph.fromEdgeSet_adj (comparedPairs t x : Set (Sym2 (Fin n)))).mpr ⟨hmem, hab⟩
      exact ⟨fun ha => ha.trans hadj.reachable, fun hb => hb.trans hadj.reachable.symm⟩
  rcases lt_or_gt_of_ne (show x u ≠ x v from fun he => hne (hx he)) with hlt | hlt
  · exact no_cross_pair h hx hB hu hv hlt
  · -- pushing the *complement* of `B` up reverses the same pair
    refine no_cross_pair h hx (B := Bᶜ) (i := v) (j := u) ?_ ?_ ?_ hlt
    · intro a b hmem
      simpa only [Set.mem_compl_iff] using (hB a b hmem).not
    · exact hv
    · exact fun h => h hu

/-- **The comparison graph is connected**, for `n ≥ 1`.  (`n = 0` is the one
exception to the contract's signature: `Fin 0` is empty, so no graph on it is
connected.  `pred_le_cost` is unaffected, because `0 - 1 = 0`.) -/
theorem connected_comparedPairs {t : Tree n} (h : Correct (α := ℕ) t) {x : Fin n → ℕ}
    (hx : Function.Injective x) (hn : 0 < n) : (comparisonGraph t x).Connected :=
  { preconnected := preconnected_comparisonGraph h hx, nonempty := ⟨⟨0, hn⟩⟩ }

end SortBounds.Projects.BestCase
