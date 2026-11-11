/-
SortBounds/Projects/SN/Basic.lean

`S n`: the fewest comparisons that sort `n` elements, as the least depth of a
correct comparison tree (`SortBounds.Tree`).

Contents (milestone M0):

* `exists_correct_tree`: some correct tree exists on `n` positions.  The witness
  is deliberately stupid — compare *every* pair in a fixed order, then read the
  sorted order off the answers — but it is derived from the answers alone, which
  is what a decision tree can do.  Its depth is quadratic, so it certifies
  existence (and makes `S` well defined) without claiming optimality.
* `S` as the infimum of achievable depths, with `S_spec` and `S_le_iff`.
* `S_lower`: counting (`n! ≤ 2 ^ depth`) gives `⌈log₂ n!⌉ ≤ S n`.

The optimal small cases (`S 0` … `S 3`) live in `SortBounds.Projects.SN.Small`.
-/
import SortBounds.Comparison.Tree

namespace SortBounds.Projects.SN

open SortBounds

variable {n : ℕ}

/-! ### Reading a permutation off a table of comparison answers -/

/-- A table of comparison outcomes: `tbl i j` answers "is `x i < x j`?". -/
abbrev Table (n : ℕ) := Fin n → Fin n → Bool

/-- The number of positions that are recorded as beating `i`.  On a genuine
(consistent, injective) table this is the rank of `x i` in sorted order. -/
def losses (tbl : Table n) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => tbl j i).card

/-- Sort key: number of losses first, position as tie-break.  The tie-break makes
the key injective for *every* table, so the permutation derived from it below is
defined without any case distinction. -/
def sortKey (tbl : Table n) (i : Fin n) : ℕ :=
  n * losses tbl i + (i : ℕ)

theorem sortKey_injective (tbl : Table n) : Function.Injective (sortKey tbl) := by
  have hkey : ∀ i j : Fin n, sortKey tbl i = sortKey tbl j → losses tbl i = losses tbl j := by
    intro i j h
    have hi : (i : ℕ) < n := i.isLt
    have hj : (j : ℕ) < n := j.isLt
    simp only [sortKey] at h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact absurd hi (by omega)
    rcases lt_trichotomy (losses tbl i) (losses tbl j) with hlt | heq | hgt
    · have hstep : n * losses tbl i + n ≤ n * losses tbl j := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left n (by omega)
      omega
    · exact heq
    · have hstep : n * losses tbl j + n ≤ n * losses tbl i := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left n (by omega)
      omega
  intro i j h
  have hloss := hkey i j h
  simp only [sortKey] at h
  rw [hloss] at h
  exact Fin.ext (Nat.add_left_cancel h)

/-- Position of `i`'s key in sorted order: the number of keys strictly below it. -/
def sortPos (tbl : Table n) (i : Fin n) : Fin n :=
  ⟨(Finset.univ.filter fun j => sortKey tbl j < sortKey tbl i).card, by
    have hsub : (Finset.univ.filter fun j => sortKey tbl j < sortKey tbl i) ⊂
        (Finset.univ : Finset (Fin n)) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
      have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
      rw [← heq] at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact absurd hmem (lt_irrefl _)
    simpa using Finset.card_lt_card hsub⟩

theorem sortPos_lt_iff (tbl : Table n) (i j : Fin n) :
    sortPos tbl i < sortPos tbl j ↔ sortKey tbl i < sortKey tbl j := by
  have key_mono : sortKey tbl i < sortKey tbl j →
      sortPos tbl i < sortPos tbl j := by
    intro h
    have hsub : (Finset.univ.filter fun k => sortKey tbl k < sortKey tbl i) ⊂
        (Finset.univ.filter fun k => sortKey tbl k < sortKey tbl j) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        omega
      · intro heq
        have hmem : i ∈ Finset.univ.filter fun k => sortKey tbl k < sortKey tbl j := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact h
        rw [← heq] at hmem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact absurd hmem (lt_irrefl _)
    exact Finset.card_lt_card hsub
  refine ⟨fun h => ?_, key_mono⟩
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ.filter fun k => sortKey tbl k < sortKey tbl j) ⊆
      (Finset.univ.filter fun k => sortKey tbl k < sortKey tbl i) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    omega
  have hle := Finset.card_le_card hsub
  exact absurd h (not_lt.mpr hle)

theorem sortPos_injective (tbl : Table n) : Function.Injective (sortPos tbl) := by
  intro i j h
  by_contra hne
  have hkey := sortKey_injective tbl
  have hlt : sortKey tbl i ≠ sortKey tbl j := fun hc => hne (hkey hc)
  rcases lt_or_gt_of_ne hlt with h' | h'
  · have := (sortPos_lt_iff tbl i j).2 h'
    rw [h] at this
    exact absurd this (lt_irrefl _)
  · have := (sortPos_lt_iff tbl j i).2 h'
    rw [h] at this
    exact absurd this (lt_irrefl _)

theorem sortPos_bijective (tbl : Table n) : Function.Bijective (sortPos tbl) :=
  ⟨sortPos_injective tbl, Finite.surjective_of_injective (sortPos_injective tbl)⟩

/-- The permutation read off a table: the inverse of the position map, i.e. the
`k`-th entry is the position whose key is the `k`-th smallest. -/
noncomputable def tablePerm (tbl : Table n) : Equiv.Perm (Fin n) :=
  (Equiv.ofBijective (sortPos tbl) (sortPos_bijective tbl)).symm

/-! ### The table of a genuine input yields the sorting permutation -/

/-- On a genuine input, the recorded losses count the smaller values. -/
theorem losses_eq (tbl : Table n) {x : Fin n → ℕ}
    (htbl : ∀ i j, tbl i j = decide (x i < x j)) (i : Fin n) :
    losses tbl i = (Finset.univ.filter fun j => x j < x i).card := by
  unfold losses
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [htbl j i, decide_eq_true_iff]

theorem card_lt_card_filter {x : Fin n → ℕ} {i j : Fin n} (h : x i < x j) :
    (Finset.univ.filter fun k => x k < x i).card <
      (Finset.univ.filter fun k => x k < x j).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    omega
  · intro heq
    have hmem : i ∈ Finset.univ.filter fun k => x k < x j := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    rw [← heq] at hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact absurd hmem (lt_irrefl _)

theorem losses_lt_iff (tbl : Table n) {x : Fin n → ℕ} (hx : Function.Injective x)
    (htbl : ∀ i j, tbl i j = decide (x i < x j)) (i j : Fin n) :
    losses tbl i < losses tbl j ↔ x i < x j := by
  rw [losses_eq tbl htbl i, losses_eq tbl htbl j]
  refine ⟨fun h => ?_, fun h => card_lt_card_filter h⟩
  by_contra hc
  push Not at hc
  rcases lt_or_eq_of_le hc with h' | h'
  · have := card_lt_card_filter h'
    omega
  · have hij : i = j := hx h'.symm
    subst hij
    exact absurd h (lt_irrefl _)

theorem losses_injective (tbl : Table n) {x : Fin n → ℕ} (hx : Function.Injective x)
    (htbl : ∀ i j, tbl i j = decide (x i < x j)) : Function.Injective (losses tbl) := by
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne (hx.ne hne) with h' | h'
  · have := (losses_lt_iff tbl hx htbl i j).2 h'
    omega
  · have := (losses_lt_iff tbl hx htbl j i).2 h'
    omega

theorem sortKey_lt_of_losses_lt (tbl : Table n) {i j : Fin n}
    (h : losses tbl i < losses tbl j) : sortKey tbl i < sortKey tbl j := by
  show n * losses tbl i + (i : ℕ) < n * losses tbl j + (j : ℕ)
  calc n * losses tbl i + (i : ℕ) < n * losses tbl i + n := by omega
    _ = n * (losses tbl i + 1) := by rw [Nat.mul_succ]
    _ ≤ n * losses tbl j := Nat.mul_le_mul_left n (by omega)
    _ ≤ n * losses tbl j + (j : ℕ) := Nat.le_add_right _ _

theorem sortKey_lt_iff_losses_lt (tbl : Table n) (hinj : Function.Injective (losses tbl))
    (i j : Fin n) : sortKey tbl i < sortKey tbl j ↔ losses tbl i < losses tbl j := by
  refine ⟨fun h => ?_, sortKey_lt_of_losses_lt tbl⟩
  by_contra hc
  push Not at hc
  rcases lt_or_eq_of_le hc with h' | h'
  · have := sortKey_lt_of_losses_lt tbl h'
    omega
  · have hij : i = j := hinj h'.symm
    subst hij
    exact absurd h (lt_irrefl _)

theorem sortPos_tablePerm (tbl : Table n) (a : Fin n) : sortPos tbl (tablePerm tbl a) = a := by
  rw [tablePerm]
  exact Equiv.ofBijective_apply_symm_apply (sortPos tbl) (sortPos_bijective tbl) a

/-- **The label read off the true comparison table is the sorting permutation.** -/
theorem tablePerm_sorts (tbl : Table n) {x : Fin n → ℕ} (hx : Function.Injective x)
    (htbl : ∀ i j, tbl i j = decide (x i < x j)) : Sorts x (tablePerm tbl) := by
  have hinj := losses_injective tbl hx htbl
  intro a b hab
  have h₁ : sortPos tbl (tablePerm tbl a) < sortPos tbl (tablePerm tbl b) := by
    rw [sortPos_tablePerm, sortPos_tablePerm]
    exact hab
  have h₂ := (sortPos_lt_iff tbl _ _).1 h₁
  have h₃ := (sortKey_lt_iff_losses_lt tbl hinj _ _).1 h₂
  exact (losses_lt_iff tbl hx htbl _ _).1 h₃

/-! ### A correct tree on `n` positions -/

/-- Every ordered pair of positions, in a fixed order. -/
def allPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).product (List.finRange n)

theorem mem_allPairs (i j : Fin n) : (i, j) ∈ allPairs n := by
  simp [allPairs]

theorem nodup_allPairs (n : ℕ) : (allPairs n).Nodup :=
  List.Nodup.product (List.nodup_finRange n) (List.nodup_finRange n)

theorem run_node {α : Type*} [LinearOrder α] (i j : Fin n) (l r : Tree n)
    (x : Fin n → α) : run (Tree.node i j l r) x = if x i < x j then run l x else run r x := rfl

/-- Ask the comparisons in `ps` in order, recording the answers in a table, and
hand the completed table to `k`. -/
def pairTree (ps : List (Fin n × Fin n)) (tbl : Table n) (k : Table n → Tree n) : Tree n :=
  match ps with
  | [] => k tbl
  | (i, j) :: rest =>
    Tree.node i j
      (pairTree rest (fun a b => if a = i ∧ b = j then true else tbl a b) k)
      (pairTree rest (fun a b => if a = i ∧ b = j then false else tbl a b) k)

/-- Running `pairTree` fills the table with the true answers for the pairs it
asked, and agrees with the incoming table elsewhere. -/
theorem run_pairTree (ps : List (Fin n × Fin n)) (hnd : ps.Nodup) (tbl : Table n)
    (k : Table n → Tree n) (x : Fin n → ℕ) :
    ∃ tbl' : Table n, run (pairTree ps tbl k) x = run (k tbl') x ∧
      (∀ p ∈ ps, tbl' p.1 p.2 = decide (x p.1 < x p.2)) ∧
      (∀ i j, (i, j) ∉ ps → tbl' i j = tbl i j) := by
  induction ps generalizing tbl with
  | nil => exact ⟨tbl, rfl, by simp, fun i j _ => rfl⟩
  | cons p ps ih =>
    obtain ⟨i, j⟩ := p
    have hmem : (i, j) ∉ ps := (List.nodup_cons.1 hnd).1
    have hnd' : ps.Nodup := (List.nodup_cons.1 hnd).2
    have hnot : ∀ a b, (a, b) ∉ (i, j) :: ps → ¬(a = i ∧ b = j) := by
      intro a b hab hc
      exact hab (by simp [hc])
    by_cases hlt : x i < x j
    · obtain ⟨tbl', hrun, hcorr, hoff⟩ :=
        ih hnd' fun a b => if a = i ∧ b = j then true else tbl a b
      refine ⟨tbl', ?_, ?_, ?_⟩
      · rw [pairTree, run_node, ite_eq_left hlt]
        exact hrun
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq'
        · have h₁ : tbl' i j = true := by
            simpa using hoff i j hmem
          rw [h₁]
          exact (decide_eq_true hlt).symm
        · exact hcorr q hq'
      · intro a b hab
        rw [hoff a b (fun hc => hab (List.mem_cons_of_mem _ hc))]
        simp only [hnot a b hab, ite_false]
    · obtain ⟨tbl', hrun, hcorr, hoff⟩ :=
        ih hnd' fun a b => if a = i ∧ b = j then false else tbl a b
      refine ⟨tbl', ?_, ?_, ?_⟩
      · rw [pairTree, run_node, ite_eq_right hlt]
        exact hrun
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq'
        · have h₁ : tbl' i j = false := by
            simpa using hoff i j hmem
          rw [h₁]
          exact (decide_eq_false_iff_not.2 hlt).symm
        · exact hcorr q hq'
      · intro a b hab
        rw [hoff a b (fun hc => hab (List.mem_cons_of_mem _ hc))]
        simp only [hnot a b hab, ite_false]

/-- Compare every pair of positions, then output the sorted order read off the
answers.  (Depth is quadratic — this only certifies existence.) -/
noncomputable def tableTree (n : ℕ) : Tree n :=
  pairTree (allPairs n) (fun _ _ => false) fun tbl => Tree.leaf (tablePerm tbl)

/-- Merge sort (or insertion sort) gives *some* correct tree for every `n`.
Neither is formalised here: the witness below just asks every pair of positions
and reads the order off the answers, which is enough for existence. -/
theorem exists_correct_tree (n : ℕ) : ∃ t : Tree n, Correct (α := ℕ) t := by
  refine ⟨tableTree n, fun x hx => ?_⟩
  obtain ⟨tbl, hrun, hcorr, -⟩ :=
    run_pairTree (allPairs n) (nodup_allPairs n) (fun _ _ => false)
      (fun tbl => Tree.leaf (tablePerm tbl)) x
  have htbl : ∀ i j : Fin n, tbl i j = decide (x i < x j) := fun i j =>
    hcorr (i, j) (mem_allPairs i j)
  have hrun' : run (tableTree n) x = tablePerm tbl := hrun
  rw [hrun']
  exact tablePerm_sorts tbl hx htbl

/-! ### The optimal depth `S n` -/

/-- The set of depths achievable by correct comparison trees on `n` positions. -/
def depths (n : ℕ) : Set ℕ :=
  {d : ℕ | ∃ t : Tree n, Correct (α := ℕ) t ∧ depth t ≤ d}

/-- `S n`: the least *depth* of a correct comparison tree on `n` positions.  By
`Comparison.Tree.exists_depth_le_of_cost_le` this is also the least worst-case
*number of comparisons*, i.e. exactly "the fewest comparisons that suffice to sort
`n` elements": a tree whose every input costs `≤ d` is truncated (`prune`) to depth
`≤ d` without losing correctness, and conversely `cost ≤ depth`. -/
noncomputable def S (n : ℕ) : ℕ :=
  sInf (depths n)

theorem depths_nonempty (n : ℕ) : (depths n).Nonempty := by
  obtain ⟨t, ht⟩ := exists_correct_tree n
  exact ⟨depth t, t, ht, le_rfl⟩

theorem S_spec (n : ℕ) : ∃ t : Tree n, Correct (α := ℕ) t ∧ depth t ≤ S n :=
  Nat.sInf_mem (depths_nonempty n)

theorem S_le_iff (n d : ℕ) : S n ≤ d ↔ ∃ t : Tree n, Correct (α := ℕ) t ∧ depth t ≤ d := by
  refine ⟨fun h => ?_, fun h => Nat.sInf_le h⟩
  obtain ⟨t, ht, hd⟩ := S_spec n
  exact ⟨t, ht, le_trans hd h⟩

/-- **Fewest comparisons that suffice ⇒ least depth.**  This is the direction that
makes `S n` mean "fewest comparisons": a tree whose every input costs at most `d` can
be truncated to depth `d` (`Comparison.Tree.exists_depth_le_of_cost_le`). -/
theorem S_le_of_forall_cost_le {n d : ℕ}
    (h : ∃ t : Tree n, Correct (α := ℕ) t ∧
      ∀ x : Fin n → ℕ, Function.Injective x → cost t x ≤ d) : S n ≤ d := by
  obtain ⟨t, ht, hcost⟩ := h
  obtain ⟨t', ht', hdepth⟩ := exists_depth_le_of_cost_le ht hcost
  exact (S_le_iff n d).mpr ⟨t', ht', hdepth⟩

/-- Lower bound: counting (`n! ≤ 2^depth`). -/
theorem S_lower (n : ℕ) : Nat.clog 2 (Nat.factorial n) ≤ S n := by
  obtain ⟨t, ht, hd⟩ := S_spec n
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  exact le_trans (factorial_le_two_pow_depth ht) (Nat.pow_le_pow_right (by norm_num) hd)

end SortBounds.Projects.SN
