/-
SortBounds/Projects/SN/Verify.lean

The tools the explicit optimal trees (`Four.lean` … `Seven.lean`) are checked with:

* `netTree`: read a *comparator sequence* (a sorting network, or any fixed
  sequence of pairwise comparisons) as a comparison tree.  The tree is built in
  wire coordinates: `π` maps a wire to the input position currently sitting on
  it, a node compares the two positions on the wires it names, and the swapping
  outcome updates `π` by composing with `Equiv.swap i j`.  The leaves carry `π`,
  which is the sorting permutation whenever the comparator sequence sorts its
  input.  (`SortBounds.Instances.Network` reads the same kind of comparator list
  as a fold producing a permutation, `runPerm`; `netTree` is its decision-tree
  counterpart, which is what a depth — and hence `S` — is defined for.)

* `correct_of_forall_run_xOfPerm`: correctness of a comparison tree on `n`
  positions follows from its behaviour on the `n!` canonical inputs `xOfPerm p`
  alone.  For an injective input `x`, `run` depends only on the comparison
  pattern (`run_eq_of_pattern`), and that pattern is the pattern of the canonical
  input indexed by `x`'s ranking permutation (`pattern_rankPerm`); so the `n!`
  canonical inputs are a complete test, and it is a finite computation.

* `correct_of_list_all` (with `allPerms`, `mem_allPerms`): the same reduction, but
  with the `n!` canonical inputs listed explicitly instead of enumerated through
  `Fintype (Equiv.Perm (Fin n))`.  That instance filters the `n ^ n` functions
  `Fin n → Fin n`, which is what dominated `decide`'s cost for `n = 6, 7`;
  `allPerms` costs `n!` steps and is deliberately written with *structural*
  recursion (`permsOf`/`inserts`) so that the kernel can evaluate it — Lean's
  `List.permutations` is defined by well-founded recursion and `decide` gets stuck
  on it (`example : (List.permutations [1, 2, 3]).length = 6 := by decide` fails).

* `swapProd`: a leaf permutation written as a product of transpositions.
-/
import SortBounds.Comparison.General

namespace SortBounds.Projects.SN

open SortBounds

variable {n : ℕ}

/-! ### Trees from comparator sequences -/

/-- The product of the transpositions in `ps`, in the order given:
`swapProd [(0, 1), (1, 2)] = Equiv.swap 0 1 * Equiv.swap 1 2` sends
`0 ↦ 1 ↦ 2 ↦ 0`.  (An empty list is the identity.) -/
def swapProd (ps : List (Fin n × Fin n)) : Equiv.Perm (Fin n) :=
  ps.foldr (fun p q => Equiv.swap p.1 p.2 * q) 1

theorem swapProd_nil : swapProd ([] : List (Fin n × Fin n)) = 1 := rfl

/-- The multiplication order of `swapProd`, spelled out: the first pair of the
list is the leftmost factor, so the last pair acts first. -/
theorem swapProd_cons (p : Fin n × Fin n) (ps : List (Fin n × Fin n)) :
    swapProd (p :: ps) = Equiv.swap p.1 p.2 * swapProd ps := rfl

/-- `netTree ps π` asks the comparisons of `ps` in order, on wires: the pair
`(i, j)` compares the positions currently on wires `i` and `j`, and if the second
one is the smaller the two wires are exchanged.  The leaves are the wire states,
i.e. the permutation `k ↦ (position on wire k)`. -/
def netTree : (ps : List (Fin n × Fin n)) → Equiv.Perm (Fin n) → Tree n
  | [], π => Tree.leaf π
  | (i, j) :: ps, π =>
      Tree.node (π i) (π j) (netTree ps π) (netTree ps (π * Equiv.swap i j))

/-- Comparing one wire pair adds one to the depth: a sequence of `k` comparators
gives a tree of depth `k`. -/
theorem netTree_depth (ps : List (Fin n × Fin n)) (π : Equiv.Perm (Fin n)) :
    depth (netTree ps π) = ps.length := by
  induction ps generalizing π with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨i, j⟩ := p
    simp only [netTree, depth, ih, List.length_cons]
    omega

/-! ### Correctness from the canonical inputs -/

/-- **A tree that sorts the `n!` canonical inputs sorts everything.**  For an
injective input the comparison pattern determines the ranking permutation
(`pattern_rankPerm`), and `run` depends only on the comparison pattern, so the
answer on `x` is the answer on the canonical input of the same pattern. -/
theorem correct_of_forall_run_xOfPerm {t : Tree n}
    (h : ∀ p : Equiv.Perm (Fin n), run t (xOfPerm p) = p) : Correct (α := ℕ) t := by
  intro x hx
  rw [run_eq_of_pattern t (pattern_rankPerm hx), h (rankPerm x hx)]
  exact sorts_rankPerm hx

/-! ### A cheap enumeration of the canonical inputs

`correct_of_list_all` turns the reduction above into a `decide` over an explicit
list of permutations.  Two things matter:

* the list must *evaluate in the kernel*, so it is built with structural
  recursion only (`inserts`, `permsOf`), not with `List.permutations`;
* it must contain each of the `n!` permutations exactly as a permutation value,
  without enumerating the `n ^ n` functions `Fin n → Fin n`: `allPerms` maps
  `permOfList` over the `n!` *orderings* of `Fin n`.
-/

section Enumeration

variable {α : Type*}

/-- `inserts a t` puts `a` in front of `t` and at every position inside it:
`inserts 0 [1, 2] = [[0, 1, 2], [1, 0, 2], [1, 2, 0]]`. -/
def inserts (a : α) : List α → List (List α)
  | [] => [[a]]
  | b :: t => (a :: b :: t) :: (inserts a t).map (List.cons b)

@[simp] theorem inserts_nil (a : α) : inserts a [] = [[a]] := rfl

/-- What the insertion list contains. -/
theorem mem_inserts {a : α} {t l : List α} :
    l ∈ inserts a t ↔ ∃ l₁ l₂, t = l₁ ++ l₂ ∧ l = l₁ ++ a :: l₂ := by
  induction t generalizing l with
  | nil =>
    rw [inserts_nil, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨[], [], rfl, rfl⟩
    · rintro ⟨l₁, l₂, hl, rfl⟩
      cases l₁ <;> simp_all
  | cons b t ih =>
    rw [inserts, List.mem_cons, List.mem_map]
    constructor
    · rintro (rfl | ⟨u, hu, rfl⟩)
      · exact ⟨[], b :: t, rfl, rfl⟩
      · obtain ⟨l₁, l₂, ht, rfl⟩ := ih.1 hu
        exact ⟨b :: l₁, l₂, by simp [ht], rfl⟩
    · rintro ⟨l₁, l₂, h, rfl⟩
      cases l₁ with
      | nil => exact Or.inl (by simpa using h.symm ▸ rfl)
      | cons c l₁ =>
        obtain ⟨rfl, ht⟩ := List.cons.inj h
        refine Or.inr ⟨l₁ ++ a :: l₂, ih.2 ⟨l₁, l₂, ht, rfl⟩, ?_⟩
        rfl

/-- A list obtained by inserting `a` into `t` is a permutation of `a :: t`. -/
theorem perm_of_mem_inserts {a : α} {t l : List α} (h : l ∈ inserts a t) :
    l.Perm (a :: t) := by
  obtain ⟨l₁, l₂, rfl, rfl⟩ := mem_inserts.1 h
  exact List.perm_middle

/-- All permutations of `l`, by inserting the head into the permutations of the tail.
Structural recursion, so `decide` can evaluate it. -/
def permsOf : List α → List (List α)
  | [] => [[]]
  | a :: t => (permsOf t).foldr (fun s acc => inserts a s ++ acc) []

/-- Undoing one fold step of `permsOf`. -/
theorem mem_foldr_inserts {a : α} {l : List (List α)} {t : List α} :
    t ∈ l.foldr (fun s acc => inserts a s ++ acc) [] ↔ ∃ s ∈ l, t ∈ inserts a s := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.foldr_cons, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨u, hu, h⟩)
      · exact ⟨s, Or.inl rfl, h⟩
      · exact ⟨u, Or.inr hu, h⟩
    · rintro ⟨u, rfl | hu, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨u, hu, h⟩

/-- **`permsOf l` is exactly the set of permutations of `l`.** -/
theorem mem_permsOf {l t : List α} : t ∈ permsOf l ↔ t.Perm l := by
  induction l generalizing t with
  | nil => simp [permsOf]
  | cons a l ih =>
    rw [permsOf, mem_foldr_inserts]
    constructor
    · rintro ⟨s, hs, ht⟩
      have hs' : s.Perm l := (ih (t := s)).1 hs
      exact (perm_of_mem_inserts ht).trans (hs'.cons a)
    · intro h
      have ha : a ∈ t := h.mem_iff.2 (List.mem_cons_self ..)
      obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.1 ha
      refine ⟨l₁ ++ l₂, (ih (t := l₁ ++ l₂)).2 ?_, mem_inserts.2 ⟨l₁, l₂, rfl, rfl⟩⟩
      exact ((List.perm_middle (l₁ := l₁) (l₂ := l₂) (a := a)).symm.trans h).cons_inv

end Enumeration

section Permutations

/-- The permutation whose inverse reads `l` off: `(permOfList l …).symm k = l.get k`, so
value `k` sits at position `l[k]` in the ordering `l`.  This is the direction
`xOfPerm` reads (`xOfPerm p i = (p.symm i : ℕ)`), so it is the side that has to be
cheap when `decide` walks a tree. -/
def permOfList (l : List (Fin n)) (hlen : l.length = n) (hnd : l.Nodup)
    (hmem : ∀ x, x ∈ l) : Equiv.Perm (Fin n) :=
  ((finCongr hlen.symm).trans (hnd.getEquivOfForallMemList l hmem)).symm

theorem permOfList_symm_apply (l : List (Fin n)) (hlen : l.length = n) (hnd : l.Nodup)
    (hmem : ∀ x, x ∈ l) (k : Fin n) :
    (permOfList l hlen hnd hmem).symm k = l.get (Fin.cast hlen.symm k) := rfl

/-- **Every permutation of `Fin n`, as a list of permutations.**  `n!` elements, from
the `n!` orderings returned by `permsOf (List.finRange n)`; no filtering. -/
def allPerms (n : ℕ) : List (Equiv.Perm (Fin n)) :=
  ((permsOf (List.finRange n)).attach).map fun l =>
    permOfList l.1 (by rw [(mem_permsOf.1 l.2).length_eq, List.length_finRange])
      ((List.nodup_finRange n).perm (mem_permsOf.1 l.2).symm)
      (fun x => (mem_permsOf.1 l.2).symm.subset (List.mem_finRange x))

/-- The enumeration is complete. -/
theorem mem_allPerms (p : Equiv.Perm (Fin n)) : p ∈ allPerms n := by
  have hperm : List.Perm ((List.finRange n).map p.symm) (List.finRange n) :=
    Equiv.Perm.map_finRange_perm p.symm
  have hlen : ((List.finRange n).map p.symm).length = n := by simp
  have hnd : ((List.finRange n).map p.symm).Nodup := (List.nodup_finRange n).perm hperm.symm
  have hmem : ∀ x : Fin n, x ∈ (List.finRange n).map p.symm :=
    fun x => hperm.symm.subset (List.mem_finRange x)
  have hkey : permOfList ((List.finRange n).map p.symm) hlen hnd hmem = p := by
    have h : (permOfList ((List.finRange n).map p.symm) hlen hnd hmem).symm = p.symm := by
      ext k
      rw [permOfList_symm_apply, List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
      exact congrArg (fun x => ((p.symm x : Fin n) : ℕ)) (Fin.ext rfl)
    have := congrArg Equiv.symm h
    simpa using this
  rw [allPerms, List.mem_map]
  exact ⟨⟨_, mem_permsOf.2 hperm⟩, List.mem_attach _ _, hkey⟩

end Permutations

/-! ### Correctness from a list of permutations -/

/-- **Correctness from a list of permutations that contains every permutation.**
`correct_of_forall_run_xOfPerm` with the `n!` canonical inputs supplied as a list, so
that `decide` only has to evaluate the tree on them. -/
theorem correct_of_list_all {t : Tree n} (L : List (Equiv.Perm (Fin n)))
    (hL : ∀ p, p ∈ L) (h : L.all (fun p => decide (run t (xOfPerm p) = p)) = true) :
    Correct (α := ℕ) t :=
  correct_of_forall_run_xOfPerm fun p =>
    of_decide_eq_true (List.all_eq_true.1 h p (hL p))

/-- The same, with the enumeration filled in: `decide` checks the tree on the `n!`
canonical inputs and nothing else. -/
theorem correct_of_allPerms {t : Tree n}
    (h : (allPerms n).all (fun p => decide (run t (xOfPerm p) = p)) = true) :
    Correct (α := ℕ) t :=
  correct_of_list_all _ mem_allPerms h

end SortBounds.Projects.SN
