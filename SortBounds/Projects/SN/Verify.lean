/-
SortBounds/Projects/SN/Verify.lean

Two tools, plus one notation, are used by the explicit optimal trees
(`Four.lean`, `Five.lean`):

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

end SortBounds.Projects.SN
