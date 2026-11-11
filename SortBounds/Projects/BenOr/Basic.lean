/-
SortBounds/Projects/BenOr/Basic.lean

**Algebraic decision trees** (Ben-Or 1983): the model in which a test is not a
comparison but the *sign* of a polynomial.

The comparison model is the special case where every test is the affine
polynomial `x i - x j`, so each test has two outcomes and the counting bound is
`log₂ n!`.  Here a test has three outcomes (`< 0`, `= 0`, `> 0`), so the
combinatorial bound `2 ^ height` still holds for the number of leaves but no
longer captures the difficulty: a single polynomial test may be positive on a
*disconnected* set, so leaves are much weaker than components.  That gap is
exactly where Ben-Or's topological method enters; the statements live in
`SortBounds.Projects.BenOr.Bound`.

This file is the model itself, plus the counting corollary (the `b = 2` shadow of
`SortBounds.card_le_pow_of_prefixFree`): a tree of height `h` has at most `2 ^ h`
leaves.
-/
import Mathlib

namespace SortBounds.Projects.BenOr

/-- An algebraic decision tree over `n` variables (`n` inputs, each in `ℚ`).
Internal nodes branch on the sign of a polynomial — the left subtree is taken
when the polynomial is negative, the right one otherwise — and leaves accept
(`true`) or reject (`false`).  The set decided is `{x | the tree accepts x}`. -/
inductive ADT (n : ℕ) where
  | leaf : Bool → ADT n
  | node : MvPolynomial (Fin n) ℚ → ADT n → ADT n → ADT n

variable {n : ℕ}

/-- Height of the tree: the worst-case number of tests on an input. -/
def ADT.height : ADT n → ℕ
  | .leaf _ => 0
  | .node _ l r => 1 + max l.height r.height

/-- Number of cells of the partition induced by the tree, i.e. the number of
leaves: each leaf carries the cell of inputs that reach it. -/
def ADT.numCells : ADT n → ℕ
  | .leaf _ => 1
  | .node _ l r => l.numCells + r.numCells

/-- Run the tree on the input `x`: follow the sign tests, return the label of the
leaf reached.  A zero test value takes the right branch. -/
def ADT.run : ADT n → (Fin n → ℚ) → Bool
  | .leaf b, _ => b
  | .node p l r, x => if p.eval x < 0 then run l x else run r x

/-- `t` decides `S` if every input reaches a leaf whose label matches `S`, i.e.
the tree accepts exactly the points of `S`. -/
def ADT.decides (t : ADT n) (S : Set (Fin n → ℚ)) : Prop :=
  ∀ x : Fin n → ℚ, (t.run x = true ↔ x ∈ S)

/-- `t` has degree at most `d`: every test is a polynomial of total degree `≤ d`.

The degree bound is not decoration — without it the model is trivial: the single
polynomial `-(∏ i < j, (x i - x j) ^ 2)` is negative exactly on the distinctness
set (`run` takes the left branch iff `p.eval x < 0`), so a tree of height `1` with
no degree bound decides element distinctness.  (Note the minus sign: `run` tests
negativity, and the product of squares is `≥ 0`.)  Every statement of Ben-Or's
bound therefore fixes `d` and lets the constant in `Ω(·)` depend on it. -/
def ADT.degreeLe (d : ℕ) : ADT n → Prop
  | .leaf _ => True
  | .node p l r => p.totalDegree ≤ d ∧ degreeLe d l ∧ degreeLe d r

/-- A binary tree of height `h` has at most `2 ^ h` leaves.  This is the
combinatorial content of the bits-per-probe bound at `b = 2`: it is what remains
of `log₂ n!` once the tests are allowed three outcomes and cells stop being
connected, and it is *not* enough for element distinctness. -/
theorem ADT.card_cells_le (t : ADT n) : t.numCells ≤ 2 ^ t.height := by
  have key : ∀ a b : ℕ, 2 ^ a + 2 ^ b ≤ 2 ^ (1 + max a b) := by
    intro a b
    rcases le_total a b with h | h
    · calc 2 ^ a + 2 ^ b ≤ 2 ^ b + 2 ^ b :=
            Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) h) le_rfl
        _ = 2 ^ (b + 1) := by ring
        _ = 2 ^ (1 + max a b) := by rw [max_eq_right h]; ring
    · calc 2 ^ a + 2 ^ b ≤ 2 ^ a + 2 ^ a :=
            Nat.add_le_add le_rfl (Nat.pow_le_pow_right (by norm_num) h)
        _ = 2 ^ (a + 1) := by ring
        _ = 2 ^ (1 + max a b) := by rw [max_eq_left h]; ring
  induction t with
  | leaf b => simp [ADT.numCells, ADT.height]
  | node p l r ihl ihr =>
    show l.numCells + r.numCells ≤ 2 ^ (1 + max l.height r.height)
    exact le_trans (Nat.add_le_add ihl ihr) (key _ _)

/-- Every tree has at least one cell. -/
theorem ADT.one_le_numCells (t : ADT n) : 1 ≤ t.numCells := by
  induction t with
  | leaf b => simp [ADT.numCells]
  | node p l r ihl ihr => simp only [ADT.numCells]; omega

/-- **The model is not vacuous.**  One linear test decides the half-line
`{x | 0 ≤ x 0}`: the polynomial `x 0` is the affine test of the comparison
model, and here it has three outcomes, of which the tree uses two. -/
noncomputable def halfLineTree : ADT 1 :=
  .node (MvPolynomial.X 0) (.leaf false) (.leaf true)

theorem halfLineTree_decides : halfLineTree.decides {x : Fin 1 → ℚ | 0 ≤ x 0} := by
  intro x
  show (if (MvPolynomial.X (0 : Fin 1)).eval x < 0 then false else true) = true ↔
    0 ≤ x 0
  rw [MvPolynomial.eval_X]
  by_cases h : x 0 < 0
  · rw [ite_eq_left h]
    simp only [Bool.false_eq_true, false_iff]
    linarith
  · rw [ite_eq_right h]
    simp only [true_iff]
    linarith

/-- The degree bookkeeping bites: the half-line tree is an affine test. -/
theorem halfLineTree_degreeLe : halfLineTree.degreeLe 1 := by
  simp [halfLineTree, ADT.degreeLe]

end SortBounds.Projects.BenOr
