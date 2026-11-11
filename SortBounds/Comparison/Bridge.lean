/-
SortBounds/Comparison/Bridge.lean

**Closing the Θ-gap inside one model.**  The lower bound (`Ω(n log n)`) lives in
the `Tree` model; the matching upper bound so far lived in a *list* model
(`Instances.MergeSort.msortCount`), and the two were never formally connected.
This file starts the connection: a *tree substitution* operation that lifts a
decision tree for `n` positions to a decision tree for `n+1` positions by
replacing every leaf (which knows the sorted order of the prefix) with an
insertion tree.

Why substitution is the right tool: after the prefix `0..n-1` has been sorted, the
*leaf* tells us the order `σ : Equiv.Perm (Fin n)` of those values, and only then
does it make sense to ask "where does element `n` belong?" — binary search must
compare `x n` against `x (σ mid)`, and `σ` is known at the leaf.  So the
`n+1`-tree is: run the `n`-tree, then, at each leaf `σ`, run `insertTree σ`.

Contents (M0):

* `liftTree` — substitute `Perm (Fin n) → Tree (n+1)` into the leaves of `Tree n`;
* `run_liftTree` — the substituted tree behaves as the prefix tree followed by
  the leaf's tree (the nodes are carried along `Fin.castSucc`);
* `liftTree_correct` — correctness transfers, given a leaf-level hypothesis;
* `depth_liftTree_le` — depth is the prefix depth plus a leaf bound.

Next (M1): `insertTree (σ : Perm (Fin n)) : Tree (n+1)`, binary search for the
rank of `x n` among `x (σ 0) < … < x (σ (n-1))`, with leaves
`insertPerm σ j` (the permutation of `Fin (n+1)` that inserts `Fin.last n` at
rank `j`); then `sortTree (n) : Tree n` by iterating `liftTree`, giving
`S n ≤ n · (⌈log₂ n⌉ + 1)`.  That closes `Θ(n log n)` in the `Tree` model alone.
-/
import SortBounds.Comparison.Tree

namespace SortBounds

variable {n : ℕ}

/-- Substitute a family of trees into the leaves of `t`, keeping the comparisons
(the positions of `Tree n` are carried into `Tree (n+1)` along `Fin.castSucc`). -/
def liftTree : Tree n → (Equiv.Perm (Fin n) → Tree (n+1)) → Tree (n+1)
  | .leaf σ, f => f σ
  | .node i j l r, f =>
      .node (Fin.castSucc i) (Fin.castSucc j) (liftTree l f) (liftTree r f)

/-- The lifted tree first sorts the prefix (as `t` does) and then follows the leaf's
tree, on the whole input. -/
theorem run_liftTree [LinearOrder α] (t : Tree n) (f : Equiv.Perm (Fin n) → Tree (n+1))
    (x : Fin (n + 1) → α) :
    run (liftTree t f) x = run (f (run t (fun k => x (Fin.castSucc k)))) x := by
  induction t with
  | leaf σ => rfl
  | node i j l r ihl ihr =>
    show (if x (Fin.castSucc i) < x (Fin.castSucc j) then run (liftTree l f) x
        else run (liftTree r f) x)
      = run (f (if x (Fin.castSucc i) < x (Fin.castSucc j)
          then run l (fun k => x (Fin.castSucc k)) else run r (fun k => x (Fin.castSucc k)))) x
    by_cases h : x (Fin.castSucc i) < x (Fin.castSucc j)
    · rw [ite_eq_left h, ite_eq_left h, ihl]
    · rw [ite_eq_right h, ite_eq_right h, ihr]

/-- Depth of the lifted tree is the prefix depth plus a uniform leaf bound. -/
theorem depth_liftTree_le (t : Tree n) (f : Equiv.Perm (Fin n) → Tree (n+1)) (B : ℕ)
    (hB : ∀ σ, depth (f σ) ≤ B) : depth (liftTree t f) ≤ depth t + B := by
  induction t with
  | leaf σ =>
    show depth (f σ) ≤ 0 + B
    simpa using hB σ
  | node i j l r ihl ihr =>
    show 1 + max (depth (liftTree l f)) (depth (liftTree r f)) ≤ 1 + max (depth l) (depth r) + B
    have hl := ihl
    have hr := ihr
    omega

/-- Correctness transfers through substitution: `t` sorts the prefix, and each
leaf's tree finishes the job given the prefix order it was handed. -/
theorem liftTree_correct {t : Tree n} (ht : Correct (α := ℕ) t)
    {f : Equiv.Perm (Fin n) → Tree (n+1)}
    (hf : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin (n + 1) → ℕ), Function.Injective x →
        StrictMono (fun k : Fin n => x (Fin.castSucc (σ k))) → Sorts x (run (f σ) x)) :
    Correct (α := ℕ) (liftTree t f) := by
  intro x hx
  rw [run_liftTree]
  apply hf _ x hx
  have hprefix : Function.Injective fun k : Fin n => x (Fin.castSucc k) :=
    fun a b hab => Fin.castSucc_injective n (hx hab)
  exact ht (fun k => x (Fin.castSucc k)) hprefix

end SortBounds
