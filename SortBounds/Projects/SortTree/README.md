# Lane: SortTree — `Θ(n log n)` inside the `Tree` model alone

**Question.** The lower bound (`Ω(n log n)`) is a theorem about `Tree n`. The
matching upper bound currently lives in a *list* model
(`Instances.MergeSort.msortCount`), so "the optimal worst case is `Θ(n log n)`"
is only true across two models. This lane closes that: build a `Tree n` of depth
`n·(⌈log₂ n⌉+1)` that is `Correct`, so that `S n` — the least depth — satisfies
`⌈log₂ n!⌉ ≤ S n ≤ n(⌈log₂ n⌉+1)` with every step in one model.

**Mechanism (M0 already landed, in `Comparison/Bridge.lean`).** `liftTree`
substitutes, at each leaf `σ` of a prefix tree, the tree `f σ`. Substitution is
the right tool because the leaf knows the prefix order `σ`, and binary insertion
must compare `x (last n)` against `x (castSucc (σ mid))` — which needs `σ`.

**Non-vacuity.** `S 2 = 1`, `S 3 = 3` are already proved (`Projects/SN`), so
"`Correct` tree of depth d" is satisfiable; this lane must beat the trivial
compare-everything tree (`depth n²`, `SN.exists_correct_tree`).

## Contract (exact target signatures)

```lean
namespace SortBounds.Projects.SortTree

open SortBounds

/-- The permutation of `Fin (n+1)` that lists the prefix order `σ` and puts the
new element (`Fin.last n`) at rank `j`. -/
noncomputable def insertPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1))

/-- The rank of the new element among the sorted prefix, as a `Fin (n+1)`. -/
noncomputable def rankOf {n : ℕ} (x : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) : Fin (n + 1)

/-- `insertPerm σ (rankOf x σ)` sorts `x`, given the prefix is sorted by `σ`. -/
theorem insertPerm_sorts {n : ℕ} {σ : Equiv.Perm (Fin n)} {x : Fin (n + 1) → ℕ}
    (hx : Function.Injective x)
    (hmono : StrictMono fun k : Fin n => x (Fin.castSucc (σ k))) :
    Sorts x (insertPerm σ (rankOf x σ))

/-- Binary search for the insertion rank: a tree of depth `≤ ⌈log₂ (n+1)⌉ + 1`. -/
noncomputable def insertTree {n : ℕ} (σ : Equiv.Perm (Fin n)) : Tree (n + 1)
theorem insertTree_depth_le {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    depth (insertTree σ) ≤ Nat.clog 2 (n + 1) + 1
theorem insertTree_correct {n : ℕ} (σ : Equiv.Perm (Fin n)) {x : Fin (n + 1) → ℕ}
    (hx : Function.Injective x)
    (hmono : StrictMono fun k : Fin n => x (Fin.castSucc (σ k))) :
    Sorts x (run (insertTree σ) x)

/-- The whole sort tree, by iterating `liftTree`. -/
noncomputable def sortTree : (n : ℕ) → Tree n
theorem sortTree_correct (n : ℕ) : Correct (α := ℕ) (sortTree n)
theorem sortTree_depth_le (n : ℕ) : depth (sortTree n) ≤ n * (Nat.clog 2 n + 1)

end SortBounds.Projects.SortTree
```

## Milestones

* **M0** `insertPerm` + evaluation lemmas + `rankOf` + `insertPerm_sorts`.
  (`insertPerm` is easiest as `Equiv.ofBijective` of the function
  `t ↦ if t = j then Fin.last n else Fin.castSucc (σ (Fin.predAbove j t))`;
  `Equiv.Perm.decomposeFin'`, `Fin.succAbove`, `Fin.predAbove`,
  `Fin.succAbove_predAbove`, `Fin.predAbove_succAbove` are the toolkit.)
* **M1** `insertTree` + `insertTree_correct` (binary search invariant: the true
  rank always lies in the active interval) + `insertTree_depth_le`.
* **M2** `sortTree` + `sortTree_correct` + `sortTree_depth_le`, using
  `Comparison/Bridge.lean`'s `liftTree`, `liftTree_correct`, `liftTree_depth_le`.
* **M3 (stretch)** instantiate `Projects/SN`: `S n ≤ n(⌈log₂ n⌉+1)` for all `n`,
  which with `SN.S_lower` gives `Θ(n log n)` in one model.

## Rules

Own only `SortBounds/Projects/SortTree/`. Do not edit `Comparison/Bridge.lean`
(if it needs a helper, prove it locally). `lake env lean` only, no `lake build`,
no git, no python helper scripts. No `sorry`.

## Prior art

Nothing machine-checked connects a decision-tree lower bound to an explicit
optimal-up-to-constant tree construction; Mathlib has `List.mergeSort`
correctness only. `S n` values: Knuth TAOCP §5.3.1.

## Log

* (empty)
