/-
SortBounds/Projects/FjTree/Basic.lean

**The machinery of a sequenced decision tree.**  Merge-insertion is not a single
substitution: it sorts the winners, then inserts one loser at a time, and each
insertion has a *different* search window.  What is needed is a way to chain decision
trees on the *same* index set, where each stage hands the next one a **state**: the
current arrangement of the positions, as an `Equiv.Perm (Fin n)`.

The state is the whole point.  `run` of a stage tree returns a permutation; if the
first `s` slots of that permutation list the positions in increasing order of value,
the arrangement is "the sorted chain followed by whatever is left", and the next stage
can ask "does a new element belong here?" by comparing against slots of the
arrangement.

Contents:

* `substTree` — substitute a family `Perm (Fin n) → Tree n` into the leaves of `Tree n`,
  with `run_substTree`, `depth_substTree_le` and the correctness transfer
  `substTree_correct` (the analogue of `Comparison/Bridge.liftTree` at a fixed index).
* `imageTree` — re-index a tree along an injection `Fin m → Fin n`, relabelling leaves;
  this is how the recursive call on the `n/2` winners is embedded (`run_imageTree`,
  `depth_imageTree`).
* `insertAt` — the state after inserting the element in slot `s` at rank `j` of the
  chain: slots `j … s-1` shift up, the rest of the arrangement is untouched.
* `ChainSorted` — "the first `s` slots of the state are sorted by value", the invariant
  every stage has to preserve.
* `rankAt` — the rank of the element in slot `s` inside the chain, as the number of
  chain elements below it; `lt_rankAt_iff` is the bridge between values and indices.
* `binIns` — the binary search for that rank in the window `[0, hi)`; `binIns_run`
  says the leaf reached is `insertAt (rankAt ·)`, and `binIns_depth_le` gives the depth
  `⌈log₂ (hi+1)⌉` (one comparison halves the window).
* `insSeq` — a whole insertion phase: insert the elements in slots `s, s+1, …, s+cnt-1`,
  each into a window given by `w`, with `insSeq_depth_le` and `insSeq_sorts`.

`M0` at the bottom is the sanity check of the whole API: binary insertion sort, i.e.
`insSeq` with the full chain as window, giving `insTree` with `insTree_correct` and
`insTree_depth_le : depth ≤ n * (⌈log₂ n⌉ + 1)` — `Projects/SortTree` reproved through
the substitution API.
-/
import SortBounds.Comparison.Bridge
import SortBounds.Projects.SN.Basic
import SortBounds.Projects.SortTree.Main

namespace SortBounds.Projects.FjTree

open SortBounds

variable {n : ℕ}

/-! ### Substitution at a fixed index -/

/-- Substitute a family of trees into the leaves of `t`: at a leaf holding the
permutation `σ`, continue with the tree `f σ`.  (Same index — unlike
`Comparison/Bridge.liftTree`, the substituted tree keeps the `n` positions and only the
*state* changes.) -/
def substTree : Tree n → (Equiv.Perm (Fin n) → Tree n) → Tree n
  | .leaf σ, f => f σ
  | .node i j l r, f => .node i j (substTree l f) (substTree r f)

section Subst

variable {α : Type*} [LinearOrder α]

@[simp]
theorem run_substTree (t : Tree n) (f : Equiv.Perm (Fin n) → Tree n) (x : Fin n → α) :
    run (substTree t f) x = run (f (run t x)) x := by
  induction t with
  | leaf σ => rfl
  | node i j l r ihl ihr =>
    show (if x i < x j then run (substTree l f) x else run (substTree r f) x)
      = run (f (if x i < x j then run l x else run r x)) x
    by_cases h : x i < x j
    · rw [ite_eq_left h, ite_eq_left h, ihl]
    · rw [ite_eq_right h, ite_eq_right h, ihr]

end Subst

/-- Depth of a substitution: the stage's depth plus a uniform bound on the
continuation. -/
theorem depth_substTree_le (t : Tree n) (f : Equiv.Perm (Fin n) → Tree n) (B : ℕ)
    (hB : ∀ σ, depth (f σ) ≤ B) : depth (substTree t f) ≤ depth t + B := by
  induction t with
  | leaf σ =>
    show depth (f σ) ≤ 0 + B
    simpa using hB σ
  | node i j l r ihl ihr =>
    show 1 + max (depth (substTree l f)) (depth (substTree r f))
      ≤ 1 + max (depth l) (depth r) + B
    omega

/-- **Correctness transfers through a stage**: the stage establishes the invariant `P`
on the state it leaves behind, and the continuation sorts from every state satisfying
`P`. -/
theorem substTree_correct {P : Equiv.Perm (Fin n) → (Fin n → ℕ) → Prop} {t : Tree n}
    (ht : ∀ x : Fin n → ℕ, Function.Injective x → P (run t x) x)
    {f : Equiv.Perm (Fin n) → Tree n}
    (hf : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℕ), Function.Injective x → P σ x →
      Sorts x (run (f σ) x)) :
    Correct (α := ℕ) (substTree t f) := by
  intro x hx
  rw [run_substTree]
  exact hf _ x hx (ht x hx)

/-! ### Re-indexing a tree along an injection -/

/-- Re-index a tree along `e : Fin m → Fin n`, relabelling its leaves with `L`.  The
tree asks only comparisons between the positions in the image of `e`. -/
def imageTree {m : ℕ} (e : Fin m → Fin n) (L : Equiv.Perm (Fin m) → Equiv.Perm (Fin n)) :
    Tree m → Tree n
  | .leaf τ => .leaf (L τ)
  | .node i j l r => .node (e i) (e j) (imageTree e L l) (imageTree e L r)

theorem depth_imageTree {m : ℕ} (e : Fin m → Fin n)
    (L : Equiv.Perm (Fin m) → Equiv.Perm (Fin n)) (t : Tree m) :
    depth (imageTree e L t) = depth t := by
  induction t with
  | leaf τ => rfl
  | node i j l r ihl ihr =>
    show 1 + max (depth (imageTree e L l)) (depth (imageTree e L r)) = 1 + max (depth l) (depth r)
    rw [ihl, ihr]

theorem run_imageTree {m : ℕ} {α : Type*} [LinearOrder α] (e : Fin m → Fin n)
    (L : Equiv.Perm (Fin m) → Equiv.Perm (Fin n)) (t : Tree m) (x : Fin n → α) :
    run (imageTree e L t) x = L (run t (fun i => x (e i))) := by
  induction t with
  | leaf τ => rfl
  | node i j l r ihl ihr =>
    show (if x (e i) < x (e j) then run (imageTree e L l) x else run (imageTree e L r) x)
      = L (if x (e i) < x (e j) then run l (fun i => x (e i)) else run r (fun i => x (e i)))
    by_cases h : x (e i) < x (e j)
    · rw [ite_eq_left h, ite_eq_left h, ihl]
    · rw [ite_eq_right h, ite_eq_right h, ihr]

/-! ### Inserting the element of slot `s` at rank `j` of the chain

The state is an arrangement `σ : Equiv.Perm (Fin n)`: slot `k` holds the position
`σ k`.  Slots `0 … s-1` are the sorted chain; slot `s` holds the element about to be
inserted.  Inserting it at rank `j` (so that it ends up between slots `j-1` and `j`)
sends slot `k` to old slot `k` (for `k < j`), to old slot `s` (for `k = j`), to old slot
`k-1` (for `j < k ≤ s`) and leaves slots `> s` alone; this is the slot map
`insertFun`. -/

/-- The chain slot that a newly inserted element pushes up by one. -/
def predFin {n : ℕ} (k : Fin n) : Fin n := ⟨k.val - 1, by have := k.isLt; omega⟩

@[simp]
theorem predFin_val {n : ℕ} (k : Fin n) : (predFin k).val = k.val - 1 := rfl

/-- The slot map of an insertion: new slot `k` reads old slot `insertFun j s k`. -/
def insertFun (j q : ℕ) (hqn : q < n) (k : Fin n) : Fin n :=
  if k.val < j then k
  else if k.val = j then ⟨q, hqn⟩
  else if k.val ≤ q then predFin k
  else k

theorem insertFun_injective (j q : ℕ) (hjq : j ≤ q) (hqn : q < n) :
    Function.Injective (insertFun (n := n) j q hqn) := by
  intro a b hab
  simp only [insertFun] at hab
  split_ifs at hab <;>
    exact Fin.ext (by
      have h := congrArg Fin.val hab
      try simp only [Fin.val_mk, predFin_val] at h
      omega)

/-- The slot map of an insertion, as a permutation of the slots. -/
noncomputable def insertPerm (j q : ℕ) (hjq : j ≤ q) (hqn : q < n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (insertFun j q hqn)
    ⟨insertFun_injective j q hjq hqn,
      Finite.surjective_of_injective (insertFun_injective j q hjq hqn)⟩

theorem insertPerm_apply (j q : ℕ) (hjq : j ≤ q) (hqn : q < n) (k : Fin n) :
    insertPerm j q hjq hqn k = insertFun j q hqn k := rfl

/-- **The state after an insertion**: slot `k` of the new arrangement reads old slot
`insertFun j s k`. -/
noncomputable def insertAt (j q : ℕ) (hjq : j ≤ q) (hqn : q < n)
    (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  σ * insertPerm j q hjq hqn

theorem insertAt_apply_lt (j q : ℕ) (hjq : j ≤ q) (hqn : q < n) (σ : Equiv.Perm (Fin n))
    {k : Fin n} (h : k.val < j) : insertAt j q hjq hqn σ k = σ k := by
  show σ (insertPerm j q hjq hqn k) = σ k
  rw [insertPerm_apply]
  simp only [insertFun, if_pos h]

theorem insertAt_apply_eq (j q : ℕ) (hjq : j ≤ q) (hqn : q < n) (σ : Equiv.Perm (Fin n))
    {k : Fin n} (h : k.val = j) : insertAt j q hjq hqn σ k = σ ⟨q, hqn⟩ := by
  show σ (insertPerm j q hjq hqn k) = σ ⟨q, hqn⟩
  rw [insertPerm_apply]
  have hk : k = ⟨j, by omega⟩ := Fin.ext h
  rw [hk]
  simp [insertFun]

theorem insertAt_apply_mid (j q : ℕ) (hjq : j ≤ q) (hqn : q < n) (σ : Equiv.Perm (Fin n))
    {k : Fin n} (h1 : j < k.val) (h2 : k.val ≤ q) :
    insertAt j q hjq hqn σ k = σ (predFin k) := by
  show σ (insertPerm j q hjq hqn k) = σ (predFin k)
  rw [insertPerm_apply]
  simp only [insertFun, if_neg (show ¬ (k.val < j) by omega),
    if_neg (show ¬ (k.val = j) by omega), if_pos h2]

theorem insertAt_apply_gt (j q : ℕ) (hjq : j ≤ q) (hqn : q < n) (σ : Equiv.Perm (Fin n))
    {k : Fin n} (h1 : q < k.val) : insertAt j q hjq hqn σ k = σ k := by
  show σ (insertPerm j q hjq hqn k) = σ k
  rw [insertPerm_apply]
  simp only [insertFun, if_neg (show ¬ (k.val < j) by omega),
    if_neg (show ¬ (k.val = j) by omega), if_neg (show ¬ (k.val ≤ q) by omega)]

/-! ### The sorted chain -/

/-- The invariant of every stage: the first `s` slots of the state are sorted by value. -/
def ChainSorted (x : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (s : ℕ) : Prop :=
  ∀ i j : Fin n, (i : ℕ) < s → (j : ℕ) < s → i < j → x (σ i) < x (σ j)

theorem ChainSorted.mono (x : Fin n → ℕ) {σ : Equiv.Perm (Fin n)} {s s' : ℕ} (h : s' ≤ s)
    (H : ChainSorted x σ s) : ChainSorted x σ s' :=
  fun i j hi hj hij => H i j (by omega) (by omega) hij

theorem ChainSorted.le (x : Fin n → ℕ) {σ : Equiv.Perm (Fin n)} {s : ℕ}
    (H : ChainSorted x σ s) {i j : Fin n} (hi : (i : ℕ) < s) (hj : (j : ℕ) < s) (h : i ≤ j) :
    x (σ i) ≤ x (σ j) := by
  rcases lt_or_eq_of_le h with h' | h'
  · exact le_of_lt (H i j hi hj h')
  · rw [h']

/-! ### The rank of the pending element

The chain is the prefix of slots `[0, c)`; the element to insert sits in slot `q ≥ c`
(it is somewhere in the pending block, in merge-insertion not necessarily first).  Its
*rank* is the number of chain elements below it — the slot it has to be inserted at. -/

/-- The chain slots below the element of slot `q`. -/
noncomputable def rankSet (x : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (c : ℕ) (q : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun k => k.val < c ∧ x (σ k) < x (σ q)

/-- **The rank of the element of slot `q` in the chain**: the number of chain elements
below it, i.e. the slot it has to be inserted at. -/
noncomputable def rankAt (x : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (c : ℕ) (q : Fin n) : ℕ :=
  (rankSet x σ c q).card

theorem card_filter_val_lt_le (c : ℕ) :
    (Finset.univ.filter (fun k : Fin n => k.val < c)).card ≤ c := by
  rcases le_or_gt c n with h | h
  · rw [SortBounds.Projects.SortTree.card_filter_val_lt (n := n) (m := c) h]
  · have h2 : (Finset.univ.filter (fun k : Fin n => k.val < c)).card ≤ n := by
      simpa using Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
        (p := fun k : Fin n => k.val < c)
    omega

theorem rankAt_le (x : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (c : ℕ) (q : Fin n) :
    rankAt x σ c q ≤ c := by
  have hsub : rankSet x σ c q ⊆ Finset.univ.filter (fun k : Fin n => k.val < c) := by
    intro k hk
    simp only [rankSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.1
  exact le_trans (Finset.card_le_card hsub) (card_filter_val_lt_le c)

theorem mem_rankSet_iff (x : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (c : ℕ) (q k : Fin n) :
    k ∈ rankSet x σ c q ↔ k.val < c ∧ x (σ k) < x (σ q) := by
  simp [rankSet]

/-- `rankSet` is an initial segment of the chain. -/
theorem rankSet_down {x : Fin n → ℕ} {σ : Equiv.Perm (Fin n)} {c : ℕ} {q : Fin n}
    (hchain : ChainSorted x σ c) {k k' : Fin n} (hk : k ∈ rankSet x σ c q) (h : k' ≤ k) :
    k' ∈ rankSet x σ c q := by
  rw [mem_rankSet_iff] at hk ⊢
  refine ⟨by omega, ?_⟩
  rcases lt_or_eq_of_le h with h' | h'
  · exact lt_trans (hchain k' k (by omega) hk.1 h') hk.2
  · simpa [h'] using hk.2

/-- **The bridge between values and indices**: in a sorted chain, the chain slot `k` is
below the element of slot `q` exactly when `k < rankAt`. -/
theorem lt_rankAt_iff {x : Fin n → ℕ} {σ : Equiv.Perm (Fin n)} {c : ℕ} {q : Fin n}
    (hchain : ChainSorted x σ c) (k : Fin n) (hk : k.val < c) :
    x (σ k) < x (σ q) ↔ k.val < rankAt x σ c q := by
  have hcard := rankAt_le x σ c q
  have hmn : k.val ≤ n := by have := k.isLt; omega
  constructor
  · intro hv
    have hmem : k ∈ rankSet x σ c q := (mem_rankSet_iff _ _ _ _ _).2 ⟨hk, hv⟩
    have hsub : (Finset.univ.filter fun j : Fin n => j.val < k.val + 1) ⊆ rankSet x σ c q := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact rankSet_down hchain hmem (by omega)
    have h1 : k.val + 1 ≤ rankAt x σ c q := by
      have h2 := Finset.card_le_card hsub
      rwa [SortBounds.Projects.SortTree.card_filter_val_lt (n := n) (m := k.val + 1)
        (by omega)] at h2
    omega
  · intro hlt
    by_contra hnot
    have hsub : rankSet x σ c q ⊆ Finset.univ.filter (fun j : Fin n => j.val < k.val) := by
      intro j hj
      rw [mem_rankSet_iff] at hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hcon
      rcases lt_or_ge k.val j.val with h' | h'
      · exact hnot (lt_trans (hchain k j hk hj.1 (by omega)) hj.2)
      · have hjk : k = j := Fin.ext (by omega)
        exact hnot (by rw [hjk]; exact hj.2)
    have h1 : rankAt x σ c q ≤ k.val := by
      have h2 := Finset.card_le_card hsub
      rwa [SortBounds.Projects.SortTree.card_filter_val_lt (n := n) (m := k.val) hmn] at h2
    omega

/-- **Insertion keeps the chain sorted**: inserting the element of slot `q` at its rank
`rankAt` extends a sorted chain of length `c ≤ q` by one sorted element. -/
theorem chainSorted_insertAt {x : Fin n → ℕ} {σ : Equiv.Perm (Fin n)} {c : ℕ} {q : Fin n}
    (hcq : c ≤ q.val) (hx : Function.Injective x) (hchain : ChainSorted x σ c) :
    ChainSorted x (insertAt (rankAt x σ c q) q.val
      (by have := rankAt_le x σ c q; omega) q.isLt σ) (c + 1) := by
  have hcard := rankAt_le x σ c q
  have hrle : rankAt x σ c q ≤ q.val := by omega
  have hbelow : ∀ k : Fin n, k.val < rankAt x σ c q → x (σ k) < x (σ q) :=
    fun k hk => (lt_rankAt_iff hchain k (by omega)).2 hk
  have habove : ∀ k : Fin n, rankAt x σ c q ≤ k.val → k.val < c → x (σ q) < x (σ k) := by
    intro k hk hks
    have hne : x (σ q) ≠ x (σ k) := by
      intro hc
      have h₂ : q.val = k.val := congrArg Fin.val (σ.injective (hx hc) : q = k)
      omega
    refine lt_of_le_of_ne (le_of_not_gt fun hc => ?_) hne
    exact absurd ((lt_rankAt_iff hchain k hks).1 hc) (by omega)
  intro i j hi hj hij
  have hi' : i.val < c := by omega
  have hj' : j.val ≤ c := by omega
  have hstep : ∀ (k : Fin n), rankAt x σ c q < k.val → k.val ≤ q.val →
      insertAt (rankAt x σ c q) q.val hrle q.isLt σ k = σ (predFin k) :=
    fun k h1 h2 => insertAt_apply_mid _ _ hrle q.isLt σ h1 h2
  rcases lt_trichotomy i.val (rankAt x σ c q) with h1 | h1 | h1
  · rw [insertAt_apply_lt (rankAt x σ c q) q.val hrle q.isLt σ h1]
    rcases lt_trichotomy j.val (rankAt x σ c q) with h2 | h2 | h2
    · rw [insertAt_apply_lt (rankAt x σ c q) q.val hrle q.isLt σ h2]
      exact hchain i j hi' (by omega) hij
    · rw [insertAt_apply_eq (rankAt x σ c q) q.val hrle q.isLt σ h2]
      exact hbelow i h1
    · rw [hstep j h2 (by omega)]
      refine hchain i (predFin j) hi' ?_ ?_
      · show (predFin j : ℕ) < c
        simp only [predFin_val]; omega
      · show (i : ℕ) < (predFin j : ℕ)
        simp only [predFin_val]; omega
  · rw [insertAt_apply_eq (rankAt x σ c q) q.val hrle q.isLt σ h1]
    rcases lt_trichotomy j.val (rankAt x σ c q) with h2 | h2 | h2
    · omega
    · omega
    · rw [hstep j h2 (by omega)]
      refine habove (predFin j) ?_ ?_
      · show rankAt x σ c q ≤ (predFin j : ℕ)
        simp only [predFin_val]; omega
      · show (predFin j : ℕ) < c
        simp only [predFin_val]; omega
  · rw [hstep i h1 (by omega)]
    rcases lt_trichotomy j.val (rankAt x σ c q) with h2 | h2 | h2
    · omega
    · omega
    · rw [hstep j h2 (by omega)]
      refine hchain (predFin i) (predFin j) ?_ ?_ ?_
      · show (predFin i : ℕ) < c
        simp only [predFin_val]; omega
      · show (predFin j : ℕ) < c
        simp only [predFin_val]; omega
      · show (predFin i : ℕ) < (predFin j : ℕ)
        simp only [predFin_val]; omega

/-! ### Binary search for the rank

The window is the prefix `[lo, hi)` of the chain (`hi ≤ c ≤ q`); the element of slot `q`
can only reach slot `hi` if `hi` is an upper bound for its rank, which is what the caller
has to supply (`binIns_run`). -/

/-- The midpoint of the window `[lo, hi)`. -/
def midOf (lo hi : ℕ) : ℕ := lo + (hi - lo) / 2

theorem le_midOf (lo hi : ℕ) : lo ≤ midOf lo hi := Nat.le_add_right _ _

theorem midOf_lt {lo hi : ℕ} (h : lo < hi) : midOf lo hi < hi := by
  have h1 : (hi - lo) / 2 < hi - lo := Nat.div_lt_self (by omega) (by norm_num)
  simp only [midOf]
  omega

/-- The midpoint of the window, as a chain slot. -/
def midFin (lo hi : ℕ) (h : midOf lo hi < n) : Fin n := ⟨midOf lo hi, h⟩

@[simp]
theorem midFin_val (lo hi : ℕ) (h : midOf lo hi < n) : (midFin lo hi h).val = midOf lo hi := rfl

/-- **The binary search tree**: find the rank of the element of slot `q` inside the
window `[lo, hi)` (an upper bound for the rank), one comparison against the midpoint per
step, and hand the state after the insertion to `next`. -/
noncomputable def binIns : (fuel lo hi c q : ℕ) → (hqn : q < n) → (hcq : c ≤ q) →
    (hhi : hi ≤ c) → Equiv.Perm (Fin n) → (Equiv.Perm (Fin n) → Tree n) → Tree n
  | 0, _, hi, c, q, hqn, hcq, hhi, σ, next => next (insertAt hi q (by omega) hqn σ)
  | fuel + 1, lo, hi, c, q, hqn, hcq, hhi, σ, next =>
    if h : lo < hi then
      Tree.node (σ ⟨q, hqn⟩) (σ (midFin lo hi (by have := midOf_lt h; have := hhi; omega)))
        (binIns fuel lo (midOf lo hi) c q hqn hcq
          (by have := midOf_lt h; omega) σ next)
        (binIns fuel (midOf lo hi + 1) hi c q hqn hcq hhi σ next)
    else next (insertAt hi q (by omega) hqn σ)

/-- One step of the search halves the window. -/
theorem one_add_clog_half_le {len : ℕ} (h : 1 ≤ len) :
    1 + Nat.clog 2 (len / 2 + 1) ≤ Nat.clog 2 (len + 1) :=
  SortBounds.Projects.SortTree.one_add_clog_half_le h

/-- The second half of the window is no larger than the first. -/
theorem half_le {lo hi : ℕ} (h : lo < hi) :
    hi - (midOf lo hi + 1) + 1 ≤ (hi - lo) / 2 + 1 := by
  have h1 := le_midOf lo hi
  simp only [midOf]
  omega

/-- The first half of the window has size `(hi-lo)/2 + 1`. -/
theorem half_eq {lo hi : ℕ} (h : lo < hi) :
    midOf lo hi - lo + 1 = (hi - lo) / 2 + 1 := by
  have h1 := le_midOf lo hi
  simp only [midOf]
  omega

/-- **Depth of the binary search**: each comparison halves the window, so the depth is
`⌈log₂ (hi - lo + 1)⌉` plus the continuation's depth. -/
theorem binIns_depth_le : ∀ (fuel lo hi c q : ℕ) (hqn : q < n) (hcq : c ≤ q) (hhi : hi ≤ c)
    (σ : Equiv.Perm (Fin n)) (next : Equiv.Perm (Fin n) → Tree n) (B : ℕ),
    (∀ σ, depth (next σ) ≤ B) → hi - lo ≤ fuel →
    depth (binIns fuel lo hi c q hqn hcq hhi σ next) ≤ Nat.clog 2 (hi - lo + 1) + B
  | 0, lo, hi, c, q, hqn, hcq, hhi, σ, next, B, hB, hm => by
    simp only [binIns]
    have hle : hi ≤ lo := by omega
    have h1 := hB (insertAt hi q (by omega) hqn σ)
    omega
  | fuel + 1, lo, hi, c, q, hqn, hcq, hhi, σ, next, B, hB, hm => by
    simp only [binIns]
    split_ifs with h
    · simp only [depth]
      have hm1 : midOf lo hi - lo ≤ fuel := by have := midOf_lt h; omega
      have hm2 : hi - (midOf lo hi + 1) ≤ fuel := by have := le_midOf lo hi; omega
      have hmi : midOf lo hi ≤ c := by have := midOf_lt h; omega
      have h1 := binIns_depth_le fuel lo (midOf lo hi) c q hqn hcq hmi σ next B hB hm1
      have h2 := binIns_depth_le fuel (midOf lo hi + 1) hi c q hqn hcq hhi σ next B hB hm2
      have hlen : 1 ≤ hi - lo := by omega
      have hstep := one_add_clog_half_le hlen
      have h3 : Nat.clog 2 (midOf lo hi - lo + 1) = Nat.clog 2 ((hi - lo) / 2 + 1) := by
        rw [half_eq h]
      have h4 : Nat.clog 2 (hi - (midOf lo hi + 1) + 1) ≤ Nat.clog 2 ((hi - lo) / 2 + 1) :=
        Nat.clog_mono_right 2 (half_le h)
      have hmax : max (depth (binIns fuel lo (midOf lo hi) c q hqn hcq hmi σ next))
          (depth (binIns fuel (midOf lo hi + 1) hi c q hqn hcq hhi σ next))
          ≤ Nat.clog 2 ((hi - lo) / 2 + 1) + B := by
        refine max_le ?_ ?_
        · rw [h3] at h1; exact h1
        · exact le_trans h2 (Nat.add_le_add_right h4 B)
      omega
    · have hle : hi ≤ lo := by omega
      have h1 := hB (insertAt hi q (by omega) hqn σ)
      omega

/-- **The search finds the rank**: if the rank of the element of slot `q` lies in the
window `[lo, hi)` (and `hi` bounds it), the search reaches the state with the element
inserted at its true rank. -/
theorem binIns_run : ∀ (fuel lo hi c q : ℕ) (hqn : q < n) (hcq : c ≤ q) (hhi : hi ≤ c),
    hi - lo ≤ fuel →
    ∀ (σ : Equiv.Perm (Fin n)) (next : Equiv.Perm (Fin n) → Tree n) (x : Fin n → ℕ),
    Function.Injective x → ChainSorted x σ c →
    lo ≤ rankAt x σ c ⟨q, hqn⟩ → rankAt x σ c ⟨q, hqn⟩ ≤ hi →
    run (binIns fuel lo hi c q hqn hcq hhi σ next) x
      = run (next (insertAt (rankAt x σ c ⟨q, hqn⟩) q
          (by have := rankAt_le x σ c ⟨q, hqn⟩; omega) hqn σ)) x
  | 0, lo, hi, c, q, hqn, hcq, hhi, hm, σ, next, x, hx, hchain, hlo, hhi' => by
    simp only [binIns]
    have heq : hi = rankAt x σ c ⟨q, hqn⟩ := by omega
    subst heq
    rfl
  | fuel + 1, lo, hi, c, q, hqn, hcq, hhi, hm, σ, next, x, hx, hchain, hlo, hhi' => by
    simp only [binIns]
    split_ifs with h
    · have hmid : midOf lo hi < c := by have := midOf_lt h; omega
      have hmidn : midOf lo hi < n := by have := midOf_lt h; omega
      have hmidv : (midFin lo hi hmidn).val < c := by
        simp only [midFin_val]; exact hmid
      rw [run]
      by_cases hlt : x (σ ⟨q, hqn⟩) < x (σ (midFin lo hi hmidn))
      · rw [ite_eq_left hlt]
        have hrank : rankAt x σ c ⟨q, hqn⟩ ≤ midOf lo hi := by
          by_contra hc
          have hc' : (midFin lo hi hmidn).val < rankAt x σ c ⟨q, hqn⟩ := by
            simp only [midFin_val]; omega
          exact absurd ((lt_rankAt_iff hchain (midFin lo hi hmidn) hmidv).2 hc')
            (not_lt.2 (le_of_lt hlt))
        exact binIns_run fuel lo (midOf lo hi) c q hqn hcq
          (by have := midOf_lt h; omega) (by have := midOf_lt h; omega) σ next x hx hchain hlo hrank
      · rw [ite_eq_right hlt]
        have hge : x (σ (midFin lo hi hmidn)) < x (σ ⟨q, hqn⟩) := by
          refine lt_of_le_of_ne (le_of_not_gt hlt) ?_
          intro hc
          have h2 : midFin lo hi hmidn = (⟨q, hqn⟩ : Fin n) := σ.injective (hx hc)
          have h3 : midOf lo hi = q := by simpa using congrArg Fin.val h2
          omega
        have hrank : midOf lo hi + 1 ≤ rankAt x σ c ⟨q, hqn⟩ := by
          have h2 := (lt_rankAt_iff hchain (midFin lo hi hmidn) hmidv).1 hge
          simp only [midFin_val] at h2
          omega
        exact binIns_run fuel (midOf lo hi + 1) hi c q hqn hcq hhi
          (by have := le_midOf lo hi; omega) σ next x hx hchain hrank hhi'
    · have heq : hi = rankAt x σ c ⟨q, hqn⟩ := by omega
      subst heq
      rfl

/-! ### A whole insertion phase -/

/-- Insert the elements of slots `s, s+1, …, n-1`, each into the window `[0, w ·)` of the
chain, then continue with `next`.  The phase fills the arrangement exactly, hence the
equation `s + cnt = n`. -/
noncomputable def insSeq (w : ℕ → ℕ) (hw : ∀ t, w t ≤ t)
    (next : Equiv.Perm (Fin n) → Tree n) :
    (cnt s : ℕ) → s + cnt = n → Equiv.Perm (Fin n) → Tree n
  | 0, _, _, σ => next σ
  | cnt + 1, s, h, σ =>
    binIns (w s) 0 (w s) s s (by omega) le_rfl (hw s) σ
      (insSeq w hw next cnt (s + 1) (by omega))

/-- **Depth of an insertion phase**: `cnt` searches, each of depth at most
`⌈log₂ (w s + 1)⌉ ≤ A`. -/
theorem insSeq_depth_le (w : ℕ → ℕ) (hw : ∀ t, w t ≤ t)
    (next : Equiv.Perm (Fin n) → Tree n) (B : ℕ) (hB : ∀ σ, depth (next σ) ≤ B) (A : ℕ)
    (hA : ∀ t, t ≤ n → Nat.clog 2 (w t + 1) ≤ A) :
    ∀ (cnt s : ℕ) (h : s + cnt = n) (σ : Equiv.Perm (Fin n)),
      depth (insSeq w hw next cnt s h σ) ≤ cnt * A + B := by
  intro cnt
  induction cnt with
  | zero =>
    intro s h σ
    simp only [insSeq]
    have := hB σ
    omega
  | succ cnt ih =>
    intro s h σ
    have hsm : s < n := by omega
    have hrec : ∀ σ' : Equiv.Perm (Fin n),
        depth (insSeq w hw next cnt (s + 1) (by omega) σ') ≤ cnt * A + B :=
      fun σ' => ih (s + 1) (by omega) σ'
    have hstep := binIns_depth_le (w s) 0 (w s) s s hsm le_rfl (hw s) σ
      (insSeq w hw next cnt (s + 1) (by omega)) (cnt * A + B) hrec (by omega)
    calc depth (insSeq w hw next (cnt + 1) s h σ)
        = depth (binIns (w s) 0 (w s) s s hsm le_rfl (hw s) σ
            (insSeq w hw next cnt (s + 1) (by omega))) := by simp only [insSeq]
      _ ≤ Nat.clog 2 (w s - 0 + 1) + (cnt * A + B) := hstep
      _ = Nat.clog 2 (w s + 1) + (cnt * A + B) := by rw [Nat.sub_zero]
      _ ≤ A + (cnt * A + B) := Nat.add_le_add_right (hA s (by omega)) _
      _ = (cnt + 1) * A + B := by ring

/-- **Correctness of an insertion phase**: the invariant `P` says the state's chain is
sorted, its rank is inside the window, and one step keeps `P`; then the phase sorts. -/
theorem insSeq_sorts (w : ℕ → ℕ) (hw : ∀ t, w t ≤ t)
    (next : Equiv.Perm (Fin n) → Tree n)
    {P : Equiv.Perm (Fin n) → ℕ → Prop} {x : Fin n → ℕ} (hx : Function.Injective x)
    (hchain : ∀ (σ : Equiv.Perm (Fin n)) (s : ℕ), P σ s → ChainSorted x σ s)
    (hrank : ∀ (σ : Equiv.Perm (Fin n)) (s : ℕ) (hs : s < n),
      P σ s → rankAt x σ s ⟨s, hs⟩ ≤ w s)
    (hstep : ∀ (σ : Equiv.Perm (Fin n)) (s : ℕ) (hs : s < n),
      P σ s → P (insertAt (rankAt x σ s ⟨s, hs⟩) s
        (by have := rankAt_le x σ s ⟨s, hs⟩; omega) hs σ) (s + 1))
    (hsorts : ∀ σ : Equiv.Perm (Fin n), P σ n → Sorts x (run (next σ) x)) :
    ∀ (cnt s : ℕ) (h : s + cnt = n) (σ : Equiv.Perm (Fin n)), P σ s →
      Sorts x (run (insSeq w hw next cnt s h σ) x)
  | 0, s, h, σ, hP => by
    simp only [insSeq]
    exact hsorts σ (h ▸ hP)
  | cnt + 1, s, h, σ, hP => by
    have hs : s < n := by omega
    have hP' := hstep σ s hs hP
    have hrec := insSeq_sorts w hw next hx hchain hrank hstep hsorts cnt (s + 1) (by omega)
      (insertAt (rankAt x σ s ⟨s, hs⟩) s
        (by have := rankAt_le x σ s ⟨s, hs⟩; omega) hs σ) hP'
    have hrun := binIns_run (w s) 0 (w s) s s hs le_rfl (hw s) (by omega) σ
      (insSeq w hw next cnt (s + 1) (by omega)) x hx (hchain σ s hP) (Nat.zero_le _)
      (hrank σ s hs hP)
    simp only [insSeq]
    rw [hrun]
    exact hrec

/-! ### An insertion phase with the item slot above the chain

`insSeq` fixes the item slot at the chain tip (`s` is both the chain length and the slot of
the item), which is what a plain insertion sort does.  A Jacobsthal batch needs the
*opposite*: the item *slot* `q` stays put while the chain grows underneath it, so that one
slot serves the whole batch (after each insertion the next item of the batch is shifted up
into `q`).  `insSeqAt` is the transfer lemma for that shape of phase, and
`insSeqAt_run` is the invariant argument: the state after the whole phase is some state
satisfying `P` at the final chain length. -/

/-- Insert `cnt` items, all taken from slot `q` (which stays fixed while the chain grows),
each searched for in the window `[0, w)`, then continue with `next`.  The chain starts with
`c ≤ q` slots and the last insertion sees `c + cnt - 1 ≤ q`. -/
noncomputable def insSeqAt (q w : ℕ) (hqn : q < n)
    (next : Equiv.Perm (Fin n) → Tree n) :
    (cnt c : ℕ) → c + cnt ≤ q + 1 → w ≤ c → Equiv.Perm (Fin n) → Tree n
  | 0, _, _, _, σ => next σ
  | cnt + 1, c, hq, hw, σ =>
    binIns w 0 w c q hqn (by omega) hw σ
      (insSeqAt q w hqn next cnt (c + 1) (by omega) (by omega))

/-- **Correctness of a phase whose item slot is fixed**: `P` is an invariant of the phase
units — it stays true while the chain grows, and it bounds the rank of the item in slot `q`
by the window `w`.  Then the phase ends in some state satisfying `P` at the final chain
length `c + cnt`. -/
theorem insSeqAt_run (q w : ℕ) (hqn : q < n) (hwq : w ≤ q)
    (next : Equiv.Perm (Fin n) → Tree n)
    {P : Equiv.Perm (Fin n) → ℕ → Prop} {x : Fin n → ℕ} (hx : Function.Injective x)
    (hchain : ∀ (σ : Equiv.Perm (Fin n)) (c : ℕ), P σ c → ChainSorted x σ c)
    (hrank : ∀ (σ : Equiv.Perm (Fin n)) (c : ℕ), c < n → P σ c →
      rankAt x σ c ⟨q, hqn⟩ ≤ w)
    (hstep : ∀ (σ : Equiv.Perm (Fin n)) (c : ℕ) (hcn : c < n) (hP : P σ c),
      P (insertAt (rankAt x σ c ⟨q, hqn⟩) q
        (by have h := hrank σ c hcn hP; omega) hqn σ) (c + 1)) :
    ∀ (cnt c : ℕ) (hq : c + cnt ≤ q + 1) (hw : w ≤ c) (σ : Equiv.Perm (Fin n)), P σ c →
      ∃ σ' : Equiv.Perm (Fin n),
        run (insSeqAt q w hqn next cnt c hq hw σ) x = run (next σ') x ∧ P σ' (c + cnt)
  | 0, c, _, _, σ, hP => ⟨σ, rfl, hP⟩
  | cnt + 1, c, hq, hw, σ, hP => by
    have hcn : c < n := by omega
    have hcq : c ≤ q := by omega
    have hrun := binIns_run w 0 w c q hqn hcq hw (by omega) σ
      (insSeqAt q w hqn next cnt (c + 1) (by omega) (by omega)) x hx
      (hchain σ c hP) (Nat.zero_le _) (hrank σ c hcn hP)
    have hstep' : P (insertAt (rankAt x σ c ⟨q, hqn⟩) q
        (by have h := hrank σ c hcn hP; omega) hqn σ) (c + 1) := hstep σ c hcn hP
    obtain ⟨σ', hrun', hP'⟩ := insSeqAt_run q w hqn hwq next hx hchain hrank hstep cnt (c + 1)
      (by omega) (by omega) _ hstep'
    exact ⟨σ', by rw [insSeqAt, hrun, hrun'],
      by have h : c + (cnt + 1) = c + 1 + cnt := by omega
         rw [h]; exact hP'⟩

/-! ### M0: binary insertion sort through the API

Sanity check of the machinery: insert the elements in slots `1, …, n-1` one by one,
each into the whole chain (`w = id`).  This is `Projects/SortTree`'s `sortTree`
reproved as a sequenced substitution. -/

/-- A chain of length `1` is sorted: it holds the single slot `0`. -/
theorem chainSorted_one (x : Fin n → ℕ) : ChainSorted x (1 : Equiv.Perm (Fin n)) 1 := by
  intro i j hi hj hij
  exact absurd hij (by omega)

/-- **Binary insertion sort, as a sequenced decision tree.** -/
noncomputable def insTree : (n : ℕ) → Tree n
  | 0 => Tree.leaf 1
  | n + 1 =>
    insSeq (n := n + 1) (fun t => t) (fun _ => le_rfl) (fun σ => Tree.leaf σ) n 1 (by omega) 1

theorem insTree_correct (n : ℕ) : Correct (α := ℕ) (insTree n) := by
  cases n with
  | zero =>
    intro x _ a _
    exact a.elim0
  | succ m =>
    intro x hx
    have h := insSeq_sorts (n := m + 1) (fun t => t) (fun _ => le_rfl)
      (fun σ => Tree.leaf σ) (P := fun σ s => ChainSorted x σ s) hx
      (fun σ s hP => hP) (fun σ s hs hP => rankAt_le x σ s ⟨s, hs⟩)
      (fun σ s hs hP => chainSorted_insertAt (le_rfl : s ≤ s) hx hP)
      (fun σ hP => fun i j hij => hP i j i.isLt j.isLt hij)
      m 1 (by omega) 1 (chainSorted_one x)
    simpa only [insTree] using h

/-- **Depth of binary insertion sort** through the API: `m` insertions, each into a
window of at most `m + 1` slots, i.e. `⌈log₂ (m+2)⌉ ≤ ⌈log₂ (m+1)⌉ + 1` comparisons. -/
theorem insTree_depth_le (n : ℕ) : depth (insTree n) ≤ n * (Nat.clog 2 n + 1) := by
  cases n with
  | zero => simp [insTree, depth]
  | succ m =>
    have h := insSeq_depth_le (n := m + 1) (fun t => t) (fun _ => le_rfl)
      (fun σ => Tree.leaf σ) 0 (fun _ => by simp [depth]) (Nat.clog 2 (m + 2))
      (fun t ht => Nat.clog_mono_right 2 (by omega))
      m 1 (by omega) 1
    have h2 : m * Nat.clog 2 (m + 2) ≤ (m + 1) * (Nat.clog 2 (m + 1) + 1) := by
      have h3 : Nat.clog 2 (m + 2) ≤ Nat.clog 2 (m + 1) + 1 := by
        have h4 : Nat.clog 2 (m + 1 + 1) ≤ Nat.clog 2 (m + 1) + 1 := by
          rw [Nat.clog_le_iff_le_pow (b := 2) (by norm_num) (x := m + 1 + 1)
            (y := Nat.clog 2 (m + 1) + 1)]
          have h5 : 2 ^ (Nat.clog 2 (m + 1) + 1) = 2 * 2 ^ Nat.clog 2 (m + 1) := by ring
          rw [h5]
          have h7 : m + 1 ≤ 2 ^ Nat.clog 2 (m + 1) :=
            (Nat.clog_le_iff_le_pow (b := 2) (by norm_num)).1 le_rfl
          omega
        simpa using h4
      calc m * Nat.clog 2 (m + 2) ≤ m * (Nat.clog 2 (m + 1) + 1) := Nat.mul_le_mul_left m h3
        _ ≤ (m + 1) * (Nat.clog 2 (m + 1) + 1) := Nat.mul_le_mul_right _ (by omega)
    simp only [insTree, Nat.sub_zero]
    calc depth (insSeq (n := m + 1) (fun t => t) (fun _ => le_rfl) (fun σ => Tree.leaf σ)
          m 1 (by omega) 1)
        ≤ m * Nat.clog 2 (m + 2) + 0 := h
      _ ≤ (m + 1) * (Nat.clog 2 (m + 1) + 1) := by omega

end SortBounds.Projects.FjTree
