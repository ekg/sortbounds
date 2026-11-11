/-
SortBounds/Projects/FordJohnson/MergeInsertion.lean

Milestone **M1** of the `FordJohnson` lane: the merge-insertion algorithm of Ford and
Johnson with a certified comparison count.

The algorithm is the 1959 one:

1. compare the elements two at a time (`l₁` with `l₂`, `l₃` with `l₄`, …), keeping the
   winner and the loser of each pair and setting aside the unpaired element of an
   odd-length input — `⌊n/2⌋` comparisons;
2. sort the winners recursively;
3. insert the losers one at a time into the chain of winners by binary insertion;
4. insert the unpaired element, if any, into the final chain.

Every comparison is spent inside `insertCount` or inside the pairing step, so the returned
number is a genuine comparison count.  What this file proves:

* `fjSort_perm`     — `fjSort` returns a permutation of its input;
* `fjSort_sorted`   — the output is sorted;
* `fjSort_count_le` — `fjSort` uses at most `fjCount n` comparisons on `n` elements, where
  `fjCount` is the stated recurrence of this particular schedule.

`fjCount` is *an* upper bound for the schedule implemented here, not the optimal `F(n)` of
the literature.  Step 3 above inserts each loser into the whole chain, while classical
merge-insertion inserts it only into the part preceding the loser's partner (the losers are
then visited in Jacobsthal order, and only `⌈log₂ (3t/4)⌉` comparisons are needed for the
`t`-th one).  Reaching that bound needs the position of a loser's partner in the chain,
which is the remaining work of this lane; see `README.md`.
-/
import SortBounds.Projects.FordJohnson.Insertion

namespace SortBounds.Projects.FordJohnson

variable {α : Type*}

/-! ### Pairing the elements -/

/-- `pairUp l` compares the elements of `l` two at a time (`x₁` with `x₂`, `x₃` with `x₄`,
…) and returns the winners, the losers — aligned with the winners, the `k`-th loser being
the partner of the `k`-th winner — and the unpaired element when `l` has odd length. -/
def pairUp [LinearOrder α] : List α → List α × List α × Option α
  | [] => ([], [], none)
  | [x] => ([], [], some x)
  | x :: y :: rest =>
    if y ≤ x then
      let p := pairUp rest
      (x :: p.1, y :: p.2.1, p.2.2)
    else
      let p := pairUp rest
      (y :: p.1, x :: p.2.1, p.2.2)

/-- The recursion step of `pairUp` when the first element wins its pair. -/
theorem pairUp_cons_of_le [LinearOrder α] (x y : α) (rest : List α) (h : y ≤ x) :
    pairUp (x :: y :: rest) =
      (x :: (pairUp rest).1, y :: (pairUp rest).2.1, (pairUp rest).2.2) := by
  simp only [pairUp, h, ite_true]

/-- The recursion step of `pairUp` when the second element wins its pair. -/
theorem pairUp_cons_of_not_le [LinearOrder α] (x y : α) (rest : List α) (h : ¬ y ≤ x) :
    pairUp (x :: y :: rest) =
      (y :: (pairUp rest).1, x :: (pairUp rest).2.1, (pairUp rest).2.2) := by
  simp only [pairUp, h, ite_false]

/-- Pairing consumes the whole list: winners, losers and the unpaired element together are
a permutation of the input. -/
theorem pairUp_perm [LinearOrder α] (l : List α) :
    l.Perm ((pairUp l).1 ++ ((pairUp l).2.1 ++ (pairUp l).2.2.toList)) := by
  induction l using pairUp.induct with
  | case1 => simp [pairUp]
  | case2 x => simp [pairUp]
  | case3 x y rest hyx ih =>
    rw [pairUp_cons_of_le x y rest hyx]
    simp only [List.cons_append]
    refine ((ih.cons y).cons x).trans ?_
    exact (List.perm_middle (l₁ := (pairUp rest).1)
      (l₂ := (pairUp rest).2.1 ++ (pairUp rest).2.2.toList)).symm.cons x
  | case4 x y rest hnyx ih =>
    rw [pairUp_cons_of_not_le x y rest hnyx]
    simp only [List.cons_append]
    refine ((ih.cons y).cons x).trans ?_
    refine (List.Perm.swap' y x (List.Perm.refl _)).trans ?_
    exact (List.perm_middle (l₁ := (pairUp rest).1)
      (l₂ := (pairUp rest).2.1 ++ (pairUp rest).2.2.toList)).symm.cons y

/-- The number of pairs is `⌊n/2⌋`. -/
theorem pairUp_fst_length [LinearOrder α] (l : List α) : (pairUp l).1.length = l.length / 2 := by
  induction l using pairUp.induct with
  | case1 => simp [pairUp]
  | case2 x => simp [pairUp]
  | case3 x y rest hyx ih =>
    rw [pairUp_cons_of_le x y rest hyx]
    simp only [List.length_cons]
    rw [ih]
    omega
  | case4 x y rest hnyx ih =>
    rw [pairUp_cons_of_not_le x y rest hnyx]
    simp only [List.length_cons]
    rw [ih]
    omega

/-- The losers are as many as the winners. -/
theorem pairUp_snd_fst_length [LinearOrder α] (l : List α) :
    (pairUp l).2.1.length = l.length / 2 := by
  induction l using pairUp.induct with
  | case1 => simp [pairUp]
  | case2 x => simp [pairUp]
  | case3 x y rest hyx ih =>
    rw [pairUp_cons_of_le x y rest hyx]
    simp only [List.length_cons]
    rw [ih]
    omega
  | case4 x y rest hnyx ih =>
    rw [pairUp_cons_of_not_le x y rest hnyx]
    simp only [List.length_cons]
    rw [ih]
    omega

/-! ### Inserting a list of elements, counted -/

/-- Insert each element of `xs` into the list `l` by binary insertion, adding up the
comparison counts. -/
def insertAll [LinearOrder α] : List α → List α → ℕ × List α
  | [], l => (0, l)
  | x :: rest, l =>
    let r := insertCount x l
    let r' := insertAll rest r.2
    (r.1 + r'.1, r'.2)

/-- Binary insertion adds exactly one element. -/
theorem insertCount_length [LinearOrder α] (x : α) (l : List α) :
    (insertCount x l).2.length = l.length + 1 :=
  (insertCount_perm x l).length_eq.trans (by simp)

/-- `insertAll` inserts a permutation of the elements it was given. -/
theorem insertAll_perm [LinearOrder α] (xs : List α) (l : List α) :
    (insertAll xs l).2.Perm (l ++ xs) := by
  induction xs generalizing l with
  | nil => simp [insertAll]
  | cons x rest ih =>
    simp only [insertAll]
    refine (ih (insertCount x l).2).trans ?_
    refine ((insertCount_perm x l).append_right rest).trans ?_
    exact (List.perm_middle (l₁ := l) (l₂ := rest)).symm

/-- `insertAll` preserves the length, adding `xs.length`. -/
theorem insertAll_length [LinearOrder α] (xs : List α) (l : List α) :
    (insertAll xs l).2.length = l.length + xs.length := by
  rw [(insertAll_perm xs l).length_eq, List.length_append]

/-- `insertAll` preserves sortedness. -/
theorem insertAll_sorted [LinearOrder α] (xs : List α) (l : List α) (h : l.Pairwise (· ≤ ·)) :
    (insertAll xs l).2.Pairwise (· ≤ ·) := by
  induction xs generalizing l with
  | nil => simpa [insertAll] using h
  | cons x rest ih =>
    simp only [insertAll]
    exact ih _ (insertCount_sorted x l h)

/-- `insertAllCost k n` bounds the comparisons spent inserting `n` elements one after
another into a chain that starts with `k` elements: each insertion costs at most
`⌈log₂ (k+1)⌉` and lengthens the chain by one. -/
def insertAllCost (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.clog 2 (k + 1) + insertAllCost (k + 1) n

/-- **The cost of a batch of binary insertions.**  If the chain has `l.length` elements
before the batch starts, inserting `xs` costs at most `insertAllCost l.length xs.length`:
insertions never reorder the chain, so the `t`-th one meets `l.length + t` elements. -/
theorem insertAll_count [LinearOrder α] (xs : List α) (l : List α) :
    (insertAll xs l).1 ≤ insertAllCost l.length xs.length := by
  induction xs generalizing l with
  | nil => simp [insertAll, insertAllCost]
  | cons x rest ih =>
    simp only [insertAll, List.length_cons, insertAllCost]
    have h1 : (insertCount x l).1 ≤ Nat.clog 2 (l.length + 1) := insertCount_count x l
    have h2 : (insertAll rest (insertCount x l).2).1 ≤ insertAllCost (l.length + 1) rest.length := by
      have := ih (insertCount x l).2
      rwa [insertCount_length] at this
    omega

/-! ### Merge-insertion -/

/-- **Merge-insertion (Ford–Johnson), counted.**  Pair up the elements, sort the winners
recursively, then insert all the losers and the unpaired element by binary insertion. -/
def fjSort [LinearOrder α] (l : List α) : ℕ × List α :=
  if l.length < 2 then (0, l)
  else
    let p := pairUp l
    let r := fjSort p.1
    let r₁ := insertAll p.2.1 r.2
    let r₂ :=
      match p.2.2 with
      | none => (0, r₁.2)
      | some x => insertCount x r₁.2
    (p.1.length + r.1 + r₁.1 + r₂.1, r₂.2)
termination_by l.length
decreasing_by
  have hlen := pairUp_fst_length l
  omega

/-- Any list of length at most one is sorted. -/
theorem pairwise_of_length_le_one {R : α → α → Prop} {l : List α} (h : l.length ≤ 1) :
    l.Pairwise R := by
  match l, h with
  | [], _ => exact List.Pairwise.nil
  | [_], _ => simp

/-- **Merge-insertion sorts.**  The output is a permutation of the input. -/
theorem fjSort_perm [LinearOrder α] (l : List α) : (fjSort l).2.Perm l := by
  induction l using fjSort.induct with
  | case1 l hlt =>
    rw [fjSort]
    simp only [hlt, ite_true]
    exact List.Perm.refl l
  | case2 l hge p ih =>
    rw [fjSort]
    simp only [hge, ite_false]
    have hins : List.Perm (insertAll (pairUp l).2.1 (fjSort (pairUp l).1).2).2
        ((fjSort (pairUp l).1).2 ++ (pairUp l).2.1) := insertAll_perm _ _
    have hrec : List.Perm (fjSort (pairUp l).1).2 (pairUp l).1 := ih
    cases hx : (pairUp l).2.2 with
    | none =>
      have hpair := pairUp_perm l
      simp only [hx, Option.toList_none, List.append_nil] at hpair
      exact (hins.trans (hrec.append_right _)).trans hpair.symm
    | some x =>
      have hpair := pairUp_perm l
      simp only [hx, Option.toList_some] at hpair
      refine (insertCount_perm x _).trans ?_
      refine (List.Perm.cons x (hins.trans (hrec.append_right _))).trans ?_
      refine ((List.perm_append_singleton x _).symm).trans ?_
      rw [List.append_assoc]
      exact hpair.symm

/-- **Merge-insertion returns a sorted list.** -/
theorem fjSort_sorted [LinearOrder α] (l : List α) : (fjSort l).2.Pairwise (· ≤ ·) := by
  induction l using fjSort.induct with
  | case1 l hlt =>
    rw [fjSort]
    simp only [hlt, ite_true]
    exact pairwise_of_length_le_one (by omega)
  | case2 l hge p ih =>
    rw [fjSort]
    simp only [hge, ite_false]
    have hins : (insertAll (pairUp l).2.1 (fjSort (pairUp l).1).2).2.Pairwise (· ≤ ·) :=
      insertAll_sorted _ _ ih
    cases hx : (pairUp l).2.2 with
    | none => exact hins
    | some x => exact insertCount_sorted x _ hins

/-! ### The comparison count of merge-insertion -/

/-- The comparisons spent inserting `m` losers one after another into a chain of winners
that starts with `m` elements. -/
def loserCost (m : ℕ) : ℕ := insertAllCost m m

/-- **`F(n)`: the comparison count of merge-insertion on `n` elements.**  `n/2` comparisons
to pair the elements, the recursive call on the `n/2` winners, one binary insertion per
loser (`loserCost (n/2)`), and one binary insertion for the unpaired element when `n` is
odd. -/
def fjCount (n : ℕ) : ℕ :=
  if n < 2 then 0
  else
    n / 2 + fjCount (n / 2) + loserCost (n / 2)
      + (if n % 2 = 1 then Nat.clog 2 (2 * (n / 2) + 1) else 0)
termination_by n
decreasing_by
  omega

/-- **The count of merge-insertion.**  On a list of `n` elements `fjSort` spends at most
`fjCount n` comparisons. -/
theorem fjSort_count_le [LinearOrder α] (l : List α) : (fjSort l).1 ≤ fjCount l.length := by
  suffices H : ∀ k (l : List α), l.length = k → (fjSort l).1 ≤ fjCount l.length from
    H l.length l rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro l hl
    rw [fjCount]
    split
    · -- at most one element: nothing to compare
      rw [fjSort]
      split
      · simp
      · rename_i hge
        omega
    · rename_i hge
      rw [fjSort]
      simp only [hge, ite_false]
      -- the search space: winners and losers both have `l.length / 2` elements
      have hm : (pairUp l).1.length = l.length / 2 := pairUp_fst_length l
      have hml : (pairUp l).2.1.length = l.length / 2 := pairUp_snd_fst_length l
      have hrec : (fjSort (pairUp l).1).1 ≤ fjCount ((pairUp l).1.length) :=
        ih _ (by rw [hm]; omega) _ rfl
      have hchain : (fjSort (pairUp l).1).2.length = (pairUp l).1.length :=
        (fjSort_perm (pairUp l).1).length_eq
      have hins := insertAll_count (pairUp l).2.1 (fjSort (pairUp l).1).2
      rw [hchain, hm, hml] at hins
      -- the unpaired element: inserted into a chain of `2 * (l.length / 2)` elements
      have hfin : (match (pairUp l).2.2 with
          | none => (0 : ℕ)
          | some x => (insertCount x (insertAll (pairUp l).2.1 (fjSort (pairUp l).1).2).2).1)
          ≤ (if l.length % 2 = 1 then Nat.clog 2 (2 * (l.length / 2) + 1) else 0) := by
        have hpar : l.length =
            (pairUp l).1.length + ((pairUp l).2.1.length + (pairUp l).2.2.toList.length) := by
          rw [← List.length_append, ← List.length_append]
          exact (pairUp_perm l).length_eq
        rw [hm, hml] at hpar
        have hlen : (insertAll (pairUp l).2.1 (fjSort (pairUp l).1).2).2.length =
            2 * (l.length / 2) := by
          rw [insertAll_length, hchain, hm, hml]
          omega
        cases hx : (pairUp l).2.2 with
        | none =>
          simp only [hx, Option.toList_none, List.length_nil, Nat.add_zero] at hpar
          have hmod : l.length % 2 = 0 := by omega
          simp only [hmod]
          norm_num
        | some x =>
          simp only [hx, Option.toList_some, List.length_cons, List.length_nil] at hpar
          have hmod : l.length % 2 = 1 := by omega
          simp only [hmod, ite_true]
          have hc := insertCount_count x (insertAll (pairUp l).2.1 (fjSort (pairUp l).1).2).2
          rw [hlen] at hc
          exact hc
      rw [hm] at hrec ⊢
      simp only [loserCost]
      cases hx : (pairUp l).2.2 with
      | none =>
        simp only [hx] at hfin ⊢
        omega
      | some x =>
        simp only [hx] at hfin ⊢
        omega

end SortBounds.Projects.FordJohnson
