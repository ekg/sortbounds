/-
SortBounds/Radix.lean

Counting sort and LSD radix sort, formalised together with the properties that make them
interesting for a lower-bound discussion:

* stable counting sort by a key into `Fin b` (`countingSort`): it is a permutation of the input,
  it is sorted by the key, it is stable, and it preserves the length;
* LSD (least-significant-digit first) radix sort over `d` base-`b` digits (`radixSort`): it is a
  permutation of the input and it is nondecreasing for the lexicographic order on the digit vector
  read from digit `d-1` down to digit `0`;
* radix sort is *comparison free*: it takes no comparison on `α` at all, and the output depends
  only on the key vectors (cf. `radixSort_ignores_comparison`, `radixSort_keys_congr`);
* a cost model with `d` passes of `n + b` elementary operations and zero comparisons, which is why
  the `Ω(n log n)` comparison lower bound of `SortBounds.Comparison.Tree` does not apply to it.
-/
import Mathlib

namespace SortBounds

variable {α : Type}

/-! ### Stable counting sort by a key into `Fin b` -/

/-- The bucket predicate of counting sort: `bucketPred key i a` holds iff the key of `a` has
value `i`.  Counting sort only ever inspects *keys* (values in `Fin b`), never elements of `α`. -/
def bucketPred {b : ℕ} (key : α → Fin b) (i : ℕ) : α → Bool :=
  fun a => decide ((key a).val = i)

/-- The selection predicate "the key is exactly `i`". -/
def selPred {b : ℕ} (key : α → Fin b) (i : Fin b) : α → Bool :=
  fun a => decide (key a = i)

theorem bucketPred_eq_true {b : ℕ} {key : α → Fin b} {i : ℕ} {a : α} :
    bucketPred key i a = true ↔ (key a).val = i := by
  simp [bucketPred]

theorem key_eq_of_bucket {b : ℕ} {key : α → Fin b} {i : ℕ} {a c : α}
    (ha : bucketPred key i a = true) (hc : bucketPred key i c = true) : key a = key c :=
  Fin.ext (by rw [bucketPred_eq_true.mp ha, bucketPred_eq_true.mp hc])

/-- Stable counting sort: distribute the elements of `l` into the `b` buckets given by
`0, 1, …, b-1` (ascending) and concatenate them.  Elements are only moved, never compared, and
each bucket keeps the input order — hence the sort is stable. -/
def countingSort (b : ℕ) (key : α → Fin b) (l : List α) : List α :=
  (List.range b).flatMap (fun i => l.filter (bucketPred key i))

/-- Auxiliary form of `countingSort` used by its permutation proof, with an abstract `ℕ`-valued
key: the buckets of `l` indexed by the distinct values listed in `s` rearrange `l`. -/
theorem flatMap_bucket_perm (val : α → ℕ) :
    ∀ (s : List ℕ) (l : List α), s.Nodup → (∀ a ∈ l, val a ∈ s) →
      (s.flatMap (fun i => l.filter (fun a => decide (val a = i)))).Perm l
  | [], l, _, hl => by
      have hl' : l = [] := by
        rcases l with _ | ⟨a, l⟩
        · rfl
        · exact absurd (hl a (List.mem_cons_self ..)) (by simp)
      simp [hl']
  | i :: t, l, hnd, hl => by
      obtain ⟨hit, hndt⟩ := List.nodup_cons.mp hnd
      set l' : List α := l.filter (fun a => !decide (val a = i)) with hl'_def
      have hmem : ∀ a ∈ l', val a ∈ t := by
        intro a ha
        obtain ⟨hal, hnot⟩ := List.mem_filter.mp ha
        have hne : val a ≠ i := by simpa using hnot
        rcases List.mem_cons.mp (hl a hal) with h | h
        · exact absurd h hne
        · exact h
      have IH := flatMap_bucket_perm val t l' hndt hmem
      have hbucket : t.flatMap (fun j => l'.filter (fun a => decide (val a = j)))
          = t.flatMap (fun j => l.filter (fun a => decide (val a = j))) := by
        apply List.flatMap_congr
        intro j hj
        have hji : j ≠ i := fun h => hit (h ▸ hj)
        rw [hl'_def, List.filter_filter]
        apply List.filter_congr
        intro a _
        by_cases hv : val a = j
        · simp [hv, hji]
        · simp [hv]
      rw [List.flatMap_cons, ← hbucket]
      exact (List.Perm.append_left _ IH).trans
        (List.filter_append_perm (fun a => decide (val a = i)) l)

theorem countingSort_perm (b : ℕ) (key : α → Fin b) (l : List α) :
    (countingSort b key l).Perm l :=
  flatMap_bucket_perm (fun a => (key a).val) (List.range b) l List.nodup_range
    (fun a _ => List.mem_range.mpr (key a).isLt)

theorem countingSort_length (b : ℕ) (key : α → Fin b) (l : List α) :
    (countingSort b key l).length = l.length :=
  (countingSort_perm b key l).length_eq

/-- A list is pairwise related by a trivially true relation. -/
theorem pairwise_true (l : List α) : l.Pairwise (fun _ _ => True) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih => exact List.Pairwise.cons (fun _ _ => trivial) ih

/-- `Pairwise` for an increasing index list follows from the pointwise condition. -/
theorem pairwise_range_of_forall_lt {R : ℕ → ℕ → Prop} (h : ∀ i j, i < j → R i j) :
    ∀ n, (List.range n).Pairwise R
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.pairwise_append]
      refine ⟨pairwise_range_of_forall_lt h n, ?_, ?_⟩
      · exact List.Pairwise.cons (fun b hb => by simp at hb) List.Pairwise.nil
      · intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        exact h a b (List.mem_range.mp ha)

/-- Inside one bucket all keys are equal. -/
theorem pairwise_bucket_key_eq (b : ℕ) (key : α → Fin b) (i : ℕ) :
    ∀ l : List α, (l.filter (bucketPred key i)).Pairwise (fun a c => key a = key c)
  | [] => List.Pairwise.nil
  | a :: t => by
      rw [List.filter_cons]
      split
      · refine List.Pairwise.cons ?_ (pairwise_bucket_key_eq b key i t)
        intro c hc
        exact key_eq_of_bucket ‹bucketPred key i a = true› (List.mem_filter.mp hc).2
      · exact pairwise_bucket_key_eq b key i t

theorem pairwise_bucket_key_le (b : ℕ) (key : α → Fin b) (i : ℕ) (l : List α) :
    (l.filter (bucketPred key i)).Pairwise (fun a c => key a ≤ key c) :=
  (pairwise_bucket_key_eq b key i l).imp (fun h => le_of_eq h)

/-- Counting sort is sorted by the key. -/
theorem countingSort_sorted (b : ℕ) (key : α → Fin b) (l : List α) :
    (countingSort b key l).Pairwise (fun a c => key a ≤ key c) := by
  rw [countingSort, List.pairwise_flatMap]
  refine ⟨fun i _ => pairwise_bucket_key_le b key i l, ?_⟩
  apply pairwise_range_of_forall_lt
  intro i j hij x hx y hy
  have hx' : (key x).val = i := bucketPred_eq_true.mp (List.mem_filter.mp hx).2
  have hy' : (key y).val = j := bucketPred_eq_true.mp (List.mem_filter.mp hy).2
  rw [Fin.le_def]
  omega

/-- Counting sort refines any order `R` that already holds on `l`: its output is monotone for any
relation `S` that holds on same-key pairs and on pairs with increasing keys.  This is the engine
of the radix-sort correctness proof (where `R` is the order produced by the previous passes). -/
theorem countingSort_pairwise {b : ℕ} {key : α → Fin b} {l : List α} {R S : α → α → Prop}
    (hl : l.Pairwise R) (hsame : ∀ a c, key a = key c → R a c → S a c)
    (hlt : ∀ a c, key a < key c → S a c) :
    (countingSort b key l).Pairwise S := by
  rw [countingSort, List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_filter (R := S) (p := bucketPred key i)]
    exact hl.imp (fun (hR : R _ _) (hx : bucketPred key i _ = true)
      (hy : bucketPred key i _ = true) => hsame _ _ (key_eq_of_bucket hx hy) hR)
  · apply pairwise_range_of_forall_lt
    intro i j hij x hx y hy
    have hx' : (key x).val = i := bucketPred_eq_true.mp (List.mem_filter.mp hx).2
    have hy' : (key y).val = j := bucketPred_eq_true.mp (List.mem_filter.mp hy).2
    exact hlt x y (by rw [Fin.lt_def]; omega)

theorem filter_flatMap (s : List β) (f : β → List α) (q : α → Bool) :
    (s.flatMap f).filter q = s.flatMap (fun j => (f j).filter q) := by
  induction s with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, ih]

/-- In a `Nodup` index list, keeping the single bucket at `i` of a `flatMap` recovers that bucket. -/
theorem flatMap_ite_eq_of_nodup {s : List ℕ} (hnd : s.Nodup) {i : ℕ} (hi : i ∈ s)
    (f : ℕ → List α) :
    s.flatMap (fun j => if j = i then f j else []) = f i := by
  induction s with
  | nil => simp at hi
  | cons a t ih =>
      obtain ⟨hit, hndt⟩ := List.nodup_cons.mp hnd
      by_cases ha : a = i
      · have hit' : i ∉ t := by rw [← ha]; exact hit
        have hnil : t.flatMap (fun j => if j = i then f j else []) = [] := by
          rw [List.flatMap_eq_nil_iff]
          intro x hx
          have hxi : x ≠ i := fun h => hit' (h ▸ hx)
          simp [hxi]
        rw [List.flatMap_cons, ite_eq_left ha, hnil, List.append_nil, ha]
      · have hi' : i ∈ t := by
          rcases List.mem_cons.mp hi with h | h
          · exact absurd h.symm ha
          · exact h
        rw [List.flatMap_cons, ite_eq_right ha, List.nil_append]
        exact ih hndt hi'

/-- **Stability.** Restricting the sorted output to the elements with key `i` gives back exactly
the same elements in the same input order: counting sort never permutes elements with equal
keys.  (Equivalently, `countingSort_stable_sublist`: for every key value, the input order of the
elements with that key is a subsequence of the output.) -/
theorem countingSort_stable (b : ℕ) (key : α → Fin b) (l : List α) (i : Fin b) :
    (countingSort b key l).filter (selPred key i) = l.filter (selPred key i) := by
  rw [countingSort, filter_flatMap]
  have hb : ∀ j ∈ List.range b,
      (l.filter (bucketPred key j)).filter (selPred key i)
        = if j = i.val then l.filter (bucketPred key j) else [] := by
    intro j _
    by_cases hji : j = i.val
    · subst hji
      rw [ite_eq_left rfl, List.filter_eq_self]
      intro a ha
      rw [selPred, decide_eq_true_eq]
      exact Fin.ext (bucketPred_eq_true.mp (List.mem_filter.mp ha).2)
    · rw [ite_eq_right hji, List.filter_eq_nil_iff]
      intro a ha
      have hv : (key a).val = j := bucketPred_eq_true.mp (List.mem_filter.mp ha).2
      have hne : key a ≠ i := by
        intro h
        exact hji (by rw [← hv, h])
      simpa [selPred] using hne
  rw [List.flatMap_congr hb,
    flatMap_ite_eq_of_nodup List.nodup_range (List.mem_range.mpr i.isLt)
      (fun j => l.filter (bucketPred key j))]
  apply List.filter_congr
  intro a _
  by_cases h : key a = i
  · simp [bucketPred, selPred, h]
  · have hv : (key a).val ≠ i.val := fun hh => h (Fin.ext hh)
    simp [bucketPred, selPred, h, hv]

theorem countingSort_stable_sublist (b : ℕ) (key : α → Fin b) (l : List α) (i : Fin b) :
    (l.filter (selPred key i)).Sublist (countingSort b key l) := by
  rw [← countingSort_stable b key l i]
  exact List.filter_sublist

/-- The output of counting sort depends only on the key values of the elements of `l`. -/
theorem countingSort_keys_congr {b : ℕ} {key key' : α → Fin b} {l : List α}
    (h : ∀ a ∈ l, key a = key' a) : countingSort b key l = countingSort b key' l := by
  rw [countingSort, countingSort]
  apply List.flatMap_congr
  intro i _
  apply List.filter_congr
  intro a ha
  simp [bucketPred, h a ha]

/-! ### LSD radix sort -/

/-- Lexicographic order on the `k` least significant digits, most significant digit first:
`lowLt d b keys k a c` says that the digit vector `(a_{k-1}, …, a_0)` of `a` is lexicographically
smaller than the digit vector of `c`.  Digit `0` is the least significant digit. -/
def lowLt (d b : ℕ) (keys : α → Fin d → Fin b) : (k : ℕ) → k ≤ d → α → α → Prop
  | 0, _, _, _ => False
  | (k + 1), h, a, c =>
      (keys a ⟨k, Nat.lt_of_succ_le h⟩ < keys c ⟨k, Nat.lt_of_succ_le h⟩ ∨
        (keys a ⟨k, Nat.lt_of_succ_le h⟩ = keys c ⟨k, Nat.lt_of_succ_le h⟩ ∧
          lowLt d b keys k (Nat.le_of_succ_le h) a c))

theorem lowLt_succ {d b : ℕ} {keys : α → Fin d → Fin b} {k : ℕ} (h : k + 1 ≤ d) (a c : α) :
    lowLt d b keys (k + 1) h a c ↔
      (keys a ⟨k, Nat.lt_of_succ_le h⟩ < keys c ⟨k, Nat.lt_of_succ_le h⟩ ∨
        (keys a ⟨k, Nat.lt_of_succ_le h⟩ = keys c ⟨k, Nat.lt_of_succ_le h⟩ ∧
          lowLt d b keys k (Nat.le_of_succ_le h) a c)) := Iff.rfl

/-- Non-strict radix order: `a` is not above `c` in the lexicographic order on the `k` least
significant digits. -/
def lowLe (d b : ℕ) (keys : α → Fin d → Fin b) (k : ℕ) (hk : k ≤ d) (a c : α) : Prop :=
  ¬ lowLt d b keys k hk c a

/-- The radix-sort key order: lexicographic on the digits read from index `d-1` down to `0`
(digit `0` being the least significant). -/
def keyLt (d b : ℕ) (keys : α → Fin d → Fin b) (a c : α) : Prop := lowLt d b keys d le_rfl a c

/-- Non-strict form of `keyLt`; this is the sortedness relation of `radixSort_sorted`. -/
def keyLe (d b : ℕ) (keys : α → Fin d → Fin b) (a c : α) : Prop := lowLe d b keys d le_rfl a c

/-- One LSD pass: a stable counting sort on digit `i`. -/
def radixPass (d b : ℕ) (keys : α → Fin d → Fin b) (i : Fin d) (l : List α) : List α :=
  countingSort b (fun a => keys a i) l

/-- LSD radix sort in the form used for the correctness induction: `k` stable counting-sort passes
on the digits `0, 1, …, k-1`, least significant digit first. -/
def radixSortAux (d b : ℕ) (keys : α → Fin d → Fin b) : (k : ℕ) → k ≤ d → List α → List α
  | 0, _, l => l
  | (k + 1), h, l =>
      radixPass d b keys ⟨k, Nat.lt_of_succ_le h⟩ (radixSortAux d b keys k (Nat.le_of_succ_le h) l)

/-- LSD radix sort over `d` digits in base `b`: one stable counting-sort pass per digit, starting
with the least significant digit `0` and ending with digit `d-1`. -/
def radixSort (d b : ℕ) (keys : α → Fin d → Fin b) (l : List α) : List α :=
  radixSortAux d b keys d le_rfl l

theorem radixSortAux_perm (d b : ℕ) (keys : α → Fin d → Fin b) :
    ∀ (k : ℕ) (hk : k ≤ d) (l : List α), (radixSortAux d b keys k hk l).Perm l
  | 0, _, l => List.Perm.refl l
  | (k + 1), hk, l =>
      (countingSort_perm b (fun a => keys a ⟨k, Nat.lt_of_succ_le hk⟩) _).trans
        (radixSortAux_perm d b keys k (Nat.le_of_succ_le hk) l)

/-- **Radix sort is a permutation.** -/
theorem radixSort_perm (d b : ℕ) (keys : α → Fin d → Fin b) (l : List α) :
    (radixSort d b keys l).Perm l :=
  radixSortAux_perm d b keys d le_rfl l

theorem pairwise_radixPass {d b : ℕ} {keys : α → Fin d → Fin b} {i : Fin d} {l : List α}
    {R S : α → α → Prop} (hl : l.Pairwise R)
    (hsame : ∀ a c, keys a i = keys c i → R a c → S a c)
    (hlt : ∀ a c, keys a i < keys c i → S a c) :
    (radixPass d b keys i l).Pairwise S :=
  countingSort_pairwise hl hsame hlt

/-- The invariant of the radix-sort induction: after the passes on the digits `0, …, k-1` the list
is sorted for the lexicographic order on those `k` digits.  No hypothesis on the input is needed. -/
theorem radixSortAux_pairwise (d b : ℕ) (keys : α → Fin d → Fin b) :
    ∀ (k : ℕ) (hk : k ≤ d) (l : List α),
      (radixSortAux d b keys k hk l).Pairwise (lowLe d b keys k hk)
  | 0, hk, l => by
      have hNil : radixSortAux d b keys 0 hk l = l := rfl
      rw [hNil]
      clear hNil
      induction l with
      | nil => exact List.Pairwise.nil
      | cons a t ih => exact List.Pairwise.cons (fun _ _ => not_false) ih
  | (k + 1), hk, l => by
      have hstep : radixSortAux d b keys (k + 1) hk l
          = radixPass d b keys ⟨k, Nat.lt_of_succ_le hk⟩
              (radixSortAux d b keys k (Nat.le_of_succ_le hk) l) := rfl
      rw [hstep]
      refine pairwise_radixPass (radixSortAux_pairwise d b keys k (Nat.le_of_succ_le hk) l)
        ?_ ?_
      · intro a c heq hR hcon
        rcases (lowLt_succ (k := k) hk c a).mp hcon with h | ⟨-, hltk⟩
        · rw [heq] at h
          exact absurd h (lt_irrefl _)
        · exact hR hltk
      · intro a c hlt hcon
        rcases (lowLt_succ (k := k) hk c a).mp hcon with h | ⟨heq', -⟩
        · exact absurd hlt (not_lt.mpr (le_of_lt h))
        · exact absurd heq'.symm (ne_of_lt hlt)

/-- **Radix sort is sorted**: the output is nondecreasing for the lexicographic order `keyLe` on
the digit vector read from digit `d-1` down to digit `0`. -/
theorem radixSort_sorted (d b : ℕ) (keys : α → Fin d → Fin b) (l : List α) :
    (radixSort d b keys l).Pairwise (keyLe d b keys) :=
  radixSortAux_pairwise d b keys d le_rfl l

/-- Totality of the radix order on the `k` least significant digits: `a` is below `c`, `c` is
below `a`, or the digits below `k` agree. -/
theorem lowLt_trichotomy (d b : ℕ) (keys : α → Fin d → Fin b) :
    ∀ (k : ℕ) (hk : k ≤ d) (a c : α),
      lowLt d b keys k hk a c ∨ lowLt d b keys k hk c a ∨
        (∀ i : Fin d, i.val < k → keys a i = keys c i)
  | 0, _, _, _ => Or.inr (Or.inr (fun i hi => absurd hi (Nat.not_lt_zero _)))
  | (k + 1), hk, a, c => by
      rcases lt_trichotomy (keys a ⟨k, Nat.lt_of_succ_le hk⟩) (keys c ⟨k, Nat.lt_of_succ_le hk⟩)
        with h | h | h
      · exact Or.inl ((lowLt_succ hk a c).mpr (Or.inl h))
      · rcases lowLt_trichotomy d b keys k (Nat.le_of_succ_le hk) a c with h1 | h1 | h1
        · exact Or.inl ((lowLt_succ hk a c).mpr (Or.inr ⟨h, h1⟩))
        · exact Or.inr (Or.inl ((lowLt_succ hk c a).mpr (Or.inr ⟨h.symm, h1⟩)))
        · refine Or.inr (Or.inr fun i hi => ?_)
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
          · exact h1 i hlt
          · have hi' : i = ⟨k, Nat.lt_of_succ_le hk⟩ := Fin.ext heq
            rw [hi']
            exact h
      · exact Or.inr (Or.inl ((lowLt_succ hk c a).mpr (Or.inl h)))

/-- **No ties except between identical keys**: two elements with different key vectors are always
strictly ordered by `keyLt`, in exactly one direction. -/
theorem keyLt_trichotomy (d b : ℕ) (keys : α → Fin d → Fin b) {a c : α}
    (h : keys a ≠ keys c) : keyLt d b keys a c ∨ keyLt d b keys c a := by
  rcases lowLt_trichotomy d b keys d le_rfl a c with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd (funext fun i => h1 i i.isLt) h

theorem pairwise_keyLt_of_pairwise_keyLe {d b : ℕ} {keys : α → Fin d → Fin b} :
    ∀ {l : List α}, (l.map keys).Nodup → l.Pairwise (keyLe d b keys) →
      l.Pairwise (keyLt d b keys)
  | [], _, _ => List.Pairwise.nil
  | a :: t, hnd, h => by
      obtain ⟨ha, hndt⟩ := List.nodup_cons.mp hnd
      obtain ⟨hhead, hpair⟩ := List.pairwise_cons.mp h
      refine List.Pairwise.cons ?_ (pairwise_keyLt_of_pairwise_keyLe hndt hpair)
      intro c hc
      have hne : keys a ≠ keys c := fun heq => ha (List.mem_map.mpr ⟨c, hc, heq.symm⟩)
      rcases keyLt_trichotomy d b keys hne with hlt | hlt
      · exact hlt
      · exact absurd hlt (hhead c hc)

/-- **Completeness.** If the keys of the input are pairwise distinct, radix sort is a *complete*
sort: the output is strictly increasing for the key order, so no ties are left except between
elements with identical keys.  (The key space has `b ^ d` elements, see `card_key_vectors`, so
such keys exist as soon as `l.length ≤ b ^ d`.) -/
theorem radixSort_strict_sorted (d b : ℕ) (keys : α → Fin d → Fin b) {l : List α}
    (hnd : (l.map keys).Nodup) : (radixSort d b keys l).Pairwise (keyLt d b keys) :=
  pairwise_keyLt_of_pairwise_keyLe
    ((List.Perm.nodup_iff ((radixSort_perm d b keys l).map keys)).mpr hnd)
    (radixSort_sorted d b keys l)

/-- There are `b ^ d` key vectors, i.e. `n ≤ b ^ d` is exactly the condition under which `n`
elements can be given pairwise distinct keys. -/
theorem card_key_vectors (d b : ℕ) : Fintype.card (Fin d → Fin b) = b ^ d := by
  simp

/-! ### Radix sort makes no comparisons -/

/-- Radix sort together with a comparison oracle on `α`.  The oracle is never consulted; that it
can be anything is the content of `radixSort_ignores_comparison`. -/
def radixSortWith (_cmp : α → α → Bool) (d b : ℕ) (keys : α → Fin d → Fin b)
    (l : List α) : List α :=
  radixSort d b keys l

/-- **Radix sort is comparison free**: the output does not depend on the comparison oracle, because
no comparison on `α` is ever consulted. -/
theorem radixSort_ignores_comparison (cmp cmp' : α → α → Bool) (d b : ℕ)
    (keys : α → Fin d → Fin b) (l : List α) :
    radixSortWith cmp d b keys l = radixSortWith cmp' d b keys l := rfl

theorem radixSortAux_keys_congr (d b : ℕ) {keys keys' : α → Fin d → Fin b} :
    ∀ (k : ℕ) (hk : k ≤ d) (l : List α), (∀ a ∈ l, keys a = keys' a) →
      radixSortAux d b keys k hk l = radixSortAux d b keys' k hk l
  | 0, _, _, _ => rfl
  | (k + 1), hk, l, h => by
      have hstep : radixSortAux d b keys (k + 1) hk l
          = radixPass d b keys ⟨k, Nat.lt_of_succ_le hk⟩
              (radixSortAux d b keys k (Nat.le_of_succ_le hk) l) := rfl
      have hstep' : radixSortAux d b keys' (k + 1) hk l
          = radixPass d b keys' ⟨k, Nat.lt_of_succ_le hk⟩
              (radixSortAux d b keys' k (Nat.le_of_succ_le hk) l) := rfl
      rw [hstep, hstep', radixSortAux_keys_congr d b k (Nat.le_of_succ_le hk) l h]
      apply countingSort_keys_congr
      intro a ha
      exact congrFun (h a ((radixSortAux_perm d b keys' k (Nat.le_of_succ_le hk) l).subset ha))
        ⟨k, Nat.lt_of_succ_le hk⟩

/-- The output of radix sort depends only on the key vectors of the elements of `l`, never on the
elements themselves: no comparison on `α` is made. -/
theorem radixSort_keys_congr (d b : ℕ) {keys keys' : α → Fin d → Fin b} {l : List α}
    (h : ∀ a ∈ l, keys a = keys' a) : radixSort d b keys l = radixSort d b keys' l :=
  radixSortAux_keys_congr d b d le_rfl l h

/-! ### Cost model -/

/-- Elementary operations of one counting pass over `n` items with `b` buckets: `n` key readings
and placements plus `b` bucket initialisations/emptyings. -/
def passCost (n b : ℕ) : ℕ := n + b

/-- Total cost of an LSD radix sort: `d` passes of `n + b` elementary operations. -/
def radixCost (d n b : ℕ) : ℕ := d * (n + b)

/-- Comparisons on `α` made by radix sort: none, reflected by the absence of any comparison term in
`radixCost` (cf. `radixSort_ignores_comparison`). -/
def radixComparisons (_d _n _b : ℕ) : ℕ := 0

/-- `d` passes, each of `n + b` elementary operations. -/
theorem radixCost_eq_passes (d n b : ℕ) :
    radixCost d n b = ((List.range d).map (fun _ => passCost n b)).sum := by
  simp [radixCost, passCost, List.map_const', List.sum_replicate]

/-- Radix sort makes zero comparisons on `α`. -/
theorem radix_cost_zero_comparisons (d n b : ℕ) : radixComparisons d n b = 0 := rfl

/-! ### Executable sanity checks -/

/-- The two base-10 digits of a natural number, digit `0` being the least significant one. -/
def twoDigitsB10 (n : ℕ) (i : Fin 2) : Fin 10 :=
  if i.val = 0 then ⟨n % 10, by omega⟩ else ⟨n / 10 % 10, by omega⟩

/-- Least significant digit first: sorting by the last digit and then by the first yields the
correct two-digit order. -/
example : radixSort 2 10 twoDigitsB10 [12, 3] = [3, 12] := by decide

/-- A larger two-digit base-10 instance. -/
example : radixSort 2 10 twoDigitsB10 [12, 21, 3, 100, 99] = [100, 3, 12, 21, 99] := by decide

/-- Stability: `22` and `12` have the same last digit and keep their input order. -/
example :
    radixSort 1 10 (fun (n : ℕ) (_ : Fin 1) => (⟨n % 10, by omega⟩ : Fin 10)) [22, 12, 3]
      = [22, 12, 3] := by
  decide

/-- With no digits to process, radix sort does nothing. -/
example : radixSort 0 10 (fun (_ : ℕ) (i : Fin 0) => i.elim0) [3, 1, 2] = [3, 1, 2] := rfl

#eval radixSort 2 10 twoDigitsB10 [12, 21, 3, 100, 99]

end SortBounds
