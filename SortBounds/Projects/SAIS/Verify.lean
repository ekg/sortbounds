/-
SortBounds/Projects/SAIS/Verify.lean

**Linear-time verification of a suffix array** (milestone `M1c`).

The check.  Given a candidate `sa : List ℕ` — a duplicate-free list of `s.length` valid
positions, i.e. a permutation of `0, …, s.length - 1` (`IsSaCandidate`) — run down the list and
check that each neighbouring pair of suffixes is strictly increasing,
`verifyStep s sa p = Ordering.lt`.  The comparison at step `p` is `cmpFrom` supplied with the
LCP-array entry `saLcp s sa p` between the two suffixes (the entry is *free*: the cost model of
`LCP.lean` charges comparisons, not the construction of lower bounds).

What is proved.

* `verifyStep_eq` — each step is a correct comparison (`cmpFrom_lcp_advance`), and
  `inspectCount_verifyStep` — each step inspects exactly one position (`inspectCount_lcp`).
  So the check never looks at a character twice.
* `sum_inspectCount_verify` — **the total is exactly `sa.length - 1` inspections**: one per
  neighbouring pair, linear in the length of the array.
* `compare_lt_of_verify` — the check is *complete*: if every neighbouring pair is strictly
  increasing then so is every pair of ranks, so a candidate that passes orders the suffixes
  lexicographically.  (This is `compare_lt_of_chain` from `Chain.lean`: strict increase of
  neighbours plus transitivity of the lexicographic order.)
* `inspectCount_of_verified` — once the array has been verified, **any** pair of ranks can be
  compared in exactly one inspection, using the interval minimum of the LCP array.
* `verify_linear_time` — the two halves together: cost `s.length - 1`, and the ranks order the
  suffixes.
* `checkSa` is the check as a *program* (`List.all` down the neighbouring pairs) and
  `checkSa_eq_true_iff` says it accepts exactly the `Verified` arrays.
* `compare_lt_iff_saRank_lt` — **the check decides every comparison**: on a verified candidate
  the ranks are the lexicographic order of the suffixes
  (`compare (suffix s i) (suffix s j) = Ordering.lt ↔ saRank sa i < saRank sa j`), so a
  candidate that passes *is* the suffix array of `s`.
* The `aⁿ` section is the quadratic-versus-linear contrast **on the same `n - 1` pairs**.  For
  `s = aⁿ` the suffix array is `replicateSa n = [n-1, n-2, …, 0]`; it passes the check
  (`replicate_verified`) and is a candidate (`replicateSa_candidate`), so the guided check of
  its neighbouring pairs costs `n - 1` (`sum_inspectCount_verify_replicate`), while the naive
  character comparison of the very same pairs costs `(n-1)(n+2)/2`
  (`naive_verify_replicate`): `2 · naive = (n + 2) · guided` (`verify_contrast_replicate`).
-/
import SortBounds.Projects.SAIS.Chain

namespace SortBounds.Projects.SAIS

variable {α : Type*} [LinearOrder α]

/-! ### The check -/

/-- `saLcp s sa p` is the LCP-array entry between ranks `p` and `p + 1` of the candidate suffix
array `sa`. -/
def saLcp (s : List α) (sa : List ℕ) (p : ℕ) : ℕ :=
  lcp (suffix s (sa.getD p 0)) (suffix s (sa.getD (p + 1) 0))

/-- One verification step: compare the suffixes at ranks `p` and `p + 1`, skipping the
LCP-array entry between them. -/
def verifyStep (s : List α) (sa : List ℕ) (p : ℕ) : Ordering :=
  cmpFrom s (saLcp s sa p) (sa.getD p 0) (sa.getD (p + 1) 0)

/-- A step of the check is a **correct** comparison, so its single inspection decides the
answer (`cmpFrom_lcp_advance`). -/
theorem verifyStep_eq (s : List α) (sa : List ℕ) (p : ℕ) :
    verifyStep s sa p = compare (suffix s (sa.getD p 0)) (suffix s (sa.getD (p + 1) 0)) :=
  cmpFrom_lcp_advance s _ _

/-- A step of the check inspects **exactly one** position (`inspectCount_lcp`). -/
theorem inspectCount_verifyStep (s : List α) (sa : List ℕ) (p : ℕ) :
    inspectCount s (saLcp s sa p) (sa.getD p 0) (sa.getD (p + 1) 0) = 1 :=
  inspectCount_lcp s _ _

/-- The candidate `sa` **passes the check**: each of its neighbouring pairs of suffixes is
strictly increasing. -/
def Verified (s : List α) (sa : List ℕ) : Prop :=
  ∀ p, p + 1 < sa.length → verifyStep s sa p = Ordering.lt

/-- The check as a *program*: `List.all` down the neighbouring pairs, testing each with
`verifyStep`.  Its inspection count is `sum_inspectCount_verify` below, and
`checkSa_eq_true_iff` says it accepts exactly the `Verified` arrays. -/
def checkSa (s : List α) (sa : List ℕ) : Bool :=
  (List.range (sa.length - 1)).all fun p => decide (verifyStep s sa p = Ordering.lt)

/-- The program accepts exactly the arrays that pass the check. -/
theorem checkSa_eq_true_iff (s : List α) (sa : List ℕ) : checkSa s sa = true ↔ Verified s sa := by
  simp only [checkSa, Verified, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h p hp => h p (by omega), fun h p hp => h p (by omega)⟩

/-- `sa` is a **candidate** suffix array of `s`: a duplicate-free list of `s.length` valid
positions, i.e. a permutation of `0, …, s.length - 1`. -/
def IsSaCandidate (s : List α) (sa : List ℕ) : Prop :=
  sa.Nodup ∧ sa.length = s.length ∧ ∀ i ∈ sa, i < s.length

/-! ### The cost of the check -/

/-- **The check costs one inspection per neighbouring pair**: verifying `sa` against its LCP
array takes exactly `sa.length - 1` character inspections. -/
theorem sum_inspectCount_verify (s : List α) (sa : List ℕ) :
    (∑ p ∈ Finset.range (sa.length - 1),
        inspectCount s (saLcp s sa p) (sa.getD p 0) (sa.getD (p + 1) 0)) =
      sa.length - 1 := by
  rw [Finset.sum_congr rfl (fun p _ => inspectCount_verifyStep s sa p), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_id]

/-! ### What a passed check means -/

/-- The hypothesis the min property needs, extracted from a passed check: within any interval of
ranks, the neighbouring suffixes compare strictly less. -/
theorem verified_chain {s : List α} {sa : List ℕ} (h : Verified s sa) {a b : ℕ}
    (hb : b < sa.length) :
    ∀ k ∈ Finset.Ico a b,
      compare (suffix s (sa.getD k 0)) (suffix s (sa.getD (k + 1) 0)) = Ordering.lt := by
  intro k hk
  have hk' := Finset.mem_Ico.mp hk
  rw [← verifyStep_eq]
  exact h k (by omega)

/-- **The check is complete**: if every neighbouring pair of the candidate is strictly
increasing then every pair of ranks is, so the ranks order the suffixes lexicographically. -/
theorem compare_lt_of_verify {s : List α} {sa : List ℕ} (h : Verified s sa) {a b : ℕ}
    (hab : a < b) (hb : b < sa.length) :
    compare (suffix s (sa.getD a 0)) (suffix s (sa.getD b 0)) = Ordering.lt :=
  compare_lt_of_chain (f := fun k => suffix s (sa.getD k 0)) hab (verified_chain h hb)

/-- **The min property, with the candidate array in place**: between two ranks of a verified
`sa`, the LCP of the suffixes is the interval minimum of the LCP array `saLcp` — the README's
M1a statement with the enumeration written out. -/
theorem lcp_eq_inf'_saLcp {s : List α} {sa : List ℕ} (h : Verified s sa) {a b : ℕ}
    (hab : a < b) (hb : b < sa.length) :
    lcp (suffix s (sa.getD a 0)) (suffix s (sa.getD b 0)) =
      (Finset.Ico a b).inf' (Finset.nonempty_Ico.mpr hab) (saLcp s sa) := by
  exact lcp_eq_inf'_of_chain hab (verified_chain h hb)

/-- The guided comparison between any two ranks of a verified array is the true comparison. -/
theorem cmpFrom_of_verified {s : List α} {sa : List ℕ} (h : Verified s sa) {a b : ℕ}
    (hab : a < b) (hb : b < sa.length) :
    cmpFrom s ((Finset.Ico a b).inf' (Finset.nonempty_Ico.mpr hab) (saLcp s sa))
        (sa.getD a 0) (sa.getD b 0) = compare (suffix s (sa.getD a 0)) (suffix s (sa.getD b 0)) := by
  rw [← lcp_eq_inf'_saLcp h hab hb]
  exact cmpFrom_lcp_advance s _ _

/-- **After the check, every pair is cheap**: between any two ranks of a verified array the
interval minimum of the LCP array is the true LCP, so the guided comparison inspects exactly
one position. -/
theorem inspectCount_of_verified {s : List α} {sa : List ℕ} (h : Verified s sa) {a b : ℕ}
    (hab : a < b) (hb : b < sa.length) :
    inspectCount s ((Finset.Ico a b).inf' (Finset.nonempty_Ico.mpr hab) (saLcp s sa))
        (sa.getD a 0) (sa.getD b 0) = 1 := by
  exact inspectCount_inf'_of_increasing s _ hab (verified_chain h hb)

/-- **M1c: a suffix array is verified in linear inspections.**  If `sa` is a candidate for the
suffix array of `s` and passes the check, then the check cost exactly `s.length - 1`
inspections, and the ranks of `sa` order the suffixes lexicographically. -/
theorem verify_linear_time (s : List α) (sa : List ℕ) (hcand : IsSaCandidate s sa)
    (h : Verified s sa) :
    (∑ p ∈ Finset.range (sa.length - 1),
        inspectCount s (saLcp s sa p) (sa.getD p 0) (sa.getD (p + 1) 0)) = s.length - 1 ∧
      (∀ a b, a < b → b < sa.length →
        compare (suffix s (sa.getD a 0)) (suffix s (sa.getD b 0)) = Ordering.lt) :=
  ⟨by rw [sum_inspectCount_verify, hcand.2.1],
    fun a b hab hb => compare_lt_of_verify h hab hb⟩

/-- A worked instance: the suffix array of `"banana"` passes the check. -/
theorem banana_verified : Verified ['b', 'a', 'n', 'a', 'n', 'a'] [5, 3, 1, 0, 4, 2] := by
  intro p hp
  simp only [List.length_cons, List.length_nil] at hp
  have h5 : p < 5 := by omega
  interval_cases p <;> decide

/-- The program accepts `"banana"`'s suffix array. -/
theorem banana_check : checkSa ['b', 'a', 'n', 'a', 'n', 'a'] [5, 3, 1, 0, 4, 2] = true := by
  decide

/-- Concretely: after the check, comparing the suffixes at ranks `1` and `4` of `"banana"`'s
suffix array inspects one character (`inspectCount_of_verified`). -/
theorem banana_inspect_one :
    inspectCount ['b', 'a', 'n', 'a', 'n', 'a']
        ((Finset.Ico 1 4).inf' (Finset.nonempty_Ico.mpr (by decide))
          (saLcp ['b', 'a', 'n', 'a', 'n', 'a'] [5, 3, 1, 0, 4, 2])) 3 4 = 1 :=
  inspectCount_of_verified banana_verified (by decide) (by decide)

/-! ### The check decides: a verified candidate is the suffix array

`compare_lt_of_verify` says that the ranks order the suffixes.  Together with the candidate
hypothesis — no repeats, `s.length` entries, all positions valid, so a permutation of
`0, …, s.length - 1` — the ranks are a total order on all the suffixes, and the check decides
every comparison: `compare_lt_iff_saRank_lt`. -/

/-- `saRank sa i` is the rank of the text position `i` in the candidate suffix array `sa`. -/
def saRank (sa : List ℕ) (i : ℕ) : ℕ := sa.idxOf i

omit [LinearOrder α] in
/-- Every valid position occurs in a candidate (a permutation of `0, …, s.length - 1`). -/
theorem mem_of_candidate {s : List α} {sa : List ℕ} (hcand : IsSaCandidate s sa) {i : ℕ}
    (hi : i < s.length) : i ∈ sa := by
  have hsub : sa.toFinset ⊆ Finset.range s.length := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_range.mpr (hcand.2.2 x hx)
  have hcard : sa.toFinset.card = s.length := by
    rw [List.toFinset_card_of_nodup hcand.1, hcand.2.1]
  have heq : sa.toFinset = Finset.range s.length :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  rw [← List.mem_toFinset, heq]
  exact Finset.mem_range.mpr hi

omit [LinearOrder α] in
/-- Every valid position has a rank in range. -/
theorem saRank_lt {s : List α} {sa : List ℕ} (hcand : IsSaCandidate s sa) {i : ℕ}
    (hi : i < s.length) : saRank sa i < sa.length :=
  List.idxOf_lt_length_iff.mpr (mem_of_candidate hcand hi)

omit [LinearOrder α] in
/-- Rank and position are inverse on valid positions. -/
theorem getD_saRank {s : List α} {sa : List ℕ} (hcand : IsSaCandidate s sa) {i : ℕ}
    (hi : i < s.length) : sa.getD (saRank sa i) 0 = i := by
  have h : saRank sa i < sa.length := saRank_lt hcand hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp only [Option.getD_some]
  exact List.getElem_idxOf h

/-- **The check decides every comparison.**  For a verified candidate, two suffixes compare
strictly less exactly when their ranks do — so the candidate *is* the suffix array of `s`. -/
theorem compare_lt_iff_saRank_lt {s : List α} {sa : List ℕ} (hcand : IsSaCandidate s sa)
    (h : Verified s sa) {i j : ℕ} (hi : i < s.length) (hj : j < s.length) (hne : i ≠ j) :
    compare (suffix s i) (suffix s j) = Ordering.lt ↔ saRank sa i < saRank sa j := by
  constructor
  · intro hcmp
    rcases lt_trichotomy (saRank sa i) (saRank sa j) with hlt | heq | hgt
    · exact hlt
    · exact absurd (by rw [← getD_saRank hcand hi, ← getD_saRank hcand hj, heq]) hne
    · -- the check, run the other way round, would say `suffix j < suffix i`
      have hji : compare (suffix s (sa.getD (saRank sa j) 0))
          (suffix s (sa.getD (saRank sa i) 0)) = Ordering.lt :=
        compare_lt_of_verify h hgt (saRank_lt hcand hi)
      rw [getD_saRank hcand hj, getD_saRank hcand hi] at hji
      have hgt' : compare (suffix s j) (suffix s i) = Ordering.gt := by
        have hswap := Std.OrientedCmp.eq_swap (cmp := fun (x y : List α) => compare x y)
          (a := suffix s i) (b := suffix s j)
        rw [hcmp] at hswap
        simpa using (congrArg Ordering.swap hswap).symm
      rw [hgt'] at hji
      exact absurd hji (by decide)
  · intro hlt
    have hc := compare_lt_of_verify h hlt (saRank_lt hcand hj)
    rwa [getD_saRank hcand hi, getD_saRank hcand hj] at hc

/-! ### Non-vacuity

`"banana"`'s suffix array `[5, 3, 1, 0, 4, 2]` satisfies every hypothesis above. -/

/-- It is a candidate: six distinct positions, all valid. -/
theorem banana_candidate : IsSaCandidate ['b', 'a', 'n', 'a', 'n', 'a'] [5, 3, 1, 0, 4, 2] :=
  ⟨by decide, rfl, by decide⟩

/-- So `verify_linear_time` applies, and the check costs `5 = 6 - 1` inspections. -/
theorem banana_verify_linear :
    (∑ p ∈ Finset.range 5,
        inspectCount ['b', 'a', 'n', 'a', 'n', 'a']
          (saLcp ['b', 'a', 'n', 'a', 'n', 'a'] [5, 3, 1, 0, 4, 2] p)
          ([5, 3, 1, 0, 4, 2].getD p 0) ([5, 3, 1, 0, 4, 2].getD (p + 1) 0)) = 5 :=
  (verify_linear_time _ _ banana_candidate banana_verified).1

/-- And the ranks of `"banana"` really are the order of its suffixes: suffix `5` (`"a"`) has
rank `0`, suffix `3` (`"ana"`) rank `1`, and indeed `"a" < "ana"`. -/
theorem banana_ranks :
    saRank [5, 3, 1, 0, 4, 2] 5 = 0 ∧ saRank [5, 3, 1, 0, 4, 2] 3 = 1 ∧
      compare (suffix ['b', 'a', 'n', 'a', 'n', 'a'] 5)
        (suffix ['b', 'a', 'n', 'a', 'n', 'a'] 3) = Ordering.lt :=
  ⟨by decide, by decide, by decide⟩

/-! ### The contrast on `aⁿ`: the same `n - 1` pairs, linear versus quadratic

For `s = aⁿ` the suffixes are ordered by length (`suffix (aⁿ) i = a^(n-i)`), so the suffix array
is `[n-1, n-2, …, 0]`: rank `p` is the suffix at position `n - 1 - p`.  The neighbouring pair
of ranks `p`, `p + 1` is therefore the position pair `(n-1-p, n-2-p)`, whose LCP is the length
`n - 1 - p` of the shorter suffix. -/

/-- The suffix array of `aⁿ` as a list of positions: `[n-1, n-2, …, 0]`. -/
def replicateSa (n : ℕ) : List ℕ := (List.range n).reverse

theorem replicateSa_length (n : ℕ) : (replicateSa n).length = n := by
  simp [replicateSa]

/-- Rank `p` of `replicateSa n` is the suffix at position `n - 1 - p`. -/
theorem replicateSa_getD {n p : ℕ} (hp : p < n) : (replicateSa n).getD p 0 = n - 1 - p := by
  rw [replicateSa, List.getD_eq_getElem?_getD, List.getElem?_reverse (by simpa using hp),
    List.getElem?_eq_getElem (by simpa using (by omega : n - 1 - p < n)), List.getElem_range,
    List.length_range]
  rfl

omit [LinearOrder α] in
/-- `replicateSa n` is a candidate suffix array of `aⁿ`. -/
theorem replicateSa_candidate (a : α) (n : ℕ) : IsSaCandidate (List.replicate n a) (replicateSa n) := by
  refine ⟨?_, by simp [replicateSa], ?_⟩
  · rw [replicateSa, List.nodup_reverse]
    exact List.nodup_range
  · intro i hi
    simp only [replicateSa, List.mem_reverse, List.mem_range] at hi
    simpa using hi

/-- Suffixes of `aⁿ` whose lengths are ordered are ordered lexicographically. -/
theorem compare_replicate (a : α) : ∀ i j : ℕ,
    compare (List.replicate i a) (List.replicate j a) = compare i j
  | 0, 0 => rfl
  | 0, j + 1 => ((compare_lt_iff_lt (a := (0 : ℕ)) (b := j + 1)).mpr (by omega)).symm
  | i + 1, 0 => ((compare_gt_iff_gt (a := i + 1) (b := (0 : ℕ))).mpr (by omega)).symm
  | i + 1, j + 1 => by
    rw [List.replicate_succ, List.replicate_succ, List.compare_cons_cons,
      show compare a a = Ordering.eq from by simp, Ordering.eq_then, compare_replicate a i j]
    cases h : compare i j with
    | lt =>
      have hij : i < j := by rwa [compare_lt_iff_lt] at h
      exact ((compare_lt_iff_lt (a := i + 1) (b := j + 1)).mpr (by omega)).symm
    | eq =>
      have hij : i = j := by rwa [compare_eq_iff_eq] at h
      exact ((compare_eq_iff_eq (a := i + 1) (b := j + 1)).mpr (by omega)).symm
    | gt =>
      have hij : j < i := by rwa [compare_gt_iff_gt] at h
      exact ((compare_gt_iff_gt (a := i + 1) (b := j + 1)).mpr (by omega)).symm

theorem compare_replicate_lt {i j : ℕ} (a : α) (h : i < j) :
    compare (List.replicate i a) (List.replicate j a) = Ordering.lt := by
  rw [compare_replicate, compare_lt_iff_lt]
  exact h

/-- The suffix array of `aⁿ` passes the check: suffixes of decreasing length are increasing. -/
theorem replicate_verified (a : α) (n : ℕ) : Verified (List.replicate n a) (replicateSa n) := by
  intro p hp
  rw [verifyStep_eq]
  have hp' : p + 1 < n := by simpa [replicateSa_length] using hp
  rw [replicateSa_getD (by omega), replicateSa_getD hp', suffix_eq_replicate, suffix_eq_replicate]
  exact compare_replicate_lt a (by omega)

/-- The guided check of `aⁿ`'s neighbouring pairs costs `n - 1` inspections. -/
theorem sum_inspectCount_verify_replicate (a : α) (n : ℕ) :
    (∑ p ∈ Finset.range (n - 1),
        inspectCount (List.replicate n a) (saLcp (List.replicate n a) (replicateSa n) p)
          ((replicateSa n).getD p 0) ((replicateSa n).getD (p + 1) 0)) = n - 1 := by
  have h := sum_inspectCount_verify (List.replicate n a) (replicateSa n)
  rwa [replicateSa_length] at h

/-- `2 · ∑_{p < m} (p + 2) = m (m + 3)`. -/
theorem two_mul_sum_range_add_two (m : ℕ) : 2 * (∑ p ∈ Finset.range m, (p + 2)) = m * (m + 3) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    nlinarith [ih]

/-- **The naive character comparison of the same `n - 1` neighbouring pairs** of `aⁿ`'s suffix
array: comparing the suffixes at positions `n-1-p` and `n-2-p` inspects `n - (n-1-p) + 1 = p + 2`
characters, so the total is `(n-1)(n+2)/2`. -/
theorem naive_verify_replicate (a : α) (n : ℕ) (hn : 1 ≤ n) :
    2 * (∑ p ∈ Finset.range (n - 1),
        inspectCount (List.replicate n a) 0 ((replicateSa n).getD p 0)
          ((replicateSa n).getD (p + 1) 0)) = (n - 1) * (n + 2) := by
  have hterm : ∀ p ∈ Finset.range (n - 1),
      inspectCount (List.replicate n a) 0 ((replicateSa n).getD p 0)
        ((replicateSa n).getD (p + 1) 0) = p + 2 := by
    intro p hp
    have hp' := Finset.mem_range.mp hp
    rw [replicateSa_getD (by omega), replicateSa_getD (by omega), inspectCount_replicate,
      Nat.max_eq_left (by omega)]
    omega
  rw [Finset.sum_congr rfl hterm, two_mul_sum_range_add_two (n - 1)]
  have h3 : n - 1 + 3 = n + 2 := by omega
  rw [h3]

/-- **Quadratic versus linear on the same pairs.**  On `aⁿ` the naive character comparison of
the `n - 1` neighbouring pairs of the suffix array inspects `(n + 2) / 2` times as many
characters as the LCP-guided check: `(n-1)(n+2)/2 = (n+2)/2 · (n-1)`. -/
theorem verify_contrast_replicate (a : α) (n : ℕ) (hn : 1 ≤ n) :
    2 * (∑ p ∈ Finset.range (n - 1),
        inspectCount (List.replicate n a) 0 ((replicateSa n).getD p 0)
          ((replicateSa n).getD (p + 1) 0)) =
      (n + 2) * (∑ p ∈ Finset.range (n - 1),
        inspectCount (List.replicate n a) (saLcp (List.replicate n a) (replicateSa n) p)
          ((replicateSa n).getD p 0) ((replicateSa n).getD (p + 1) 0)) := by
  rw [naive_verify_replicate a n hn, sum_inspectCount_verify_replicate, Nat.mul_comm]

/-- The instance `a⁴`: the guided check of the three neighbouring pairs costs `3`, the naive
one `9`. -/
theorem contrast_replicate_four :
    (∑ p ∈ Finset.range 3,
        inspectCount (List.replicate 4 'a') (saLcp (List.replicate 4 'a') (replicateSa 4) p)
          ((replicateSa 4).getD p 0) ((replicateSa 4).getD (p + 1) 0)) = 3 ∧
      (∑ p ∈ Finset.range 3,
        inspectCount (List.replicate 4 'a') 0 ((replicateSa 4).getD p 0)
          ((replicateSa 4).getD (p + 1) 0)) = 9 := by
  refine ⟨?_, ?_⟩ <;> decide

end SortBounds.Projects.SAIS
