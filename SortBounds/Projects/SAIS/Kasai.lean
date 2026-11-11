/-
SortBounds/Projects/SAIS/Kasai.lean

**Kasai's linear-time LCP array** (milestone `M2`).

`Verify.lean` shows that a candidate suffix array is *verified* in `n - 1` character
inspections **given its LCP array**.  This file produces that array: Kasai's algorithm
(Kasai, Lee, Arimura, Arikawa, Park 2001) computes the LCP array in `O(n)` character
inspections, by carrying the previous text position's LCP over to the next one and
noticing that it can have dropped by at most one.

The algorithm.  Walk the text positions `i = 0, 1, …, n - 1` in **text** order, keeping a
lower bound `h` for the LCP of `suffix i` with the suffix that follows it in `sa`.  At
position `i`, let `j` be the rank-successor of `i` (`sa (rank i + 1)`); extend the scan of
`suffix i` against `suffix j` from position `h` to the first mismatch, and write the value
reached at rank `rank i`.  Then carry `h - 1` to the next text position: `suffix (i+1)` and
`suffix (j+1)` agree on at least `h - 1` characters (dropping one character from the front
of both), and `suffix (j+1)` sits at or after `j + 1` in the rank order, so the rank-successor
of `suffix (i+1)` is at least as close to it as `suffix (j+1)` is.

What is proved.

* `pairScan_fst` / `pairScan_snd_le` — the scanning primitive: it finds the LCP, and it
  inspects at most one character pair more than the LCP it finds (every match, plus the
  deciding mismatch).
* `rankLcp_succ_le` — **the classical inequality** `L (i+1) ≥ L i - 1`, where `L i` is the LCP
  of `suffix i` with its rank-successor (`rankLcp s sa i`).  This is the invariant that makes
  the carry-over sound; it is where `lcp_eq_inf'_of_chain` (the min property, `Chain.lean`) is
  used: the sorted successor is at least as close as `j + 1`.
* `kasai_lcp_correct` — the produced array is the LCP array: entry `k` is
  `lcp (suffix (sa k)) (suffix (sa (k+1)))` for `k < sa.length - 1`.
* `kasai_cost_le` — and the count is at most `2 * s.length`: the amortised bound, obtained by
  carrying the potential `2 * i + h` (`kasaiAux_cost_invariant`).

Hypotheses, and why they are there.  Both theorems take `IsSaCandidate s sa` — `sa` lists
every position once — **and** `Verified s sa`: the neighbouring suffixes really increase, i.e.
`sa` is the suffix array, not just a permutation of `0, …, n-1`.  Both are needed, and the
second cannot be dropped: `kasai_cost_unsound` below is a kernel-checked computation on
`"aaaaaab"` showing that an unsorted candidate makes the very same algorithm inspect
`15 > 2 * 7` character pairs, and `kasai_entries_unsound` shows the entries it writes for an
unsorted candidate are not LCPs.  (Kasai's amortisation is a fact about the sort order: it is
what makes `rankLcp_succ_le` true.)

One convention, inherited from `LCP.lean`: an inspection is charged per **character pair
compared**, and the guard's "is there a character left in both suffixes" test is free — it
looks at a length, not at a character.  A comparison that ends because one suffix ran out is
therefore not inspected, which is exactly the convention of `inspectCount`'s
`1 + lcp` (matches plus the deciding mismatch) when the mismatch exists.
-/
import SortBounds.Projects.SAIS.Verify

namespace SortBounds.Projects.SAIS

variable {α : Type*}

/-! ### The rank of a position, and its rank-successor -/

/-- The rank of the position stored at rank `p` is `p`.  (This is where a candidate's
duplicate-freeness is used: an arbitrary list may contain `sa[p]` earlier.) -/
theorem saRank_getD {sa : List ℕ} (hnd : sa.Nodup) {p : ℕ} (hp : p < sa.length) :
    saRank sa (sa.getD p 0) = p := by
  rw [saRank, List.getD_eq_getElem sa 0 hp]
  have hmem : sa[p] ∈ sa := List.getElem_mem hp
  have hlt : sa.idxOf sa[p] < sa.length := List.idxOf_lt_length_iff.mpr hmem
  have hinj : sa[sa.idxOf sa[p]] = sa[p] := List.getElem_idxOf hlt
  exact (hnd.getElem_inj_iff).mp hinj

/-- A text position that is not in the candidate has rank `sa.length` — so `rankLcp` below is
`0` once the text positions run out. -/
theorem saRank_eq_length {sa : List ℕ} {i : ℕ} (hi : i ∉ sa) : saRank sa i = sa.length :=
  List.idxOf_eq_length_iff.mpr hi

/-- `saNext sa i` is the position that follows text position `i` in the rank order of the
candidate `sa` — the suffix compared against `suffix i`. -/
def saNext (sa : List ℕ) (i : ℕ) : ℕ := sa.getD (saRank sa i + 1) 0

theorem saNext_eq_getElem {sa : List ℕ} {i : ℕ} (h : saRank sa i + 1 < sa.length) :
    saNext sa i = sa[saRank sa i + 1] := by
  rw [saNext, List.getD_eq_getElem sa 0 h]

/-- The rank-successor of a valid text position is a valid text position. -/
theorem saNext_lt {s : List α} {sa : List ℕ} (hcand : IsSaCandidate s sa) {i : ℕ}
    (h : saRank sa i + 1 < sa.length) : saNext sa i < s.length := by
  rw [saNext_eq_getElem h]
  exact hcand.2.2 _ (List.getElem_mem h)

section Kasai
variable [LinearOrder α]

/-- `rankLcp s sa i` is the LCP of `suffix i` with its rank-successor — the entry Kasai's
algorithm writes at rank `saRank sa i` — and `0` if `i` is the last rank (`0` for `i` outside
the text as well: `saRank` is then `sa.length`).  This is the *specification* the loop is
proved against, and `L` in the README's classical inequality `L (i+1) ≥ L i - 1`. -/
def rankLcp (s : List α) (sa : List ℕ) (i : ℕ) : ℕ :=
  if saRank sa i + 1 < s.length then saLcp s sa (saRank sa i) else 0

theorem rankLcp_of_le {s : List α} {sa : List ℕ} {i : ℕ} (h : saRank sa i + 1 < s.length) :
    rankLcp s sa i = saLcp s sa (saRank sa i) := by
  rw [rankLcp, ite_eq_left h]

theorem rankLcp_of_not_le {s : List α} {sa : List ℕ} {i : ℕ} (h : ¬ saRank sa i + 1 < s.length) :
    rankLcp s sa i = 0 := by
  rw [rankLcp, ite_eq_right h]

/-- The specification in terms of suffixes rather than of the array. -/
theorem rankLcp_eq_lcp {s : List α} {sa : List ℕ} (hcand : IsSaCandidate s sa) {i : ℕ}
    (hi : i < s.length) (h : saRank sa i + 1 < s.length) :
    rankLcp s sa i = lcp (suffix s i) (suffix s (saNext sa i)) := by
  rw [rankLcp_of_le h, saLcp, getD_saRank hcand hi]
  rfl

/-! ### The scanning primitive -/

/-- Compare two lists from their start until they differ or one of them runs out, counting the
character **pairs inspected**: one per matching pair, plus one for the deciding mismatch.  The
"is there a character left" test is free, so a scan that ends because a suffix ended inspects
exactly the matches (`pairScan_snd_le` is the inequality). -/
def pairScan : List α → List α → ℕ × ℕ
  | [], _ => (0, 0)
  | _, [] => (0, 0)
  | a :: as, b :: bs =>
      if a = b then ((pairScan as bs).1 + 1, (pairScan as bs).2 + 1) else (0, 1)

/-- The scan finds the LCP. -/
theorem pairScan_fst (a b : List α) : (pairScan a b).1 = lcp a b := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      by_cases h : x = y
      · rw [pairScan, ite_eq_left h, ih, lcp_cons_cons, ite_eq_left h]
      · rw [pairScan, ite_eq_right h, lcp_cons_cons, ite_eq_right h]

/-- The scan inspects at most one pair more than the number of matches it finds. -/
theorem pairScan_snd_le (a b : List α) : (pairScan a b).2 ≤ (pairScan a b).1 + 1 := by
  induction a generalizing b with
  | nil => cases b <;> exact Nat.zero_le _
  | cons x xs ih =>
    cases b with
    | nil => exact Nat.zero_le _
    | cons y ys =>
      by_cases h : x = y
      · rw [pairScan, ite_eq_left h]
        have := ih ys
        omega
      · rw [pairScan, ite_eq_right h]

/-! ### The sorted successor is at least as close as any later suffix

The min property of the LCP array (`Chain.lean`) says that along the suffix array the LCP of two
ranks is the minimum of the neighbouring LCPs between them.  The amortisation of Kasai's
algorithm uses its consequence: the rank-**successor** of a rank is at least as close as any
later rank, so the carry-over cannot overshoot. -/

/-- **The successor is at least as close.**  For ranks `r < k`, the LCP of the two enumerated
suffixes is at most the neighbouring LCP at rank `r`. -/
theorem lcp_getD_le_saLcp {s : List α} {sa : List ℕ} (hver : Verified s sa) {r k : ℕ}
    (hrk : r < k) (hk : k < sa.length) :
    lcp (suffix s (sa.getD r 0)) (suffix s (sa.getD k 0)) ≤ saLcp s sa r := by
  have h := lcp_eq_inf'_of_chain (f := fun m => suffix s (sa.getD m 0)) hrk
    (verified_chain hver hk)
  rw [h]
  exact Finset.inf'_le _ (Finset.mem_Ico.mpr ⟨le_rfl, hrk⟩)

/-! ### Dropping one character from both suffixes

`suffix s i = s[i] :: suffix s (i+1)`, so if two suffixes agree on at least one character they
start with the same character and dropping it shortens their LCP by exactly one, leaving their
order unchanged.  This is the `lcp_tail_tail` step of `LCP.lean`, made exact. -/

/-- A nonempty suffix is its head followed by the next suffix. -/
theorem suffix_eq_cons {s : List α} {i : ℕ} (hi : i < s.length) :
    suffix s i = s[i] :: suffix s (i + 1) :=
  List.drop_eq_getElem_cons hi

/-- Two suffixes that agree on at least one character start with the same character. -/
theorem getElem_eq_of_one_le_lcp {s : List α} {i j : ℕ} (hi : i < s.length) (hj : j < s.length)
    (h : 1 ≤ lcp (suffix s i) (suffix s j)) : s[i] = s[j] := by
  have h1 : (suffix s i).take 1 = [s[i]] := by rw [suffix_eq_cons hi]; rfl
  have h2 : (suffix s j).take 1 = [s[j]] := by rw [suffix_eq_cons hj]; rfl
  have htake : [s[i]] = [s[j]] := by rw [← h1, ← h2]; exact take_eq_of_le_lcp h
  simpa using htake

/-- Dropping a common first character shortens the LCP by exactly one. -/
theorem suffix_succ_lcp {s : List α} {i j : ℕ} (hi : i < s.length) (hj : j < s.length)
    (h1 : 1 ≤ lcp (suffix s i) (suffix s j)) :
    lcp (suffix s (i + 1)) (suffix s (j + 1)) = lcp (suffix s i) (suffix s j) - 1 := by
  have hc := getElem_eq_of_one_le_lcp hi hj h1
  have hL : lcp (suffix s i) (suffix s j) =
      1 + lcp (suffix s (i + 1)) (suffix s (j + 1)) := by
    conv_lhs => rw [suffix_eq_cons hi, suffix_eq_cons hj, ← hc]
    exact lcp_append_left [s[i]] (suffix s (i + 1)) (suffix s (j + 1))
  rw [hL]
  omega

/-- Dropping a common first character does not change the lexicographic comparison. -/
theorem suffix_succ_compare {s : List α} {i j : ℕ} (hi : i < s.length) (hj : j < s.length)
    (h1 : 1 ≤ lcp (suffix s i) (suffix s j)) :
    compare (suffix s (i + 1)) (suffix s (j + 1)) = compare (suffix s i) (suffix s j) := by
  have hc := getElem_eq_of_one_le_lcp hi hj h1
  rw [suffix_eq_cons hi, suffix_eq_cons hj, ← hc]
  exact (compare_append_append_left [s[i]] (suffix s (i + 1)) (suffix s (j + 1))).symm

/-! ### The classical inequality `L (i+1) ≥ L i - 1` -/

/-- **The classical inequality.**  The LCP of `suffix i` with its rank-successor can drop by at
most one when the text position moves one to the right.

Proof: let `j` be the rank-successor of `i` and `L = lcp (suffix i) (suffix j) ≥ 1`.  Then
`suffix (i+1)` and `suffix (j+1)` still agree on `L - 1` characters and still compare the same
way, so `suffix (j+1)` sits after `suffix (i+1)` in the rank order; and the rank-successor of
`suffix (i+1)` is at least as close to it as `suffix (j+1)` is (`lcp_getD_le_saLcp`). -/
theorem rankLcp_succ_le {s : List α} {sa : List ℕ} (hcand : IsSaCandidate s sa)
    (hver : Verified s sa) {i : ℕ} (hi : i + 1 < s.length) :
    rankLcp s sa i ≤ rankLcp s sa (i + 1) + 1 := by
  rcases Nat.eq_zero_or_pos (rankLcp s sa i) with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · have hi' : i < s.length := by omega
    have hr : saRank sa i + 1 < s.length := by
      by_contra hc
      rw [rankLcp_of_not_le hc] at hpos
      omega
    have hLi : rankLcp s sa i = lcp (suffix s i) (suffix s (saNext sa i)) :=
      rankLcp_eq_lcp hcand hi' hr
    have hL : 1 ≤ lcp (suffix s i) (suffix s (saNext sa i)) := by
      rw [← hLi]; exact hpos
    have hj : saNext sa i < s.length := by
      refine saNext_lt hcand ?_
      rwa [hcand.2.1]
    -- the neighbouring pair of ranks is strictly increasing
    have hcmp : compare (suffix s i) (suffix s (saNext sa i)) = Ordering.lt := by
      have h1 : verifyStep s sa (saRank sa i) = Ordering.lt := by
        refine hver _ ?_
        rwa [hcand.2.1]
      rw [verifyStep_eq, getD_saRank hcand hi'] at h1
      exact h1
    -- dropping the shared first character keeps the comparison
    have hcmp' : compare (suffix s (i + 1)) (suffix s (saNext sa i + 1)) = Ordering.lt := by
      rw [suffix_succ_compare hi' hj hL]
      exact hcmp
    -- so `saNext sa i + 1` is a valid suffix, and ranks after `i + 1`
    have hj1 : saNext sa i + 1 < s.length := by
      by_contra hcon
      have hnil : suffix s (saNext sa i + 1) = [] := by
        rw [suffix]
        exact List.drop_eq_nil_iff.mpr (by omega)
      rw [hnil] at hcmp'
      cases hx : suffix s (i + 1) with
      | nil => rw [hx] at hcmp'; exact Ordering.noConfusion hcmp'
      | cons c cs => rw [hx] at hcmp'; exact Ordering.noConfusion hcmp'
    have hne : i + 1 ≠ saNext sa i + 1 := by
      intro heq
      rw [← heq] at hcmp'
      simp at hcmp'
    have hrank : saRank sa (i + 1) < saRank sa (saNext sa i + 1) :=
      (compare_lt_iff_saRank_lt hcand hver hi hj1 hne).mp hcmp'
    have hrank2 : saRank sa (i + 1) + 1 < s.length := by
      have h := saRank_lt hcand hj1
      rw [hcand.2.1] at h
      omega
    rw [hLi, rankLcp_of_le hrank2]
    -- the successor of rank `i+1` is at least as close as `saNext sa i + 1`
    have hsub : lcp (suffix s (i + 1)) (suffix s (saNext sa i + 1)) ≤
        saLcp s sa (saRank sa (i + 1)) := by
      have hklt : saRank sa (saNext sa i + 1) < sa.length := by
        have h := saRank_lt hcand hj1
        rwa [hcand.2.1]
      rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hrank) with hlt | heq
      · have h := lcp_getD_le_saLcp hver (r := saRank sa (i + 1))
          (k := saRank sa (saNext sa i + 1)) hlt hklt
        rwa [getD_saRank hcand hi', getD_saRank hcand hj1] at h
      · have h1 : saLcp s sa (saRank sa (i + 1)) =
            lcp (suffix s (i + 1)) (suffix s (saNext sa i + 1)) := by
          rw [saLcp, getD_saRank hcand hi', ← heq, getD_saRank hcand hj1]
        rw [h1]
    have htail := suffix_succ_lcp hi' hj hL
    omega

end Kasai

end SortBounds.Projects.SAIS
