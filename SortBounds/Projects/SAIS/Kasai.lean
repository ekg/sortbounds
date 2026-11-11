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
  deciding mismatch); `lcp_drop_of_le` — a scan that starts at a genuine lower bound finds the
  rest of the LCP.
* `rankLcp_succ_le` — **the classical inequality** `L (i+1) ≥ L i - 1`, where `L i` is the LCP
  of `suffix i` with its rank-successor (`rankLcp s sa i`).  This is the invariant that makes
  the carry-over sound; it is where `lcp_eq_inf'_of_chain` (the min property, `Chain.lean`) is
  used: the sorted successor is at least as close as `j + 1` (`lcp_getD_le_saLcp`), and
  `suffix_succ_lcp` / `suffix_succ_compare` are the "drop one character from both" step.
* `kasai_lcp_correct` — the produced array is the LCP array: entry `k` is
  `lcp (suffix (sa k)) (suffix (sa (k+1)))` for `k < sa.length - 1` (`kasai_length` says the
  array has exactly `sa.length - 1` entries, `kasai_lcp_correct_saLcp` says it is the `saLcp`
  array the verifier reads).
* `kasai_cost_le` — and the count is at most `2 * s.length`: the amortised bound, obtained by
  carrying the potential `2 * i + h` (`KasaiInv`): every step adds at most `(new matches) + 1`
  inspections and `h` gains exactly the new matches and loses one, so the count never outruns
  `2 * i + h`; at the end `h ≤ rankLcp s sa s.length = 0`.
* `kasai_verify_linear` — **the whole linear-time account**: producing the array (`2 n` at
  most) and then checking the candidate against it (`sum_inspectCount_verify`, `n - 1`) costs
  at most `3 n` character pairs.
* the running example: `pairScan_replicate`, `saRank_replicateSa`, `saNext_replicateSa`,
  `kasaiStep_replicateSa_{zero,one,succ}`, `kasaiAux_replicateSa_flat` and
  `kasai_replicate_cost` — **on `aⁿ` the algorithm inspects exactly `n - 1` pairs**.

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


/-- Starting a scan at a genuine lower bound: the LCP of the two drops is what is left of the
LCP. -/
theorem lcp_drop_of_le {a b : List α} {k : ℕ} (hk : k ≤ lcp a b) :
    lcp (a.drop k) (b.drop k) = lcp a b - k := by
  have hsplit := lcp_eq_length_take_add (take_eq_of_le_lcp hk)
  have hlen : (a.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left (le_trans hk (lcp_le_left a b))]
  omega

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

omit [LinearOrder α] in
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
      have hklt : saRank sa (saNext sa i + 1) < sa.length := saRank_lt hcand hj1
      have hle : saRank sa (i + 1) + 1 ≤ saRank sa (saNext sa i + 1) := hrank
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · have h := lcp_getD_le_saLcp hver (r := saRank sa (i + 1))
          (k := saRank sa (saNext sa i + 1)) hrank hklt
        rw [getD_saRank hcand hi, getD_saRank hcand hj1] at h
        exact h
      · have h1 : saLcp s sa (saRank sa (i + 1)) =
            lcp (suffix s (i + 1)) (suffix s (saNext sa i + 1)) := by
          rw [saLcp, getD_saRank hcand hi, heq, getD_saRank hcand hj1]
        rw [h1]
    have htail := suffix_succ_lcp hi' hj hL
    omega

/-! ### The scan of one text position -/

/-- The scan Kasai's algorithm performs at text position `i` with carry-over `h`: compare
`suffix i` against its rank-successor, starting `h` characters in. -/
def kasaiScan (s : List α) (sa : List ℕ) (i h : ℕ) : ℕ × ℕ :=
  pairScan ((suffix s i).drop h) ((suffix s (saNext sa i)).drop h)

/-- Starting at a genuine lower bound, the scan finds the rest of the LCP. -/
theorem kasaiScan_fst {s : List α} {sa : List ℕ} {i h : ℕ}
    (hh : h ≤ lcp (suffix s i) (suffix s (saNext sa i))) :
    (kasaiScan s sa i h).1 = lcp (suffix s i) (suffix s (saNext sa i)) - h := by
  simp only [kasaiScan, pairScan_fst, lcp_drop_of_le hh]

/-- The value the scan reaches: the carry-over plus the matches. -/
theorem kasaiScan_total {s : List α} {sa : List ℕ} {i h : ℕ}
    (hh : h ≤ lcp (suffix s i) (suffix s (saNext sa i))) :
    h + (kasaiScan s sa i h).1 = lcp (suffix s i) (suffix s (saNext sa i)) := by
  rw [kasaiScan_fst hh]
  omega

/-- The scan inspects at most one pair per new match, plus the deciding mismatch. -/
theorem kasaiScan_snd_le {s : List α} {sa : List ℕ} {i h : ℕ}
    (hh : h ≤ lcp (suffix s i) (suffix s (saNext sa i))) :
    (kasaiScan s sa i h).2 ≤ lcp (suffix s i) (suffix s (saNext sa i)) - h + 1 := by
  have h1 := pairScan_snd_le ((suffix s i).drop h) ((suffix s (saNext sa i)).drop h)
  simp only [pairScan_fst, lcp_drop_of_le hh] at h1
  exact h1

/-! ### The state, and one step of the loop -/

/-- The state of Kasai's loop. -/
structure KasaiState where
  /-- The entries written so far: `lcpOf p` is the value written at rank `p`. -/
  lcpOf : ℕ → ℕ
  /-- The carried lower bound for the LCP at the next text position. -/
  h : ℕ
  /-- The number of character pairs inspected so far. -/
  cost : ℕ

/-- The initial state: nothing written, no carry-over, nothing inspected. -/
def KasaiState.init : KasaiState := ⟨fun _ => 0, 0, 0⟩

/-- **One text position of Kasai's algorithm.**  Compare `suffix i` with its rank-successor
starting `h` characters in, write the value reached at rank `saRank sa i`, and carry one less to
the next text position (`st.h + … - 1` is truncated subtraction, i.e. `max 0 (… - 1)`).  At the last rank there is no entry to write and the carry-over restarts
at `0`. -/
def kasaiStep (s : List α) (sa : List ℕ) (i : ℕ) (st : KasaiState) : KasaiState :=
  if saRank sa i + 1 < s.length then
    { lcpOf := fun p => if p = saRank sa i then st.h + (kasaiScan s sa i st.h).1 else st.lcpOf p
      h := st.h + (kasaiScan s sa i st.h).1 - 1
      cost := st.cost + (kasaiScan s sa i st.h).2 }
  else { lcpOf := st.lcpOf, h := 0, cost := st.cost }

/-- Kasai's loop, as a recursion on a fuel/index pair: `kasaiAux s sa fuel i st` runs the loop
over the text positions `i, i + 1, …, i + fuel - 1`. -/
def kasaiAux (s : List α) (sa : List ℕ) : ℕ → ℕ → KasaiState → KasaiState
  | 0, _, st => st
  | fuel + 1, i, st => kasaiAux s sa fuel (i + 1) (kasaiStep s sa i st)

/-- **Kasai's algorithm.**  The first component is the LCP array of the suffix array `sa` (entry
`k` is `lcp (suffix (sa k)) (suffix (sa (k+1)))`, for `k < sa.length - 1`) and the second is the
number of character pairs the algorithm inspected. -/
def kasai (s : List α) (sa : List ℕ) : List ℕ × ℕ :=
  let st := kasaiAux s sa s.length 0 KasaiState.init
  ((List.range (sa.length - 1)).map st.lcpOf, st.cost)

theorem kasai_fst (s : List α) (sa : List ℕ) :
    (kasai s sa).1 =
      (List.range (sa.length - 1)).map (kasaiAux s sa s.length 0 KasaiState.init).lcpOf := rfl

theorem kasai_snd (s : List α) (sa : List ℕ) :
    (kasai s sa).2 = (kasaiAux s sa s.length 0 KasaiState.init).cost := rfl

/-- Reading off the produced array. -/
theorem getD_map_range (f : ℕ → ℕ) {m k : ℕ} (hk : k < m) :
    ((List.range m).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem kasaiAux_zero (s : List α) (sa : List ℕ) (i : ℕ) (st : KasaiState) :
    kasaiAux s sa 0 i st = st := rfl

theorem kasaiAux_succ (s : List α) (sa : List ℕ) (fuel i : ℕ) (st : KasaiState) :
    kasaiAux s sa (fuel + 1) i st = kasaiAux s sa fuel (i + 1) (kasaiStep s sa i st) := rfl

/-! ### The loop invariant -/

/-- The loop invariant at text position `i`:

* the carry-over `h` is a lower bound for the LCP there (`rankLcp s sa i`), which is what makes
  the scan start in a genuinely common prefix;
* every rank written so far holds its true LCP;
* the count satisfies the potential `2 * i + h` — the amortised accounting. -/
def KasaiInv (s : List α) (sa : List ℕ) (i : ℕ) (st : KasaiState) : Prop :=
  st.h ≤ rankLcp s sa i ∧
    (∀ i' < i, saRank sa i' + 1 < s.length →
      st.lcpOf (saRank sa i') = saLcp s sa (saRank sa i')) ∧
    st.cost ≤ 2 * i + st.h

theorem KasaiState.init_inv (s : List α) (sa : List ℕ) :
    KasaiInv s sa 0 KasaiState.init := by
  refine ⟨Nat.zero_le _, ?_, ?_⟩
  · intro i' hi'
    omega
  · simp [KasaiState.init]

omit [LinearOrder α] in
/-- Two distinct positions have distinct ranks. -/
theorem saRank_ne {sa : List ℕ} {i i' : ℕ} (hi : i ∈ sa) (hne : i ≠ i') :
    saRank sa i ≠ saRank sa i' := by
  intro heq
  exact hne ((List.idxOf_inj hi).mp heq)

/-- Once the text positions run out the LCP of "the last rank" is `0`: there is no rank after
`sa.length`. -/
theorem rankLcp_length {s : List α} {sa : List ℕ} (hcand : IsSaCandidate s sa) :
    rankLcp s sa s.length = 0 := by
  rw [rankLcp_of_not_le]
  intro h
  rcases Classical.em (s.length ∈ sa) with hmem | hmem
  · exact absurd (hcand.2.2 _ hmem) (by omega)
  · rw [saRank_eq_length hmem, hcand.2.1] at h
    omega

/-- **One step of the loop preserves the invariant.** -/
theorem kasaiStep_inv {s : List α} {sa : List ℕ} (hcand : IsSaCandidate s sa)
    (hver : Verified s sa) {i : ℕ} (hi : i < s.length) {st : KasaiState}
    (hinv : KasaiInv s sa i st) : KasaiInv s sa (i + 1) (kasaiStep s sa i st) := by
  obtain ⟨hbound, hwritten, hcost⟩ := hinv
  by_cases hr : saRank sa i + 1 < s.length
  · have hLi : rankLcp s sa i = lcp (suffix s i) (suffix s (saNext sa i)) :=
      rankLcp_eq_lcp hcand hi hr
    have hhL : st.h ≤ lcp (suffix s i) (suffix s (saNext sa i)) := by
      rw [← hLi]; exact hbound
    have htot := kasaiScan_total hhL
    have hsnd := kasaiScan_snd_le hhL
    have hval : st.h + (kasaiScan s sa i st.h).1 - 1 =
        lcp (suffix s i) (suffix s (saNext sa i)) - 1 := by omega
    have hrank_eq : st.h + (kasaiScan s sa i st.h).1 = saLcp s sa (saRank sa i) := by
      rw [htot, ← hLi]; exact rankLcp_of_le hr
    -- the fields of the state after the step
    have hh : (kasaiStep s sa i st).h = st.h + (kasaiScan s sa i st.h).1 - 1 := by
      rw [kasaiStep, ite_eq_left hr]
    have hc : (kasaiStep s sa i st).cost = st.cost + (kasaiScan s sa i st.h).2 := by
      rw [kasaiStep, ite_eq_left hr]
    have hf : (kasaiStep s sa i st).lcpOf =
        fun p => if p = saRank sa i then st.h + (kasaiScan s sa i st.h).1 else st.lcpOf p := by
      rw [kasaiStep, ite_eq_left hr]
    refine ⟨?_, ?_, ?_⟩
    · -- the carry-over is a lower bound at the next position
      rw [hh, hval]
      rcases Nat.lt_or_eq_of_le (show i + 1 ≤ s.length by omega) with hlt | heq
      · have hstep := rankLcp_succ_le hcand hver hlt
        rw [hLi] at hstep
        omega
      · -- the last text position: its suffix has length one
        have h2 := lcp_le_left (suffix s i) (suffix s (saNext sa i))
        rw [suffix_length] at h2
        omega
    · -- the entry written at rank `saRank sa i` is the LCP there
      intro i' hi' hcond
      have hi'len : i' < s.length := by omega
      rw [hf]
      rcases Nat.lt_or_eq_of_le (show i' ≤ i by omega) with hlt | heq
      · have hne : saRank sa i' ≠ saRank sa i :=
          saRank_ne (mem_of_candidate hcand hi'len) (by omega)
        show (if saRank sa i' = saRank sa i then st.h + (kasaiScan s sa i st.h).1
            else st.lcpOf (saRank sa i')) = saLcp s sa (saRank sa i')
        rw [ite_eq_right hne]
        exact hwritten i' hlt hcond
      · have hsame : saRank sa i' = saRank sa i := by rw [heq]
        rw [hsame]
        show (if saRank sa i = saRank sa i then st.h + (kasaiScan s sa i st.h).1
            else st.lcpOf (saRank sa i)) = saLcp s sa (saRank sa i)
        rw [ite_eq_left rfl]
        exact hrank_eq
    · -- the amortised accounting
      rw [hh, hc]
      omega
  · -- the last rank: nothing to write, the carry-over restarts at zero
    have hzero : rankLcp s sa i = 0 := rankLcp_of_not_le hr
    have hh0 : st.h = 0 := by
      have := hbound
      rw [hzero] at this
      omega
    have hh : (kasaiStep s sa i st).h = 0 := by
      rw [kasaiStep, ite_eq_right hr]
    have hc : (kasaiStep s sa i st).cost = st.cost := by
      rw [kasaiStep, ite_eq_right hr]
    have hf : (kasaiStep s sa i st).lcpOf = st.lcpOf := by
      rw [kasaiStep, ite_eq_right hr]
    refine ⟨?_, ?_, ?_⟩
    · rw [hh]
      exact Nat.zero_le _
    · intro i' hi' hcond
      rw [hf]
      rcases Nat.lt_or_eq_of_le (show i' ≤ i by omega) with hlt | heq
      · exact hwritten i' hlt hcond
      · exact absurd hcond (by rw [heq]; exact hr)
    · rw [hh, hc]
      omega

/-- **The invariant holds at the end of the loop.** -/
theorem kasaiAux_inv {s : List α} {sa : List ℕ} (hcand : IsSaCandidate s sa)
    (hver : Verified s sa) (fuel i : ℕ) (heq : i + fuel = s.length) (st : KasaiState)
    (hinv : KasaiInv s sa i st) :
    KasaiInv s sa (i + fuel) (kasaiAux s sa fuel i st) := by
  induction fuel generalizing i st with
  | zero =>
    rw [kasaiAux_zero]
    simpa using hinv
  | succ fuel ih =>
    have hstep := ih (i + 1) (by omega) (kasaiStep s sa i st)
      (kasaiStep_inv hcand hver (by omega) hinv)
    rw [kasaiAux_succ]
    rwa [show i + 1 + fuel = i + (fuel + 1) by omega] at hstep

/-! ### The two theorems -/

/-- **Kasai's algorithm produces the LCP array.**  For a candidate suffix array that is genuinely
sorted (`Verified`), entry `k` of `(kasai s sa).1` is the LCP of the suffixes of ranks `k` and
`k + 1`. -/
theorem kasai_lcp_correct (s : List α) (sa : List ℕ) (hsa : IsSaCandidate s sa)
    (hsorted : Verified s sa) :
    ∀ k < sa.length - 1,
      (kasai s sa).1.getD k 0 =
        lcp (suffix s (sa.getD k 0)) (suffix s (sa.getD (k + 1) 0)) := by
  have hinv := kasaiAux_inv hsa hsorted s.length 0 (by omega) KasaiState.init
    (KasaiState.init_inv s sa)
  have hwritten := hinv.2.1
  intro k hk
  have hk' : k < sa.length := by omega
  have hgetD : sa.getD k 0 = sa[k] := List.getD_eq_getElem sa 0 hk'
  have hi'y : sa.getD k 0 < s.length := by
    rw [hgetD]
    exact hsa.2.2 _ (List.getElem_mem hk')
  have hpos : saRank sa (sa.getD k 0) = k := saRank_getD hsa.1 hk'
  have hcond : saRank sa (sa.getD k 0) + 1 < s.length := by
    rw [hpos, ← hsa.2.1]; omega
  have h := hwritten (sa.getD k 0) (by omega) hcond
  rw [hpos] at h
  rw [kasai_fst, getD_map_range _ hk]
  exact h

/-- **Kasai's algorithm is linear**: at most `2 * s.length` character pairs inspected.  The proof
carries the potential `2 * i + h` (`KasaiInv`): each step adds at most `(new matches) + 1`
inspections, and `h` gains exactly the new matches and loses one — so the count never outruns
`2 * i + h`, and at the end `h ≤ rankLcp s sa s.length = 0`. -/
theorem kasai_cost_le (s : List α) (sa : List ℕ) (hsa : IsSaCandidate s sa)
    (hsorted : Verified s sa) : (kasai s sa).2 ≤ 2 * s.length := by
  have hinv := kasaiAux_inv hsa hsorted s.length 0 (by omega) KasaiState.init
    (KasaiState.init_inv s sa)
  have hcost := hinv.2.2
  have hlast := hinv.1
  rw [Nat.zero_add, rankLcp_length hsa] at hlast
  rw [kasai_snd]
  omega

/-- The produced array has exactly `sa.length - 1` entries: one per neighbouring pair of ranks. -/
theorem kasai_length (s : List α) (sa : List ℕ) : (kasai s sa).1.length = sa.length - 1 := by
  rw [kasai_fst, List.length_map, List.length_range]

/-- The produced array is exactly the array the verifier reads: `saLcp`. -/
theorem kasai_lcp_correct_saLcp (s : List α) (sa : List ℕ) (hsa : IsSaCandidate s sa)
    (hsorted : Verified s sa) {k : ℕ} (hk : k < sa.length - 1) :
    (kasai s sa).1.getD k 0 = saLcp s sa k :=
  kasai_lcp_correct s sa hsa hsorted k hk

/-! ### Composition with the verifier

`Verify.lean`'s check needs the LCP array and costs `n - 1` inspections; `kasai` produces it in at
most `2n`.  Together they account for the whole linear-time path: build the array, then verify the
candidate against it. -/

/-- **A complete linear-time account.**  Constructing the LCP array (`kasai`, at most `2 * n`
inspections) and then verifying the candidate against it (`sum_inspectCount_verify`, `n - 1`
inspections) inspects at most `3 * n` character pairs in total. -/
theorem kasai_verify_linear (s : List α) (sa : List ℕ) (hcand : IsSaCandidate s sa)
    (hver : Verified s sa) :
    (kasai s sa).2 +
        (∑ p ∈ Finset.range (sa.length - 1),
          inspectCount s (saLcp s sa p) (sa.getD p 0) (sa.getD (p + 1) 0)) ≤ 3 * s.length := by
  rw [sum_inspectCount_verify]
  have hcost := kasai_cost_le s sa hcand hver
  have hlen : sa.length = s.length := hcand.2.1
  omega

/-! ### Non-vacuity

The hypotheses of both theorems are satisfied and the algorithm really computes the LCP array:
`"banana"` and `a⁴`, by the kernel's own reduction.  `"banana"`'s suffix array is a candidate
(`banana_candidate`) that passes the check (`banana_verified`), so the two theorems apply to it
verbatim. -/

/-- Kasai on `"banana"` produces the LCP array `[1, 3, 0, 0, 2]` — the array `Chain.lean` uses in
`banana_min_property` — inspecting `5` character pairs (against `2 * 6 = 12`). -/
theorem banana_kasai :
    (kasai ['b', 'a', 'n', 'a', 'n', 'a'] [5, 3, 1, 0, 4, 2]).1 = [1, 3, 0, 0, 2] ∧
      (kasai ['b', 'a', 'n', 'a', 'n', 'a'] [5, 3, 1, 0, 4, 2]).2 = 5 := by
  decide

/-- On `a⁴` (suffix array `replicateSa 4 = [3, 2, 1, 0]`) the LCP array is `[1, 2, 3]` and the
algorithm inspects `3 = n - 1` character pairs. -/
theorem replicate_four_kasai :
    (kasai (List.replicate 4 'a') (replicateSa 4)).1 = [1, 2, 3] ∧
      (kasai (List.replicate 4 'a') (replicateSa 4)).2 = 3 := by
  decide

/-- `"mississippi"`: the whole LCP array `[1, 1, 4, 0, 0, 1, 0, 2, 1, 3]` of the suffix array
`[10, 7, 4, 1, 0, 9, 8, 6, 3, 5, 2]`, at the cost of `16` inspected pairs (`≤ 2 * 11 = 22`). -/
theorem mississippi_kasai :
    (kasai "mississippi".toList [10, 7, 4, 1, 0, 9, 8, 6, 3, 5, 2]).1 =
        [1, 1, 4, 0, 0, 1, 0, 2, 1, 3] ∧
      (kasai "mississippi".toList [10, 7, 4, 1, 0, 9, 8, 6, 3, 5, 2]).2 = 16 := by
  decide

/-- `kasai_lcp_correct` on `"banana"`: entry `1` of the produced array is the LCP of the suffixes
at ranks `1` and `2` — `"ana"` and `"anana"`, i.e. `3`. -/
theorem banana_kasai_entry_one :
    (kasai ['b', 'a', 'n', 'a', 'n', 'a'] [5, 3, 1, 0, 4, 2]).1.getD 1 0 =
      lcp (suffix ['b', 'a', 'n', 'a', 'n', 'a'] 3) (suffix ['b', 'a', 'n', 'a', 'n', 'a'] 1) := by
  have h := kasai_lcp_correct _ _ banana_candidate banana_verified 1 (by decide)
  simpa using h

/-! ### Why `Verified` cannot be dropped

`IsSaCandidate` only says that `sa` is a permutation of the positions; Kasai's carry-over is a
fact about the *sort order*.  Both theorems need the order, and here is the kernel's own
computation showing what goes wrong without it. -/

/-- **The entries can be wrong on an unsorted candidate.**  `[0, 1, 3, 2]` is a candidate suffix
array of `"aaaa"`, and Kasai writes `2` at rank `1`, where the LCP of the suffixes at ranks `1`
and `2` is `1`. -/
theorem kasai_entries_unsound :
    (kasai ['a', 'a', 'a', 'a'] [0, 1, 3, 2]).1.getD 1 0 ≠
      lcp (suffix ['a', 'a', 'a', 'a'] ([0, 1, 3, 2].getD 1 0))
        (suffix ['a', 'a', 'a', 'a'] ([0, 1, 3, 2].getD 2 0)) := by
  decide

/-- **And the `2n` bound fails on an unsorted candidate.**  `[6, 1, 0, 3, 4, 5, 2]` is a
candidate suffix array of `"aaaaaab"`, and the same algorithm inspects 15 character pairs —
more than `2 * 7 = 14`.  The potential argument of `kasai_cost_le` shows exactly where the
hypothesis enters: without `Verified`, the carry-over need not be a lower bound for `rankLcp`,
so at the last rank `h` can still be positive; resetting it to `0` there (`kasaiStep`'s second
branch) throws that potential away, and the sorted case is precisely the one where `h` is
already `0` at that point. -/
theorem kasai_cost_unsound :
    2 * 7 < (kasai ['a', 'a', 'a', 'a', 'a', 'a', 'b'] [6, 1, 0, 3, 4, 5, 2]).2 := by
  decide


/-! ### The running example `aⁿ`

On a string of `n` equal characters the suffixes are ordered by length and the suffix array is
`replicateSa n = [n-1, …, 0]`.  The run of the algorithm is then completely explicit: at text
position `i ≥ 1` the suffix sits next to `suffix (i-1)` (`saNext_replicateSa`) and the two share
`n - i` characters (`lcp_replicateSa`), so the only scan that finds anything is the one at
position `1`; after it the carry-over already is the whole LCP and every further step is free
(`kasaiAux_replicateSa_flat`), for a total of `n - 1` inspections (`kasai_replicate_cost`). -/

/-- Scanning two runs of equal characters compares `min p q` pairs and they all match. -/
theorem pairScan_replicate (a : α) (p q : ℕ) :
    pairScan (List.replicate p a) (List.replicate q a) = (min p q, min p q) := by
  induction p generalizing q with
  | zero => simp [pairScan]
  | succ p ih =>
    cases q with
    | zero => simp [pairScan]
    | succ q =>
      rw [List.replicate_succ, List.replicate_succ, pairScan, ite_eq_left rfl, ih,
        Nat.succ_min_succ]

omit [LinearOrder α] in
/-- The rank of text position `i` in the suffix array of `aⁿ`. -/
theorem saRank_replicateSa (a : α) {n i : ℕ} (hi : i < n) :
    saRank (replicateSa n) i = n - 1 - i := by
  have hp : n - 1 - i < (replicateSa n).length := by
    rw [replicateSa_length]; omega
  have hnd : (replicateSa n).Nodup := (replicateSa_candidate a n).1
  have hget : (replicateSa n).getD (n - 1 - i) 0 = i := by
    rw [replicateSa_getD (n := n) (p := n - 1 - i) (by omega)]
    omega
  have h1 : saRank (replicateSa n) ((replicateSa n).getD (n - 1 - i) 0) = n - 1 - i :=
    saRank_getD hnd hp
  rwa [hget] at h1

omit [LinearOrder α] in
/-- At a text position `i ≥ 1`, the rank-successor in the suffix array of `aⁿ` is the previous
text position. -/
theorem saNext_replicateSa (a : α) {n i : ℕ} (hi1 : 1 ≤ i) (hi : i < n) :
    saNext (replicateSa n) i = i - 1 := by
  rw [saNext, saRank_replicateSa a hi]
  have hidx : n - 1 - i + 1 = n - i := by omega
  rw [hidx]
  have hp : n - i < n := by omega
  rw [replicateSa_getD (n := n) (p := n - i) hp]
  omega

/-- The LCP of the two neighbouring suffixes of `aⁿ` at text positions `i` and `i - 1`. -/
theorem lcp_replicateSa (a : α) {n i : ℕ} (hi : i < n) :
    lcp (suffix (List.replicate n a) i) (suffix (List.replicate n a) (i - 1)) = n - i := by
  rw [suffix_eq_replicate, suffix_eq_replicate, lcp_replicate]
  omega

omit [LinearOrder α] in
/-- At text position `0` of `aⁿ` there is no rank-successor: it is the last rank. -/
theorem saRank_replicateSa_zero (a : α) (n : ℕ) :
    ¬ saRank (replicateSa n) 0 + 1 < List.length (List.replicate n a) := by
  intro h
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp at h
  · rw [saRank_replicateSa a (by omega), List.length_replicate] at h
    omega

/-- One step of the loop on `aⁿ` at the last rank (`i = 0`): nothing written, carry-over `0`. -/
theorem kasaiStep_replicateSa_zero (a : α) (n : ℕ) (f : ℕ → ℕ) (c : ℕ) :
    kasaiStep (List.replicate n a) (replicateSa n) 0 ⟨f, 0, c⟩ = ⟨f, 0, c⟩ := by
  rw [kasaiStep, ite_eq_right (saRank_replicateSa_zero a n)]

/-- One step of the loop on `aⁿ` at a position `i ≥ 2`: the carry-over already is the whole LCP,
so the scan is empty — the entry is written and the carry-over drops by one. -/
theorem kasaiStep_replicateSa_succ (a : α) {n i : ℕ} (hi2 : 2 ≤ i) (hi : i < n)
    (f : ℕ → ℕ) (c : ℕ) :
    kasaiStep (List.replicate n a) (replicateSa n) i ⟨f, n - i, c⟩ =
      ⟨fun p => if p = n - 1 - i then n - i else f p, n - (i + 1), c⟩ := by
  have hr : saRank (replicateSa n) i + 1 < List.length (List.replicate n a) := by
    rw [saRank_replicateSa a hi, List.length_replicate]
    omega
  have hdrop : (suffix (List.replicate n a) i).drop (n - i) = [] := by
    rw [suffix, List.drop_eq_nil_iff, List.length_drop, List.length_replicate]
  have hscan : kasaiScan (List.replicate n a) (replicateSa n) i (n - i) = (0, 0) := by
    rw [kasaiScan, saNext_replicateSa a (by omega) hi, hdrop]
    rfl
  rw [kasaiStep, ite_eq_left hr, hscan, saRank_replicateSa a hi]
  dsimp only
  have hh : n - i + 0 - 1 = n - (i + 1) := by omega
  rw [hh, Nat.add_zero]
  simp

/-- One step of the loop on `aⁿ` at position `1`: the suffix `a^(n-1)` is scanned against `a^n`
and matches on all `n - 1` characters. -/
theorem kasaiStep_replicateSa_one (a : α) {n : ℕ} (hn : 2 ≤ n) (f : ℕ → ℕ) (c : ℕ) :
    kasaiStep (List.replicate n a) (replicateSa n) 1 ⟨f, 0, c⟩ =
      ⟨fun p => if p = n - 2 then n - 1 else f p, n - 2, c + (n - 1)⟩ := by
  have h1 : 1 < n := by omega
  have hr : saRank (replicateSa n) 1 + 1 < List.length (List.replicate n a) := by
    rw [saRank_replicateSa a h1, List.length_replicate]
    omega
  have hscan : kasaiScan (List.replicate n a) (replicateSa n) 1 0 = (n - 1, n - 1) := by
    rw [kasaiScan, saNext_replicateSa a le_rfl h1, suffix_eq_replicate, suffix_eq_replicate,
      List.drop_zero]
    rw [show n - (1 - 1) = n from by omega, List.drop_zero, pairScan_replicate]
    rw [show min (n - 1) n = n - 1 from by omega]
  rw [kasaiStep, ite_eq_left hr, hscan, saRank_replicateSa a h1]
  dsimp only
  have hh : 0 + (n - 1) - 1 = n - 2 := by omega
  rw [hh, Nat.zero_add]
  rfl

/-- The run of the loop on `aⁿ` from a position `i ≥ 2` whose carry-over is `n - i`: every
remaining step is an empty scan, so the count stays put and the carry-over walks down to `0`. -/
theorem kasaiAux_replicateSa_flat (a : α) (n : ℕ) :
    ∀ (k i : ℕ) (f : ℕ → ℕ) (c : ℕ), i + k = n → 2 ≤ i →
      (kasaiAux (List.replicate n a) (replicateSa n) k i ⟨f, n - i, c⟩).cost = c ∧
        (kasaiAux (List.replicate n a) (replicateSa n) k i ⟨f, n - i, c⟩).h + (i + k) = n := by
  intro k
  induction k with
  | zero =>
    intro i f c hik hi2
    rw [kasaiAux_zero]
    exact ⟨rfl, by show n - i + (i + 0) = n; omega⟩
  | succ k ih =>
    intro i f c hik hi2
    have hin : i < n := by omega
    rw [kasaiAux_succ, kasaiStep_replicateSa_succ a hi2 hin]
    have h := ih (i + 1) (fun p => if p = n - 1 - i then n - i else f p) c (by omega) (by omega)
    exact ⟨h.1, by omega⟩

/-- **Kasai's algorithm on `aⁿ` inspects exactly `n - 1` character pairs** — one run of matches at
text position `1`, then nothing at all, because the carry-over already knows the rest.  Together
with `sum_inspectCount_verify_replicate` (`Verify.lean`) this prices the whole linear-time path on
`aⁿ` at `(n - 1) + (n - 1)` inspections (`kasai_verify_replicate`). -/
theorem kasai_replicate_cost (a : α) (n : ℕ) :
    (kasai (List.replicate n a) (replicateSa n)).2 = n - 1 := by
  rw [kasai_snd, List.length_replicate]
  simp only [KasaiState.init]
  rcases n with _ | _ | m
  · rw [kasaiAux_zero]
  · rw [show (1 : ℕ) = 0 + 1 from rfl, kasaiAux_succ, kasaiStep_replicateSa_zero, kasaiAux_zero]
  · rw [kasaiAux_succ, kasaiStep_replicateSa_zero, kasaiAux_succ,
      kasaiStep_replicateSa_one a (by omega)]
    have hflat := (kasaiAux_replicateSa_flat a (m + 2) m 2
      (fun p => if p = m + 2 - 2 then m + 2 - 1 else (fun _ => 0) p) (0 + (m + 2 - 1))
      (by omega) (by omega)).1
    rw [hflat]
    simp

/-- **The whole path on `aⁿ` costs exactly `2 n - 2` inspections**: `n - 1` to build the LCP
array (`kasai_replicate_cost`) and `n - 1` to check the suffix array against it
(`sum_inspectCount_verify_replicate`, `Verify.lean`). -/
theorem kasai_verify_replicate (a : α) (n : ℕ) :
    (kasai (List.replicate n a) (replicateSa n)).2 +
        (∑ p ∈ Finset.range (n - 1),
          inspectCount (List.replicate n a) (saLcp (List.replicate n a) (replicateSa n) p)
            ((replicateSa n).getD p 0) ((replicateSa n).getD (p + 1) 0)) = 2 * (n - 1) := by
  rw [kasai_replicate_cost a n, sum_inspectCount_verify_replicate a n]
  ring

/-! ### The contract's statements, verbatim

`kasai_lcp_correct` and `kasai_cost_le` above carry `Verified s sa` in addition to the
`IsSaCandidate s sa` of the lane README's M2 block.  That hypothesis is not removable —
`kasai_entries_unsound` and `kasai_cost_unsound` are counterexamples for the statements without it —
so the README's statements as literally written are false, and the versions here are the true
ones.  (`suffix` is the total version of `LCP.lean` and `saRank` the `Verify.lean` one, as
recorded there.) -/

end Kasai

end SortBounds.Projects.SAIS
