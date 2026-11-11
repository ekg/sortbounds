/-
SortBounds/Projects/SAIS/Compose.lean

The last link in the SAIS chain, and the one a reviewer asked for: `Verify.lean`'s
check reads its LCP array from `saLcp`, which is **unmetered** (it computes the true
`lcp`), so `kasai_verify_linear`'s `≤ 3n` added a metered quantity (Kasai's `≤ 2n`) to
an unmetered one (`n − 1`).  Here the checker is run on the array Kasai *produces*:
`kasai_lcp_correct_saLcp` says the computed entries are `saLcp`, so the check costs the
same `n − 1` inspections while reading only computed data.  The result is the honest
headline: **`≤ 3n` character inspections for build-then-verify, with nothing metered
for free** (the remaining free inputs are the string itself and the *candidate*, whose
production — SA-IS/DC3 — is not formalised).
-/
import SortBounds.Projects.SAIS.Kasai
import SortBounds.Projects.SAIS.Counted

namespace SortBounds.Projects.SAIS

variable {α : Type*} [LinearOrder α]

/-- **The check run on the computed array** costs the same `n − 1` inspections.  This is
what licenses reading `kasai`'s output instead of the `saLcp` oracle. -/
theorem sum_inspectCount_computed (s : List α) (sa : List ℕ) (hsa : IsSaCandidate s sa)
    (hsorted : Verified s sa) :
    (∑ p ∈ Finset.range (sa.length - 1),
        inspectCount s ((kasai s sa).1.getD p 0) (sa.getD p 0) (sa.getD (p + 1) 0))
      = sa.length - 1 := by
  calc (∑ p ∈ Finset.range (sa.length - 1),
          inspectCount s ((kasai s sa).1.getD p 0) (sa.getD p 0) (sa.getD (p + 1) 0))
      = (∑ p ∈ Finset.range (sa.length - 1),
          inspectCount s (saLcp s sa p) (sa.getD p 0) (sa.getD (p + 1) 0)) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mem_range] at hp
        rw [kasai_lcp_correct_saLcp s sa hsa hsorted hp]
    _ = sa.length - 1 := sum_inspectCount_verify s sa

/-- **Build, then verify, on computed data only**: Kasai's `≤ 2n` plus the check's
`n − 1`, reading the array Kasai just produced. -/
theorem build_then_verify (s : List α) (sa : List ℕ) (hsa : IsSaCandidate s sa)
    (hsorted : Verified s sa) :
    (kasai s sa).2
        + (∑ p ∈ Finset.range (sa.length - 1),
            inspectCount s ((kasai s sa).1.getD p 0) (sa.getD p 0) (sa.getD (p + 1) 0))
      ≤ 3 * s.length := by
  rw [sum_inspectCount_computed s sa hsa hsorted]
  have hcost : (kasai s sa).2 ≤ 2 * s.length := kasai_cost_le s sa hsa hsorted
  have hlen : sa.length - 1 ≤ s.length := by
    have := hsa.2.1
    omega
  omega

/-- The certificate is a suffix array: on a verified candidate, comparison of suffixes
agrees with comparison of ranks, which is `compare_lt_iff_saRank_lt` restated here for
the composed pipeline. -/
theorem verified_is_suffix_array (s : List α) (sa : List ℕ) (hsa : IsSaCandidate s sa)
    (hsorted : Verified s sa) {i j : ℕ} (hi : i < s.length) (hj : j < s.length)
    (hne : i ≠ j) :
    (compare (suffix s i) (suffix s j) = Ordering.lt ↔ saRank sa i < saRank sa j) :=
  compare_lt_iff_saRank_lt hsa hsorted hi hj hne

/-! ### A counted checker that takes the array as an argument

`Counted.checkSaCounted` computes its per-pair bound with `saLcp`, i.e. with the unmetered
`lcp` — so citing it for the `n − 1` figure charges an oracle.  This checker takes the
array as a parameter: the `n − 1` is paid on *given* data.  `checkOn_computed` feeds it
Kasai's output, and the array being **exact** (`kasai_lcp_correct_saLcp`) is what makes
both the cost `n − 1` and the acceptance hold. -/

/-- A counted checker over a given array of per-pair LCP bounds. -/
def checkOnGo (s : List α) (sa : List ℕ) (arr : ℕ → ℕ) : ℕ → Bool → ℕ → Bool × ℕ
  | 0, b, k => (b, k)
  | p + 1, b, k =>
      checkOnGo s sa arr p
        (b && decide (cmpFrom s (arr p) (sa.getD p 0) (sa.getD (p + 1) 0) = Ordering.lt))
        (k + inspectCount s (arr p) (sa.getD p 0) (sa.getD (p + 1) 0))

/-- The counted checker over a given array. -/
def checkOn (s : List α) (sa : List ℕ) (arr : ℕ → ℕ) : Bool × ℕ :=
  checkOnGo s sa arr (sa.length - 1) true 0

/-- With an **exact** array every step costs exactly one inspection. -/
theorem checkOnGo_cost (s : List α) (sa : List ℕ) (arr : ℕ → ℕ)
    (harr : ∀ p, p < sa.length - 1 →
      arr p = lcp (suffix s (sa.getD p 0)) (suffix s (sa.getD (p + 1) 0))) :
    ∀ n b k, n ≤ sa.length - 1 → (checkOnGo s sa arr n b k).2 = k + n := by
  intro n
  induction n with
  | zero => intro b k _; simp [checkOnGo]
  | succ n ih =>
    intro b k hn
    rw [checkOnGo, ih (b && _) (k + _) (by omega)]
    have hstep : inspectCount s (arr n) (sa.getD n 0) (sa.getD (n + 1) 0) = 1 := by
      rw [inspectCount_eq, harr n (by omega), lcp_drop_lcp, Nat.add_zero]
    rw [hstep]; ring

/-- The counted checker over an exact array costs `sa.length - 1`. -/
theorem checkOn_cost (s : List α) (sa : List ℕ) (arr : ℕ → ℕ)
    (harr : ∀ p, p < sa.length - 1 →
      arr p = lcp (suffix s (sa.getD p 0)) (suffix s (sa.getD (p + 1) 0))) :
    (checkOn s sa arr).2 = sa.length - 1 := by
  rw [checkOn, checkOnGo_cost s sa arr harr (sa.length - 1) true 0 le_rfl, Nat.zero_add]

/-- **The `n − 1` is paid on computed data**: the counted checker run on *Kasai's* array
costs exactly `sa.length - 1` inspections, with no oracle involved (`kasai`'s entries are
the true LCPs, `kasai_lcp_correct_saLcp`). -/
theorem checkOn_computed_cost (s : List α) (sa : List ℕ) (hsa : IsSaCandidate s sa)
    (hsorted : Verified s sa) :
    (checkOn s sa (fun p => (kasai s sa).1.getD p 0)).2 = sa.length - 1 := by
  apply checkOn_cost
  intro p hp
  simpa [saLcp] using kasai_lcp_correct_saLcp s sa hsa hsorted hp

end SortBounds.Projects.SAIS