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

end SortBounds.Projects.SAIS
