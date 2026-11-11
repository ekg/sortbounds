# Lane: SAIS — suffix arrays, and a cost model that LCP actually improves

**Status: QUEUED.** Correctness is solved elsewhere (Isabelle AFP `SuffixArray`,
2024; JAR 2025), so the only unclaimed and interesting target is the **cost
model**.

**Question.** Sorting the `n` suffixes of a string is *not* the comparison
problem we proved a bound for: (a) each comparison is over strings, so its cost is
the number of characters inspected, not 1; (b) keeping an LCP lower bound makes
comparisons start past the shared prefix; (c) the linear-time algorithms
(SA-IS, DC3) sort *integer ranks* with radix/counting, i.e. they leave the
comparison model — the same door radix sort uses.

**Target (M0/M1, when unblocked).**

```lean
namespace SortBounds.Projects.SAIS

/-- Suffix `i` of `s`. -/
def suffix (s : List α) (i : Fin s.length) : List α
/-- Cost model: a comparison of two suffixes costs `1 + characters examined past
the supplied LCP lower bound`. -/
def cmpCost (lcp : ℕ) (a b : List α) : ℕ
/-- M1: LCP-guided sorting of suffixes costs `O(n log n)` character inspections
(instead of `Θ(n²)` for naive comparison). -/
theorem lcp_guided_cost (s : List α) : …

end SortBounds.Projects.SAIS
```

**Blocked on:** lane `XY` (weighted cost model, same machinery). Do not start
before `XY` M1 lands.

## Prior art

Isabelle AFP `SuffixArray` (SA-IS correctness, 2024); Cheung thesis (SA-IS + BWT);
Kasai et al. 2001 (LCP in linear time); Manber–Myers 1993; Nong–Zhang–Chan 2009.

## Log

* (empty)
