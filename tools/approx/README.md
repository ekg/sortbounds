# approx — guaranteed-bound attractor constructions (theory + implementation)

The anytime search (`tools/attractor`) gives *empirical* upper bounds. This directory is
about bounds that are **proved before you measure**: constructions whose size is bounded by
a function of a computable measure, hence an approximation algorithm with a known ratio.

## What is already in reach (no new theory needed, but nobody packages it)

    γ ≤ z        an LZ77 parse of z phrases yields an attractor of size ≤ z
                 (Kempa–Prezza, Lemma 3.7 — constructive)
    γ ≤ g        an SLP of size g yields an attractor of size ≤ g (Kempa–Prezza Thm 3.5)
    z ≤ 4(δ log(n/δ) + δ)                        (KNP Lemma II.2, after Raskhodnikova et al.)
    δ ≤ γ                                        (KNP; machine-checked in this repo)
    ⟹  δ ≤ γ ≤ z ≤ 4(δ log(n/δ)+δ)   ⇒  |Γ_LZ| / γ ≤ 4 log(n/γ) + O(1)

So: **a computable attractor with a proven `O(log n)` ratio, from a linear-time parse.**
That is a guarantee, not a heuristic — and it is the seed the anytime search should start
from, and the benchmark any heuristic must beat.

## The structural questions this directory is for

1. **Why `log n`, and is it necessary?** `γ/δ = Θ(log n log log n)` is achievable
   (Kempa–Kociumaka Thm 4.3), while `δ` is computable. So *any* algorithm whose lower bound
   is only `δ` cannot beat a `log n` factor. Can an algorithm use structure to do better
   than the `z`-based bound — e.g. a **constant-factor** approximation, or exact for
   restricted families (periodic, Fibonacci, Thue–Morse, unary-run, bounded `k`)?
2. **The interval structure.** For a *fixed* `k`, factor `S[i..i+k)` is covered by positions
   `p ∈ [i, i+k)` — consecutive positions. So for one `k`, the instance is "stab the unions
   of length-`k` intervals", and *if the occurrences of each factor were disjoint* it would
   be interval stabbing, solvable exactly by the right-endpoint greedy. The union over all
   `k` is what breaks it. Questions: what is the integrality gap of the set-cover LP on this
   family? Is the `k`-attractor problem (fixed `k`) exactly solvable in polynomial time for
   *our* instances even though it is NP-hard in general (the general hardness is for
   `k ≥ 3` on general alphabets — what is the hardness for `σ = 2`)?
3. **Certified lower bounds beyond `δ`**: the packing bound (no position covers two chosen
   factors ⇒ `γ ≥ k`), LP-dual bounds, and any bound derived from `n`, `σ`, `z`, `r`, `χ`.
   Which are efficient to compute, and how close do they get to `γ` on real corpora?
4. **Interaction with `χ`** (`pangenome/sxgc`): `χ` is a suffixient-set size, a *locating*
   bound; `γ` is the grammar-side quantity. Measuring `γ`, `z`, `δ`, `χ` on the same texts
   is new information, and cheap.

## Contract

* `docs/research/attractor-approx.md` — the theory note: state of the art with citations and
  verdicts (PROVED / OPEN / UNVERIFIED), the structural lemmas, the constructions with their
  ratios, and an explicit list of *falsifiable conjectures* with the experiment that would
  settle each.
* `tools/approx/` — implement the `LZ77 → attractor` construction, verify the result with an
  **independent** checker, and measure `|Γ_LZ| / z`, `|Γ_LZ| / δ`, and (for `n ≤ 14`) `/ γ`.
  On Fibonacci, Thue–Morse, `aⁿ`, random, and a real repetitive sample if available.
* `tools/approx/check.py` — self-tests: on all binary strings of length ≤ 12, the constructed
  `Γ` passes the independent verifier and `δ ≤ |Γ| ≤ z` holds; exit non-zero otherwise.

## Rules

stdlib only; `timeout` on every run; assert progress in every loop; never print a number
without either a certificate or an explicit "not computed". No claim of a ratio that is not
derived above (in particular: do **not** claim `γ` is exactly `z`, and do not claim a
constant-factor algorithm you have not proved).
