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

---

# Implementation

| file | what it is |
| --- | --- |
| `lz.py` | greedy LZ77 (hash chains on 3-grams + a 2-gram chain, lcp by binary search on slice equality); produces `Phrase(start, length, dist)`, `dist == 0` meaning a literal. Overlapping ("self-referencing") copies by default, `overlap=False` for the prefix-only variant |
| `attractor_from_lz.py` | KP18 Lemma 3.7: `Gamma_LZ = { e_j }`, the **last character of each phrase**, one position per phrase. The docstring carries the two-case proof that every distinct factor has an occurrence crossing `Gamma_LZ` |
| `verify.py` | independent checking, no knowledge of LZ77: the definition-level `find_uncovered_factor_definition` (enumerate every distinct factor, test every occurrence against the sorted position list) and the O(n log n) `find_uncovered_factor_suffix_array` (suffix-tree node criterion, proved in the docstring, and it asserts that the nodes partition the distinct factors). Also carries the suffix array, LCP array and `delta` |
| `check.py` | self-tests; exits non-zero on failure (651 627 assertions, 4 s) |
| `run.py` | the results table below; also `exact_gamma` (exhaustive hitting set, n <= 14) and the generative texts |

```sh
timeout 120 python3 check.py      # 4 s, must print OK
timeout 120 python3 run.py        # 4 s, the table below
timeout 120 python3 verify.py --text ababa --gamma 0,1,4   # one-off check, exit 1 if not an attractor
```

## The construction (KP18 Lemma 3.7, PROVED)

Parse `S` into `z` phrases `[b_j, e_j]`; emit `e_j` for every `j`.  `|Gamma_LZ| = z`
exactly (phrase ends are distinct), and the two-case argument in
`attractor_from_lz.py` shows every distinct factor is covered: taking the leftmost
occurrence of a factor, either it runs past its phrase's end (`e_j` is inside it)
or it sits inside a copy phrase, which would make it occur `d` positions earlier.
Hence `delta <= gamma <= |Gamma_LZ| = z`, and with `z <= 4(delta log(n/delta)+delta)`
(KNP23 II.2) an `O(log n)` ratio — **not** a constant one; nothing here claims
`gamma = z` or a constant-factor approximation.

## Results (`timeout 120 python3 run.py`, 4 s)

Every `Gamma_LZ` in this table was verified **before** its size was printed: the
definition-level checker for every row with `n <= 400` and the O(n log n) node
checker for every row, and the two must agree.  `gamma` is exact only where the row
says so: exhaustively for `n <= 14`, otherwise the certified bracket
`[ceil(delta), |Gamma_LZ|]`.  `F_1 = a, F_2 = ab, F_k = F_{k-1}F_{k-2}` so
`|F_k| = Fib_k` (the numbering of `../attractor` and `../repmeter`); the random text
is `random.Random(1).getrandbits(1)`.

| text | n | z | delta | \|Gamma_LZ\| | \|Gamma_LZ\|/z | \|Gamma_LZ\|/delta | gamma |
| --- | --- | --- | --- | --- | --- | --- | --- |
| "ababa" | 5 | 3 | 2 | 3 | 1 | 3/2 = 1.5000 | γ = 2 [exhaustive] |
| "mississippi" | 11 | 8 | 4 | 8 | 1 | 2 | γ = 4 [exhaustive] |
| Fibonacci F_10 | 55 | 9 | 2 | 9 | 1 | 9/2 = 4.5000 | γ ∈ [2, 9] [delta ≤ γ ≤ \|Gamma_LZ\|] |
| Fibonacci F_11 | 89 | 10 | 2 | 10 | 1 | 5 | γ ∈ [2, 10] [delta ≤ γ ≤ \|Gamma_LZ\|] |
| Fibonacci F_12 | 144 | 11 | 2 | 11 | 1 | 11/2 = 5.5000 | γ ∈ [2, 11] [delta ≤ γ ≤ \|Gamma_LZ\|] |
| Fibonacci F_13 | 233 | 12 | 2 | 12 | 1 | 6 | γ ∈ [2, 12] [delta ≤ γ ≤ \|Gamma_LZ\|] |
| Fibonacci F_14 | 377 | 13 | 2 | 13 | 1 | 13/2 = 6.5000 | γ ∈ [2, 13] [delta ≤ γ ≤ \|Gamma_LZ\|] |
| Fibonacci F_15 | 610 | 14 | 2 | 14 | 1 | 7 | γ ∈ [2, 14] [delta ≤ γ ≤ \|Gamma_LZ\|] |
| Fibonacci F_16 | 987 | 15 | 2 | 15 | 1 | 15/2 = 7.5000 | γ ∈ [2, 15] [delta ≤ γ ≤ \|Gamma_LZ\|] |
| Fibonacci F_17 | 1597 | 16 | 2 | 16 | 1 | 8 | γ ∈ [2, 16] [delta ≤ γ ≤ \|Gamma_LZ\|] |
| Fibonacci F_18 | 2584 | 17 | 2 | 17 | 1 | 17/2 = 8.5000 | γ ∈ [2, 17] [delta ≤ γ ≤ \|Gamma_LZ\|] |
| Thue-Morse 2^12 | 4096 | 24 | 2560/769 = 3.3290 | 24 | 1 | 2307/320 = 7.2094 | γ ∈ [4, 24] [delta ≤ γ ≤ \|Gamma_LZ\|] |
| Thue-Morse 2^16 | 65536 | 32 | 40960/12289 = 3.3331 | 32 | 1 | 12289/1280 = 9.6008 | γ ∈ [4, 32] [delta ≤ γ ≤ \|Gamma_LZ\|] |
| a^100 | 100 | 2 | 1 | 2 | 1 | 2 | γ = 1 [singleton [0] verified] |
| a^1000 | 1000 | 2 | 1 | 2 | 1 | 2 | γ = 1 [singleton [0] verified] |
| random binary 4096 | 4096 | 386 | 1793/7 = 256.1429 | 386 | 1 | 2702/1793 = 1.5070 | γ ∈ [257, 386] [delta ≤ γ ≤ \|Gamma_LZ\|] |

`|Gamma_LZ| <= z` and `delta <= |Gamma_LZ|` held on **every** row and on every
binary text of length 1..12 (`check.py` [3], 8 190 texts): `|Gamma_LZ|/z = 1`
everywhere, because the construction emits exactly `z` positions.  The worst
`|Gamma_LZ|/delta` among those 8 190 texts is **4.0** (the text `000100000101`:
n = 12, `delta = 2`, `z = |Gamma_LZ| = 8`), and in the table it is **9.60**
(Thue-Morse `2^16`), which is the `Theta(log n)` growth of the bound showing up —
not a violation of it.

What the table says.

* **The two published anchors reproduce exactly.**  `z(t_n) = 2n` on Thue-Morse
  (`24` at `2^12`, `32` at `2^16`; KTMSIT20) and `z(F_k) = k-1` on Fibonacci with
  `|F_k| = Fib_k`, i.e. `z = m` on the word of length `Fib_{m+1}` (W25 Thm 10, up to
  the indexing offset).  A *bounded* `z` on these families would have refuted those
  papers; it does not happen.
* **`|Gamma_LZ|/gamma` is not constant, as predicted (C1).**  With the *cited*
  `gamma(t_n) = 4` (KTMSIT20) and `gamma(F_k) = 2` (BBGKM26), `|Gamma_LZ|/gamma` is
  `8` at `t_16` (`= log_2 n / 2`) and `8.5` at `F_18` (`= 0.72 log_2 n`).  Those
  `gamma` values are **citations**, not measurements from this directory — the tool's
  own certified bracket is `[delta, |Gamma_LZ|]`, e.g. `[4, 32]` and `[2, 17]`.
* **On unary text the construction is a factor 2 off**: `z(a^n) = 2` and `gamma = 1`
  (the singleton `{0}` is verified), so `|Gamma_LZ|/gamma = 2` for any `a^n`.  Even
  where the LZ parse is optimal-ish (two phrases for any `a^n`) the ratio is 2, not 1.
* **The ratio is mildest on random text** (`1.507` in `delta`), where `delta` is
  already within a constant factor of `gamma` — the direction in which the `z` bound
  is least lossy.

What is **not** claimed, and must not be read into the table:

* `gamma != z` in general; `|Gamma_LZ|` equals `z`, which is not a minimum.
* No constant-factor, `o(log n)`, or "practical approximation" statement.  The only
  proved ratio is `4 log(n/gamma) + 4` (MY-INFERENCE chaining KP18 L3.7, KNP23 II.2
  and II.4; see `docs/research/attractor-approx.md` §1.1).
* `Gamma_LZ` is a certificate, not a good attractor: `../attractor`'s greedy+prune
  beats it on every text where both numbers are known — random binary 256 (seed 1):
  `43` here vs `35` there; `t_10`: `20` vs `4` (`= gamma`); `F_14`: `13` vs `2`
  (`= gamma`); `"mississippi"`: `8` vs `4` (`= gamma`, and `4` is exhaustive here
  too).  Use it as the baseline the anytime search starts from, not as the answer.

## An observation beyond the contract

The **phrase starts** `{ b_j }` are also an attractor, by the same two-case argument
with the roles of the two cases swapped (`attractor_from_lz.py`, "REMARK"), and with
the same size `z`.  This is **MY-INFERENCE**, not in `docs/research/attractor-approx.md`;
`check.py` [5'] confirms it on every binary text of length <= 10 and `run.py` on every
row.  It is recorded because it says the construction does not need the *ends* in
particular — any one position per phrase works as long as it is chosen by phrase, so
the `z` bound is robust to that choice, and no smaller choice is available without
leaving the parse.

## Independent verification, and how it is trusted

`verify.py` knows nothing about LZ77.  Two consequences worth knowing:

1. `verify.py`'s fast path uses the suffix-tree node criterion (every distinct factor
   is the shortest factor of some node), so it is a *proof* only if that lemma holds;
   `check.py` therefore compares three implementations — the definition-level one, the
   node one, and a third naive one written inside `check.py` — on **every subset of
   every binary text of length <= 7** (21 844 cases), on all 2 048 subsets of
   `"mississippi"`, and on 900 random (text, position-set) pairs up to n = 59, with
   0 disagreements.  `delta` and the exhaustive `gamma` were additionally compared
   against `../repmeter`'s independent implementations on 61 cases (0 mismatches).
2. `check.py` [4] also shows the verifier has teeth: 268 of 1 020 deliberately wrong
   position sets (stride-2 sets, and `Gamma_LZ` minus its last element) are rejected.

The `run.py` guard means an unverified `Gamma` cannot reach the table: a single
failing witness aborts with `FAIL <row>: Gamma_LZ is NOT an attractor`, and a row with
`delta > |Gamma_LZ|` aborts instead of printing a number that would contradict
KNP23 II.4.
