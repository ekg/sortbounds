# attractor — an anytime search for small string attractors

`r` is solved and `χ` (suffixient sets) is what `pangenome/sxgc` already exploits.
The measure that would *improve a grammar* is `γ`, the smallest string attractor
(an attractor of size `c` yields an RLSLP of size `O(c log(n/c))`). `γ` is NP-hard,
so the only honest interface is:

    report a certified bracket  [LB, UB]  and improve both ends with more budget.

## The exact reduction (no loss)

Minimum attractor **is** minimum set cover:

* universe  = distinct nonempty factors of `S`;
* for each position `p`, the set `cover(p)` = factors having an occurrence crossing `p`;
* `Γ` is an attractor ⟺ `⋃_{p∈Γ} cover(p)` = universe.

Consequences used by the tool: greedy gives `O(log U)`; any `Γ` is verifiable in one
pass (`check` from `tools/repmeter`); and the LP/dual and packing bounds are lower
bounds on `γ`.

The universe here is not the naive `Θ(n²)` one: it is the set of **suffix-tree nodes**,
of which there are at most `2n−1` (see *Two lemmas* below). Everything in this
directory — the bit masks, the greedy, the DFS — works on that reduced instance,
which is exact, not an approximation.

## Two certified ends

* **UB** — an explicit set of positions, verified by an *independent* checker
  (every distinct factor has an occurrence crossing `Γ`). Monotone: the tool only
  accepts a new `Γ` that is strictly smaller.
* **LB** — the maximum of:
  1. `δ` = `max_k d_k/k` (KNP: `δ ≤ γ`), computed exactly from SA/LCP;
  2. a **packing bound**: factors `f_1..f_k` such that no position covers two of them
     ⇒ `γ ≥ k`. Certified by exhibiting the factors and the incompatibility.
  3. (optional) a validated LP-dual bound if you implement one — must come with a
     checkable dual solution, never a solver's word.

## Any-time schedule (each step only ever improves)

1. **Greedy**: repeatedly take the position covering the most uncovered factors.
2. **Irredundant prune**: drop any position whose removal keeps the cover.
3. **Local search**: try `1↔1` swaps (move a position, re-cover, prune) and
   `2↔1` replacements; accept only strict improvements.
4. **Exact tail**: iterative deepening over `k = LB, LB+1, …` deciding "is there an
   attractor of size ≤ k" by DFS/SAT with the packing and `δ` pruning. This is only
   run while `k ≤ |Γ|` and the budget allows.
5. Every accepted `Γ` is printed with a timestamp, its size, and the current bracket.

## Contract

```python
# instance.py
class Instance:
    def __init__(self, text): ...          # from SA+LCP; elements are SA-intervals
    def uncovered(self, gamma) -> int      # how many distinct factors are uncovered
    def verify(self, gamma) -> bool        # INDEPENDENT definition-level check
    def delta(self) -> Fraction            # exact substring complexity
    def packing_bound(self) -> tuple[int, list]   # (k, witness factors)

# anytime.py
def search(inst, budget_s=60.0, seed=0) -> Iterator[dict]
    # yields {"t":…, "gamma":[…], "ub":…, "lb":…} on every improvement, and at the end
```
**Acceptance tests** (must be in `check.py`, must exit non-zero on failure):
1. For every binary string of length ≤ 12: `verify` accepts the greedy result, and for
   `n ≤ 12` the *exact* `γ` (exhaustive) is bracketed by `[lb, ub]`.
2. On `"mississippi"` the exact `γ = 4` and the tool's search reaches 4 within budget.
3. On the Thue–Morse family the packing bound must exceed `δ` at some `n` (that is the
   whole point of a second lower bound) — if it never does, say so honestly instead of
   faking it.
4. `search` never yields a *larger* `Γ` than a previous yield (monotonicity), and never
   yields an unverified one.

## Rules

stdlib only; `timeout` every run; assert progress in every loop (a loop that does not
strictly improve must terminate).  No number printed without either a proof-shaped
certificate (`δ`, packing) or an explicit "not computed".  This directory is Python
tooling; the Lean side is `SortBounds/Projects/Repetitiveness`.

---

# Implementation

| file | what it is |
| --- | --- |
| `instance.py` | the set-cover instance of one text: suffix-tree nodes, cover/element bit masks, `delta`, `uncovered`, `verify`, `packing_bound`, `certify_packing` |
| `anytime.py` | the search: greedy, prune, local search, GRASP restarts, exact DFS tail; `search()` generator and a CLI |
| `check.py` | 283k acceptance/consistency assertions; exits non-zero on the first class of failure |
| `run.sh` | reproduces the results table below (~2 minutes) |
| `README.md` | this file |

Only four things are imported from `tools/repmeter`: `suffix_array`, `lcp_array`,
`dk_profile`/`delta_exact` (via `Instance.delta`) and `RangeMin`. The attractor logic
— coverage, verification, packing, search — is written here.

```sh
timeout 120 python3 anytime.py --text "mississippi" --budget 60
timeout 120 python3 anytime.py --gen thue-morse:10 --budget 60
timeout 120 python3 anytime.py --gen random-binary:1024:1 --budget 60
timeout 600 python3 check.py        # 17 s, must print OK
timeout 600 sh run.sh               # the table below
```

The CLI prints every accepted `Γ` with its timestamp and bracket, and at the end the
lower-bound certificate itself — the witness factors (as text) and the result of
re-checking that no position crosses two of them:

```
$ timeout 120 python3 anytime.py --text "mississippi" --budget 3
  0.000s  bracket=[4, 4]  phase=greedy      gamma=[0, 5, 7, 9]
  0.000s  bracket=[4, 4]  phase=done        gamma=[0, 5, 7, 9]
input       : text 'mississippi'
n           : 11
delta       : 4  (KNP: delta <= gamma)
packing     : 4  (gamma >= 4: 4 factors, pairwise disjoint crossing-position sets)
witnesses   : i p s m
              re-checked from the text: OK
bracket     : 4 <= gamma <= 4   ==> gamma = 4 exactly
```

## Two lemmas the tool relies on

Both are derivations, not optimisations; each is checked mechanically in `check.py`.

**(R1) The universe is the set of suffix-tree nodes.**  A node `v` owns the factors of
length `pd(v)+1 … d(v)` (`pd` = parent depth), and every one of them occurs exactly at
the starts `sa[lo..hi]` of `v`'s SA interval.  Therefore

> `Γ` is an attractor ⟺ for every node `v`, the *shortest* factor of `v` is covered.

(⇐) let `f` be owned by `v` and `|f| ≥ min_len(v)`; if the occurrence `[i, i+min_len)`
of the shortest factor crosses `p`, then `[i, i+|f|) ⊇ [i, i+min_len)` also contains `p`.
(⇒) the shortest factor is itself a distinct factor.
`check.py` confirms the stronger statement — the set of `(node, length)` pairs *is* the
set of distinct factors — for every binary string of length ≤ 8.

**(R2) Representatives suffice for the packing bound.**  For a factor `f` let
`C(f) = {p : p crosses some occurrence of f}`.  Factors of one node share their
occurrence set and a longer window at the same start contains the shorter one, so
`C(f) ⊇ C(shortest factor of v)` for every `f` owned by `v`, and two factors of the same
node always have intersecting `C`.  Hence any pairwise-disjoint family of `C`-sets can
be replaced, element by element, by the shortest factors of the corresponding nodes; the
maximum packing is attained on representatives.  So enumerating only `min_len(v)` factors
loses nothing.

## The packing bound is a lower bound (why)

Fix factors `f_1 … f_k` with `C(f_i) ∩ C(f_j) = ∅` for `i ≠ j`.  Every `f_i` is a
distinct factor of `S`, so any attractor `Γ` must contain a position `p_i` crossing an
occurrence of `f_i`, i.e. `p_i ∈ C(f_i)`.  If `p_i = p_j` then that position is in
`C(f_i) ∩ C(f_j) = ∅`, a contradiction, so `p_1 … p_k` are `k` distinct positions and
`|Γ| ≥ k`.  The bound is certified, not estimated:

* the witnesses are printed as the actual factor strings (`packing_bound` returns
  `(k, [(node, factor, text), …])`);
* `Instance.certify_packing` re-derives each `C(f_i)` **from the text** (scan every
  start, union the intervals `[i, i+|f_i|)`), and then checks (a) every pair of sets is
  disjoint and (b) no position belongs to two sets.  Only after that does `search`
  report the bound.  The family is found by a greedy over the elements ordered by
  `|C|` ascending, with restarts (`seed`, 32 restarts); greedy is a heuristic *for
  finding* the family, the certificate is what makes the number a bound.

Consistency with exhaustive `γ`: for every text in the table the packing bound is `≤` the
exhaustive `γ` whenever `γ` is known, as it must be, and `check.py` asserts
`packing ≤ γ ≤ greedy` for all 8190 binary strings of length ≤ 12.

## Results

`sh run.sh` prints this table itself (as markdown); the numbers below are that output,
with the `2⁴`/`F₁₄` labels and the fractions tidied by hand.  This machine, 60 s budget
per row.  `δ` is `d_k/k` at its argmax, as an
exact fraction.  "greedy+prune" is *this* tool's phases 1+2; "repmeter greedy" is
`tools/repmeter/measure.py`'s longest-uncovered-factor greedy (skipped above n = 1024,
hence "not computed").  `ub @ t` is the best *verified* upper bound the search had
produced `t` seconds into that run — not a bound from a longer run.

| text | n | δ | pack LB | greedy+prune | repmeter greedy | ub @ 1 s | ub @ 10 s | ub @ 60 s | γ | bracket |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `a` | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 (bracket closed) | [1, 1] |
| `ab` | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 (bracket closed) | [2, 2] |
| `ababa` | 5 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 (bracket closed) | [2, 2] |
| `mississippi` | 11 | 4 | 4 | 4 | 7 | 4 | 4 | 4 | 4 (bracket closed) | [4, 4] |
| `abracadabra` | 11 | 5 | 5 | 5 | 6 | 5 | 5 | 5 | 5 (bracket closed) | [5, 5] |
| Thue–Morse `2⁴` | 16 | 5/2 = 2.5 | 3 | 4 | 4 | 4 | 4 | 4 | 4 (bracket closed) | [4, 4] |
| Thue–Morse `2⁶` | 64 | 40/13 ≈ 3.0769 | 3 | 4 | 4 | 4 | 4 | 4 | 4 (bracket closed) | [4, 4] |
| Thue–Morse `2⁸` | 256 | 160/49 ≈ 3.2653 | 3 | 4 | 4 | 4 | 4 | 4 | 4 (bracket closed) | [4, 4] |
| Thue–Morse `2¹⁰` | 1024 | 640/193 ≈ 3.3161 | 3 | 4 | 4 | 4 | 4 | 4 | 4 (bracket closed) | [4, 4] |
| Fibonacci `F₁₄` | 377 | 2 | 2 | 2 | **5** | 2 | 2 | 2 | 2 (bracket closed) | [2, 2] |
| Fibonacci `F₁₈` | 2584 | 2 | 2 | 2 | not computed | 2 | 2 | 2 | 2 (bracket closed) | [2, 2] |
| random binary, 64, seed 3 | 64 | 49/8 = 6.125 | 7 | 8 | 11 | 7 | 7 | 7 | 7 (bracket closed) | [7, 7] |
| random binary, 256, seed 1 | 256 | 200/9 ≈ 22.2222 | 26 | 35 | 38 | 28 | 28 | 28 | not computed | [26, 28] |
| random binary, 512, seed 1 | 512 | 81/2 = 40.5 | 49 | 60 | 64 | 53 | 52 | 52 | not computed | [49, 52] |
| random binary, 1024, seed 1 | 1024 | 913/12 ≈ 76.0833 | 91 | 108 | 127 | 99 | 99 | 99 | not computed | [91, 99] |
| random binary, 2048, seed 1 | 2048 | 1824/13 ≈ 140.3077 | 165 | 212 | not computed | 212 | 183 | 179 | not computed | [165, 179] |

What the table says.

* **Thue–Morse: `γ = 4`, proved, for `n = 16 … 1024`.**  For `n ≥ 64` the bracket closes
  on the lower side alone (`⌈δ⌉ = ⌈3.0769…⌉ = 4`), which is the cleanest possible use of
  `δ ≤ γ`.  At `n = 16` `⌈δ⌉ = 3` and the packing bound is 3, so `lb = 3 < ub = 4`; there
  the exact tail proved that no attractor of size 3 exists, which closed the bracket.
  (Machine-checked for these lengths only — not a theorem for all `k`.)
* **Fibonacci words: `γ = 2`, and `γ = δ`.**  The bracket closes on `δ = 2` and the
  greedy reaches 2 (e.g. `Γ = {1595, 1596}` for `F₁₈`: every factor of the Fibonacci word
  has an occurrence crossing the middle two positions).  repmeter's greedy reports 5 for
  `F₁₄` — **the previous upper bound was 2.5× too large**, and its bracket `[2, 5]` was
  wide where `[2, 2]` is available.  This is the single most useful number here.
* **`mississippi`: 7 → 4.**  repmeter's greedy gives 7 against `γ = 4`; the max-coverage
  greedy + prune gives 4 immediately, and the packing bound (`i`, `p`, `s`, `m` — four
  single-symbol factors, whose crossing-position sets are disjoint) certifies it.
* **The search strictly improves on its own greedy.**  `random-binary 256`: 35 → 28
  (−20 %, local search plus restarts).  `random-binary 2048`: 212 → 179 (−33, −16 %) at
  60 s.  `random-binary 1024`: 108 → 99 by 1 s.  It never gets *worse*: ub is monotone by
  construction and every yield is verified.
* **On incompressible text the packing bound beats `δ` and the bracket stays open.**
  `n = 2048`: `δ = 140.31` but the packing certifies `γ ≥ 165`, and the search's ub is
  179, so `[165, 179]` (9 % wide) instead of `[141, 212]` (50 % wide).  `δ` alone would
  have been 18 % below the certified bound.  `γ` is still unknown there: NP-hard.
* **Sizes.**  The table stops at `n = 2584` (Fibonacci) / `n = 2048` (random) because
  that is where 60 s of this Python still buys something.  At `n = 4096` random the
  instance builds in 0.1 s, greedy+prune gives 374 at 1.2 s, the local search reaches 332
  at 44 s, and nothing is left for restarts or the exact tail: bracket `[305, 332]`.
  At `n = 8192` the greedy alone gives 716 in 2.7 s and the local search does not finish
  a sweep inside a minute.

## What is certified, what is heuristic

| quantity | status |
| --- | --- |
| `δ` | exact rational, from SA+LCP (`δ ≤ γ` is KNP's theorem, quoted, not re-proved here) |
| packing LB | **certified**: witnesses + pairwise-disjoint `C`-sets re-derived from the text |
| `lb` after "exact tail" | **certified**: a completed DFS proved no attractor of size `k` |
| any reported `Γ` | **certified**: `Instance.verify` re-checks the definition from scratch |
| `ub` | certified as an upper bound; **not** claimed optimal unless `lb = ub` |
| exact tail finding *solutions* | heuristic in practice (node cap; see below) |
| greedy / local search / restarts | pure heuristics; only their *output* is certified |

`Instance.verify` is deliberately not the fast path.  It ignores `cover_masks`,
`elem_masks`, `uncovered` and the greedy's bookkeeping entirely: it walks the nodes,
and for each one takes its occurrence starts and tests the concrete interval
`[i, i+min_len)` against the sorted point list with a binary search.  It is cross-checked
two ways: against a raw window-enumerating reading of the definition **for every position
set of every binary string of length ≤ 8** (and random sets above that), and against
repmeter's independent brute-force and suffix-tree verifiers.

`search`'s monotonicity and verifiedness are enforced structurally: `consider()` refuses
any candidate that is not strictly smaller than the current best and raises
`AssertionError` if `witness(cand)` is not `None`, so an unverified `Γ` cannot be yielded.

## What did not work

1. **A fractional (LP-dual) lower bound, in two forms, was always dominated by the
   integral packing.**  (a) Greedy dual ascent — give element `v` weight
   `min over p ∈ C(v) of (1 − load(p))`, in units of `1/n`; it is a valid dual
   (`check`-able: every position's load ≤ 1) and it reproduces the packing when elements
   are disjoint, but once a packing element gets weight 1 every position of its `C` is
   saturated, so any element sharing a position with it must get weight 0.  On
   `random-binary 1024` it gave **78** against the packing's **91**.  (b) Uniform
   fractional weights on an `M`-overlap family (`|F| / max_p |{f ∈ F : p ∈ C(f)}|`):
   best over `M = 2,3,4,8` was **82** on the same text.  Both are cheaper to state than
   the packing and both are weaker here, so neither is shipped.  A real LP solver is out
   of scope (stdlib only) and would need its dual solution checked anyway.
2. **Improving the packing family by 1-out-2-in local search found nothing** on the four
   instances tried (`random-binary` 256/512/1024, Thue–Morse `2¹⁰`): the greedy family
   sorted by `|C|` is already 2-optimal there, because the bound is essentially a
   knapsack — take as many small `|C|` factors as fit into `n` positions — and the greedy
   is optimal for that relaxation.
3. **The exact tail is a poor way to *find* attractors on incompressible text.**  It
   proves infeasibility well (it closed `k = 3` for Thue–Morse `2⁴`, and `k = 25` for
   `random-binary 256` in milliseconds, thanks to the packing prune: 26 disjoint factors
   cannot fit in 25 slots), but at `k = 28` on the same text it did not find the 28-set
   the greedy had found in 0.1 s, within 200 000 nodes.  Infeasibility proofs are a
   ∧-shaped search that pruning helps; finding a cover needs the greedy/repair structure
   that phase 1–3 provides.  So the tail is used mainly to raise `lb`.
4. **`uncovered()` (the counting fast path) was not usable as the verifier**, tempting as
   the speed was: it shares the suffix-tree/range-minimum machinery with the rest of the
   tool, so a bug there would have been invisible.  It is kept as the counting API and
   cross-checked against `verify` on every position set of every binary string ≤ 8
   (87 380 comparisons of the *count*, not just of zero/non-zero).

## Self-tests

`timeout 600 python3 check.py` — 283 545 assertions, 0 failures, ~17 s:

| test | what it pins down |
| --- | --- |
| 1 | node/`length` pairs = distinct factors (bijection, not just a count); `verify` = raw window enumeration for **all** `Γ` on all binary strings `n ≤ 8`; `uncovered`'s count matches the definition (87 380 of the latter) |
| 1b | `verify` = raw definition and = repmeter's brute force on longer texts, random `Γ` |
| 1c | every binary string `n ≤ 12`: greedy verified, exact `γ` from a complete DFS = `γ` from subset enumeration, `lb ≤ γ ≤ ub`, packing ≤ `γ` and its certificate re-checks |
| 1d | `exact_gamma` = repmeter's `gamma_bruteforce` on all binary strings `n ≤ 10` |
| 2 | `mississippi`: `γ = 4`, the search reaches `ub = lb = 4` |
| 3 | Thue–Morse: packing > `δ` at `n = 16, 32` (3 > 2.5, 3 > 2.857) — it is printed honestly on both sides of the crossover |
| 4 | monotonicity: `ub` never grows, every yield verified, `lb ≤ ub`, last record is `done` |
| 5 | the search beats its own greedy (`random-binary 256`: 35 → 28) |
| 6 | the README's headline claims (`γ = 4` for Thue–Morse `2⁸`, `2¹⁰`; `γ = 2` for `F₁₄`), each accepted by *two* independent verifiers |
| 7 | the lazy (CELF) greedy returns exactly the exhaustive-scan greedy's answer, all binary `n ≤ 12` |

## Costs and limits, honestly

* `Instance.__init__`: `O(n log²n)` prefix-doubling SA + `O(Σ_v |occ(v)|)` for the masks.
  Measured: 0.3 s at `n = 8192` random, 0.03 s at `n = 987` Fibonacci.
* one greedy round: `O(n)` big-int popcounts of `m`-bit masks; the CELF heap makes a
  whole greedy ~2.7 s at `n = 8192` (it was 98 s with a full scan per round).
* `verify`: `O(Σ_v |occ(v)|)` with early exit — the whole definition, no bookkeeping.
* local search: `O(m)` mask unions per pair in `2→1`, i.e. `O(m³/64)` bit-ops per sweep;
  this is the phase that stops scaling first (43 s for one chain at `n = 4096`).
* the DFS node cap (default 200 000 per `k`) and the deadline are the only two limits;
  when either is hit the tail concludes *nothing* (`status = "budget"`), so an
  interrupted run can only under-report, never over-claim.
* `δ ≤ γ` is used as a theorem (KNP), not re-derived; the packing bound is derived and
  re-checked here, and is independent of the alphabet or the text family.

## For the integrator

* The bracket on `γ` is now tight on every repetitive text in the table (`γ = 4` for
  Thue–Morse, `γ = 2` for Fibonacci words, `γ = 4` for `mississippi`), which is stronger
  than `δ ≤ γ`: on the Fibonacci words `δ` is **attained**, `γ = δ = 2`, so any claim of
  the form "`γ > δ` for Fibonacci words" is false; on Thue–Morse `γ = 4` while
  `δ = 3.0769…, 3.2653…, 3.3161…`, so `γ > δ` there but `⌈δ⌉ = γ`.
* On random text `γ` is *not* near `δ`: `δ = 140.31` vs certified `γ ≥ 165` at `n = 2048`.
  The packing bound is a second, genuinely different certificate (`δ` counts factors,
  the packing counts *positions* that cannot be shared) and it is the better one on
  incompressible text.
* repmeter's greedy UB should not be used as a proxy for `γ`: it is 7 vs 4 on
  `mississippi` and 5 vs 2 on `F₁₄`.
