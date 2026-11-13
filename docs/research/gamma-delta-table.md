# The gap γ − ⌈δ⌉ across string families, with certified bounds

`δ` (the KNP substring complexity, `max_k d_k/k`) is a lower bound on the smallest
attractor `γ` and is computable in linear time; `γ` is NP-hard.  So the natural hope is

> **(N)** `γ = ⌈δ⌉` on the strings compressed indexes actually see,

which would make `γ` exactly computable in `O(n)` there.  This note measures
`gap = γ − ⌈δ⌉` on 117 texts in 13 family groups (the families of the brief, with de Bruijn
split by alphabet size and `S S` / `S S^R` kept apart), each row carrying an **exact** `δ` and a
**certified bracket** `[lb, ub]` on `γ`.  Neither measure is re-implemented: `δ` comes from
`tools/attractor/instance.py::Instance.delta` (repmeter's `delta_exact`), and the bracket
from `tools/attractor/anytime.py::search`.  Every number below is machine-generated and
re-verified; see §8.

**Claim register used here** (the convention of `docs/research/README.md`):

| tag | meaning |
| --- | --- |
| PROVED | read in a primary source, cited in §10 |
| PROVED, cited | a theorem quoted in `docs/research/gamma-equals-delta.md` (lane C's note, which reads the paper); the primary source was **not** opened here — §1.1 says which of these are which |
| MY-COMPUTATION | computed by `run_families.py`; endpoints re-derived by `check.py` |
| MY-INFERENCE | derived by me from cited or computed facts, reasoning given |
| UNVERIFIED | not confirmed against a primary source here; §7 says what would settle it |

## 1. What "certified" means in every row

A row is a text `S` (n = |S|) and four certified objects:

* **`δ`, exact** — a rational number, `max_k d_k/k` over the `k`-profile of the suffix array.
  `δ ≤ γ` is KNP23 Lemma II.4 (PROVED, cited: quoted in `docs/research/attractor-approx.md`
  §1.1, and machine-checked in this repo as `substringComplexity_le_card_attractor`).  So
  `⌈δ⌉ ≤ γ` for every text, and `gap ≥ 0` is a theorem, not a measurement.
* **`ub`, certified upper bound** — an explicit set of positions accepted by
  `Instance.verify`, the *definition-level* checker (every distinct factor has an occurrence
  crossing some position of the set).  `ub = |Γ|`; it is optimal only when `lb = ub`.
* **`lb`, certified lower bound** — `max` of three independently checkable certificates:
  `⌈δ⌉`; a *packing* family of factors with pairwise-disjoint crossing-position sets
  (each such factor forces its own position, so `γ ≥` the family size — re-derived from the
  text by `certify_packing`); and, where `lb` exceeds both, a **completed DFS** at `k = lb−1`
  that proves no attractor of that size exists.
* **`bracket closed`** — `lb = ub`, so `γ` is known exactly.  `γ` is also exact when
  `n ≤ 14` (complete DFS).  Otherwise the row's `γ` is printed as **not computed** and the
  gap as an interval `[lb − ⌈δ⌉, ub − ⌈δ⌉]`: an interval, never a point estimate.

The three lower-bound certificates are not redundant: in this sweep `⌈δ⌉` alone is the
binding certificate in 11 rows, the packing bound alone in 38, the two tie in 61, and the
completed DFS is what settles 7 (MY-COMPUTATION, `results.json`).  On
`S S^R` at `n = 512` the packing bound is 9 above `⌈δ⌉`, which is the whole refutation in §6.

Families, all with several sizes (details in `run_families.py::family_cases`): `a^n`;
`(ab)^m`; Fibonacci words `F_k` (the golden-slope Sturmian word, 13 … 6765); Thue–Morse
`t_k` (4 … 8192); balanced periodic words of rational slope `p/q` (42 … 210) — **not**
Sturmian, since a rational slope is periodic (Morse–Hedlund 1940: Sturmian = aperiodic and
balanced, and `p(k) = k+1` characterises it); de Bruijn sequences of order `k` over
`σ = 2, 3, 4` (4 … 256); random over `σ = 2` and `σ = 4` (16 … 1024); run-length texts
`(a^L b^L)^m` (64 … 2048); and one repeated half `S S` and `S S^R` (16 … 512).

### 1.1 What is already settled before any measurement

Four citations fix the two ends of the question.  They are quoted from
`docs/research/gamma-equals-delta.md` (lane C's note, which reads the papers; **I did not open
them myself**, so these are "PROVED, cited there") — and §4–§7 below check the measurements
against each of them.

* **(N) is false in general, and false by more than a constant.** KNP23 Thm III.3: for every
  `n` and every integer `δ ∈ [2 .. n]` there is a string `S` of length `n` with
  `γ = Ω(δ log(n/δ))`; the family is `S_∞[i] = b` iff `i = 2^j`, and KNP23 Lemma III.2 states
  it has `δ ≤ 2` and `γ ≥ ½⌊log n⌋`.  With the upper bound `γ ≤ 4(δ log(n/δ) + δ)` (KP18
  Thm 3.5 and Lemma 3.7 with KNP23 Lemma II.2), that family has **`γ = Θ(log n)` with `δ ≤ 2`**,
  i.e. a gap that grows like `log n`.  So "how fast can the gap grow" has a proved worst-case
  answer: like `δ log(n/δ)`.
* **(N) holds, provably, for standard Sturmian words** — every one of them: `γ = 2`
  (MRRRS19 Thm 5) while `p(k) = k+1` forces `δ = 2` (MH40).  That is this note's
  `Fibonacci (Sturmian)` family.
* **(N) holds, provably, for Thue–Morse beyond the shortest lengths.**  `γ(t_n) = 4` for every
  `n ≥ 4` (KTMSIT20 Thm 3) and `δ(t_n) = 10/(3 + 2^{4−n})` (KTMSIT20 Thm 4), which is `5/2` and
  `20/7` at the two shortest lengths — so `⌈δ⌉ = 3 < 4 = γ` exactly there, and KTMSIT20 say
  those two were "verified by computation"; from `δ > 3` on, `⌈δ⌉ = 4 = γ`.  (Lane C's note
  adds that every TM *prefix* of length 25…59 also has `γ = 4 > ⌈δ⌉ = 3` — a stronger statement
  than the 2^k prefixes measured here.)
* **`γ = ⌈δ⌉` is not a consequence of `δ = d_1`.**  `aababb`, TM `2³`, `B(2,3)` all have
  `δ = d_1 = 2` and `γ = 3` (lane C §3.3) — §4 reproduces two of those rows independently.

What the citations do *not* pin down is which families sit where, and how the gap behaves
between the `δ = 2` regime and the `Θ(log n)` worst case.  That is what the tables are for.

## 2. Block 1 — per family: where `γ = ⌈δ⌉` and where it is more

| family | rows | computed | gamma known exactly | gamma = ceil(delta) | gamma > ceil(delta) | undecided | max certified gap | n range |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Fibonacci (Sturmian) | 14 | 14 | 14 | 14 | 0 | 0 | 0 | 13..6765 |
| Thue-Morse | 12 | 12 | 12 | 9 | 3 | 0 | 1 | 4..8192 |
| balanced periodic p/q | 9 | 9 | 9 | 9 | 0 | 0 | 0 | 42..210 |
| de Bruijn sigma=2 | 7 | 7 | 6 | 2 | 4 | 1 | 1 | 4..256 |
| de Bruijn sigma=3 | 1 | 1 | 1 | 1 | 0 | 0 | 0 | 9..9 |
| de Bruijn sigma=4 | 1 | 1 | 1 | 1 | 0 | 0 | 0 | 16..16 |
| periodic (ab)^n | 7 | 7 | 7 | 7 | 0 | 0 | 0 | 4..256 |
| random sigma=2 | 15 | 15 | 12 | 1 | 11 | 3 | 14 | 16..1024 |
| random sigma=4 | 10 | 10 | 6 | 1 | 5 | 4 | 14 | 16..512 |
| reverse square S S^R | 12 | 12 | 7 | 2 | 5 | 5 | 9 | 16..512 |
| run-length (a^L b^L)^m | 12 | 12 | 12 | 12 | 0 | 0 | 0 | 64..2048 |
| square S S | 12 | 12 | 9 | 5 | 4 | 3 | 3 | 16..512 |
| unary a^n | 5 | 5 | 5 | 5 | 0 | 0 | 0 | 4..256 |

## 3. Block 2 — every row

`δ` is exact (and given as a fraction); `lb`/`ub` are certified; `γ` is printed only when
it is exact; `gap` is `γ − ⌈δ⌉` when `γ` is exact and the interval `[lb−⌈δ⌉, ub−⌈δ⌉]`
otherwise.  `CLOSED, fallback` marks a row where `anytime.search` crashed and the row was
measured with the same primitives re-scheduled (§9) — the endpoints are certified the same
way.

| family | text | n | delta | ceil(delta) | lb | ub | gamma | bracket | gap = gamma - ceil(delta) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| unary a^n | a^4 | 4 | 1 | 1 | 1 | 1 | 1 (bracket closed) | CLOSED | 0 |
| unary a^n | a^8 | 8 | 1 | 1 | 1 | 1 | 1 (bracket closed) | CLOSED | 0 |
| unary a^n | a^16 | 16 | 1 | 1 | 1 | 1 | 1 (bracket closed) | CLOSED | 0 |
| unary a^n | a^64 | 64 | 1 | 1 | 1 | 1 | 1 (bracket closed) | CLOSED | 0 |
| unary a^n | a^256 | 256 | 1 | 1 | 1 | 1 | 1 (bracket closed) | CLOSED | 0 |
| periodic (ab)^n | (ab)^2 | 4 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| periodic (ab)^n | (ab)^4 | 8 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| periodic (ab)^n | (ab)^8 | 16 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| periodic (ab)^n | (ab)^16 | 32 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| periodic (ab)^n | (ab)^32 | 64 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| periodic (ab)^n | (ab)^64 | 128 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| periodic (ab)^n | (ab)^128 | 256 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_7 | 13 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_8 | 21 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_9 | 34 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_10 | 55 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_11 | 89 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_12 | 144 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_13 | 233 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_14 | 377 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_15 | 610 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_16 | 987 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_17 | 1597 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_18 | 2584 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_19 | 4181 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Fibonacci (Sturmian) | F_20 | 6765 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Thue-Morse | t_2 | 4 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| Thue-Morse | t_3 | 8 | 2 | 2 | 3 | 3 | 3 (bracket closed) | CLOSED, fallback | 1 |
| Thue-Morse | t_4 | 16 | `5/2` | 3 | 4 | 4 | 4 (bracket closed) | CLOSED | 1 |
| Thue-Morse | t_5 | 32 | `20/7` | 3 | 4 | 4 | 4 (bracket closed) | CLOSED | 1 |
| Thue-Morse | t_6 | 64 | `40/13` | 4 | 4 | 4 | 4 (bracket closed) | CLOSED | 0 |
| Thue-Morse | t_7 | 128 | `16/5` | 4 | 4 | 4 | 4 (bracket closed) | CLOSED | 0 |
| Thue-Morse | t_8 | 256 | `160/49` | 4 | 4 | 4 | 4 (bracket closed) | CLOSED | 0 |
| Thue-Morse | t_9 | 512 | `320/97` | 4 | 4 | 4 | 4 (bracket closed) | CLOSED | 0 |
| Thue-Morse | t_10 | 1024 | `640/193` | 4 | 4 | 4 | 4 (bracket closed) | CLOSED | 0 |
| Thue-Morse | t_11 | 2048 | `256/77` | 4 | 4 | 4 | 4 (bracket closed) | CLOSED | 0 |
| Thue-Morse | t_12 | 4096 | `2560/769` | 4 | 4 | 4 | 4 (bracket closed) | CLOSED | 0 |
| Thue-Morse | t_13 | 8192 | `5120/1537` | 4 | 4 | 4 | 4 (bracket closed) | CLOSED | 0 |
| balanced periodic p/q | 1/3 n=42 | 42 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| balanced periodic p/q | 1/3 n=105 | 105 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| balanced periodic p/q | 1/3 n=210 | 210 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| balanced periodic p/q | 2/5 n=42 | 42 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| balanced periodic p/q | 2/5 n=105 | 105 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| balanced periodic p/q | 2/5 n=210 | 210 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| balanced periodic p/q | 3/7 n=42 | 42 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| balanced periodic p/q | 3/7 n=105 | 105 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| balanced periodic p/q | 3/7 n=210 | 210 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| de Bruijn sigma=2 | k=2 n=4 | 4 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| de Bruijn sigma=2 | k=3 n=8 | 8 | 2 | 2 | 3 | 3 | 3 (bracket closed) | CLOSED | 1 |
| de Bruijn sigma=2 | k=4 n=16 | 16 | `13/4` | 4 | 4 | 4 | 4 (bracket closed) | CLOSED | 0 |
| de Bruijn sigma=2 | k=5 n=32 | 32 | `28/5` | 6 | 7 | 7 | 7 (bracket closed) | CLOSED | 1 |
| de Bruijn sigma=2 | k=6 n=64 | 64 | `59/6` | 10 | 11 | 11 | 11 (bracket closed) | CLOSED | 1 |
| de Bruijn sigma=2 | k=7 n=128 | 128 | `122/7` | 18 | 19 | 19 | 19 (bracket closed) | CLOSED | 1 |
| de Bruijn sigma=2 | k=8 n=256 | 256 | `249/8` | 32 | 32 | 34 | not computed | open | [0, 2] |
| de Bruijn sigma=3 | k=2 n=9 | 9 | 4 | 4 | 4 | 4 | 4 (complete DFS (n <= 14)) | CLOSED, fallback | 0 |
| de Bruijn sigma=4 | k=2 n=16 | 16 | `15/2` | 8 | 8 | 8 | 8 (bracket closed) | CLOSED | 0 |
| random sigma=2 | n=16 s=11 | 16 | `9/4` | 3 | 3 | 3 | 3 (bracket closed) | CLOSED | 0 |
| random sigma=2 | n=16 s=12 | 16 | `8/3` | 3 | 4 | 4 | 4 (bracket closed) | CLOSED | 1 |
| random sigma=2 | n=16 s=13 | 16 | `8/3` | 3 | 4 | 4 | 4 (bracket closed) | CLOSED | 1 |
| random sigma=2 | n=32 s=11 | 32 | `11/3` | 4 | 5 | 5 | 5 (bracket closed) | CLOSED | 1 |
| random sigma=2 | n=32 s=12 | 32 | `23/6` | 4 | 6 | 6 | 6 (bracket closed) | CLOSED | 2 |
| random sigma=2 | n=32 s=13 | 32 | `23/6` | 4 | 6 | 6 | 6 (bracket closed) | CLOSED | 2 |
| random sigma=2 | n=64 s=11 | 64 | `50/7` | 8 | 9 | 9 | 9 (bracket closed) | CLOSED | 1 |
| random sigma=2 | n=64 s=12 | 64 | `53/7` | 8 | 9 | 9 | 9 (bracket closed) | CLOSED | 1 |
| random sigma=2 | n=64 s=13 | 64 | `52/7` | 8 | 9 | 9 | 9 (bracket closed) | CLOSED | 1 |
| random sigma=2 | n=128 s=11 | 128 | `99/8` | 13 | 15 | 15 | 15 (bracket closed) | CLOSED | 2 |
| random sigma=2 | n=128 s=12 | 128 | `109/8` | 14 | 16 | 16 | 16 (bracket closed) | CLOSED | 2 |
| random sigma=2 | n=128 s=13 | 128 | `25/2` | 13 | 16 | 16 | 16 (bracket closed) | CLOSED | 3 |
| random sigma=2 | n=256 s=11 | 256 | `113/5` | 23 | 28 | 29 | not computed | open | [5, 6] |
| random sigma=2 | n=512 s=11 | 512 | `453/11` | 42 | 50 | 52 | not computed | open | [8, 10] |
| random sigma=2 | n=1024 s=11 | 1024 | `917/12` | 77 | 91 | 97 | not computed | open | [14, 20] |
| random sigma=4 | n=16 s=11 | 16 | `9/2` | 5 | 6 | 6 | 6 (bracket closed) | CLOSED | 1 |
| random sigma=4 | n=16 s=12 | 16 | `9/2` | 5 | 5 | 5 | 5 (bracket closed) | CLOSED | 0 |
| random sigma=4 | n=32 s=11 | 32 | `25/3` | 9 | 10 | 10 | 10 (bracket closed) | CLOSED | 1 |
| random sigma=4 | n=32 s=12 | 32 | `23/3` | 8 | 10 | 10 | 10 (bracket closed) | CLOSED | 2 |
| random sigma=4 | n=64 s=11 | 64 | 14 | 14 | 16 | 17 | not computed | open, fallback | [2, 3] |
| random sigma=4 | n=64 s=12 | 64 | 14 | 14 | 18 | 18 | 18 (bracket closed) | CLOSED | 4 |
| random sigma=4 | n=128 s=11 | 128 | `97/4` | 25 | 28 | 29 | not computed | open | [3, 4] |
| random sigma=4 | n=128 s=12 | 128 | 25 | 25 | 31 | 31 | 31 (bracket closed) | CLOSED | 6 |
| random sigma=4 | n=256 s=11 | 256 | `219/5` | 44 | 52 | 53 | not computed | open | [8, 9] |
| random sigma=4 | n=512 s=11 | 512 | 80 | 80 | 94 | 99 | not computed | open | [14, 19] |
| run-length (a^L b^L)^m | L=2 m=16 n=64 | 64 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| run-length (a^L b^L)^m | L=2 m=32 n=128 | 128 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| run-length (a^L b^L)^m | L=2 m=64 n=256 | 256 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| run-length (a^L b^L)^m | L=4 m=16 n=128 | 128 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| run-length (a^L b^L)^m | L=4 m=32 n=256 | 256 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| run-length (a^L b^L)^m | L=4 m=64 n=512 | 512 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| run-length (a^L b^L)^m | L=8 m=16 n=256 | 256 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| run-length (a^L b^L)^m | L=8 m=32 n=512 | 512 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| run-length (a^L b^L)^m | L=8 m=64 n=1024 | 1024 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| run-length (a^L b^L)^m | L=16 m=16 n=512 | 512 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| run-length (a^L b^L)^m | L=16 m=32 n=1024 | 1024 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| run-length (a^L b^L)^m | L=16 m=64 n=2048 | 2048 | 2 | 2 | 2 | 2 | 2 (bracket closed) | CLOSED | 0 |
| square S S | m=8 s=1 n=16 | 16 | 2 | 2 | 3 | 3 | 3 (bracket closed) | CLOSED | 1 |
| square S S | m=8 s=2 n=16 | 16 | `7/3` | 3 | 3 | 3 | 3 (bracket closed) | CLOSED | 0 |
| square S S | m=16 s=1 n=32 | 32 | `11/4` | 3 | 3 | 3 | 3 (bracket closed) | CLOSED | 0 |
| square S S | m=16 s=2 n=32 | 32 | `13/5` | 3 | 3 | 3 | 3 (bracket closed) | CLOSED | 0 |
| square S S | m=32 s=1 n=64 | 64 | `24/5` | 5 | 5 | 5 | 5 (bracket closed) | CLOSED | 0 |
| square S S | m=32 s=2 n=64 | 64 | `9/2` | 5 | 6 | 6 | 6 (bracket closed) | CLOSED | 1 |
| square S S | m=64 s=1 n=128 | 128 | `58/7` | 9 | 9 | 10 | not computed | open | [0, 1] |
| square S S | m=64 s=2 n=128 | 128 | `57/7` | 9 | 9 | 9 | 9 (bracket closed) | CLOSED | 0 |
| square S S | m=128 s=1 n=256 | 256 | `53/4` | 14 | 16 | 16 | 16 (bracket closed) | CLOSED | 2 |
| square S S | m=128 s=2 n=256 | 256 | `106/9` | 12 | 15 | 15 | 15 (bracket closed) | CLOSED | 3 |
| square S S | m=256 s=1 n=512 | 512 | `45/2` | 23 | 24 | 28 | not computed | open | [1, 5] |
| square S S | m=256 s=2 n=512 | 512 | `227/10` | 23 | 23 | 27 | not computed | open | [0, 4] |
| reverse square S S^R | m=8 s=1 n=16 | 16 | 2 | 2 | 3 | 3 | 3 (bracket closed) | CLOSED | 1 |
| reverse square S S^R | m=8 s=2 n=16 | 16 | `5/2` | 3 | 3 | 3 | 3 (bracket closed) | CLOSED | 0 |
| reverse square S S^R | m=16 s=1 n=32 | 32 | `19/5` | 4 | 4 | 4 | 4 (bracket closed) | CLOSED | 0 |
| reverse square S S^R | m=16 s=2 n=32 | 32 | `11/3` | 4 | 5 | 5 | 5 (bracket closed) | CLOSED | 1 |
| reverse square S S^R | m=32 s=1 n=64 | 64 | `41/6` | 7 | 8 | 8 | 8 (bracket closed) | CLOSED | 1 |
| reverse square S S^R | m=32 s=2 n=64 | 64 | `37/6` | 7 | 8 | 8 | 8 (bracket closed) | CLOSED | 1 |
| reverse square S S^R | m=64 s=1 n=128 | 128 | `95/8` | 12 | 15 | 16 | not computed | open | [3, 4] |
| reverse square S S^R | m=64 s=2 n=128 | 128 | `101/9` | 12 | 13 | 13 | 13 (bracket closed) | CLOSED | 1 |
| reverse square S S^R | m=128 s=1 n=256 | 256 | 21 | 21 | 27 | 28 | not computed | open | [6, 7] |
| reverse square S S^R | m=128 s=2 n=256 | 256 | `191/10` | 20 | 23 | 25 | not computed | open | [3, 5] |
| reverse square S S^R | m=256 s=1 n=512 | 512 | `430/11` | 40 | 49 | 50 | not computed | open | [9, 10] |
| reverse square S S^R | m=256 s=2 n=512 | 512 | `406/11` | 37 | 44 | 47 | not computed | open | [7, 10] |

## 4. Question 1 — where `γ = ⌈δ⌉`, and where the gap lives

Reading block 1 with block 2 (all counts MY-COMPUTATION):

* **The five "δ ≤ 2" families are unanimous: 47 of 47 rows have `γ = ⌈δ⌉`, and in fact
  `γ = δ` exactly.**  `a^n` (`δ = 1`, `γ = 1`, 5 rows); `(ab)^m` (`δ = γ = 2`, 7 rows);
  Fibonacci/Sturmian (`δ = γ = 2`, 14 rows up to `F_20`, `n = 6765`); balanced periodic
  `p/q` (`δ = γ = 2`, 9 rows); run-length `(a^L b^L)^m` (`δ = γ = 2` for every `L ∈ {2,4,8,16}`
  up to `n = 2048`, 12 rows).  The last one is worth a second look: long runs do *not*
  break the bound; `δ` is still attained with two positions.
* **Thue–Morse is the cleanest failure-then-repair.**  `γ = 4` at every size from `n = 16` on
  (`n = 16 … 8192`) and `γ = 3` at `n = 8`, while `δ_t` climbs: `5/2` at `n=16`, `20/7 ≈ 2.857` at 32, `40/13` at 64,
  `16/5` at 128, `160/49` at 256, `320/97` at 512, `640/193` at 1024, `256/77` at 2048,
  `2560/769` at 4096, `5120/1537` at 8192.  So `⌈δ⌉ = 3` for `n = 16, 32` (gap 1) and
  `⌈δ⌉ = 4` from `n = 64` on (gap 0): **the cross-over is exactly `δ` passing 3.**
  The three failing rows are `n = 8, 16, 32`.
* **de Bruijn words are `⌈δ⌉ + 1` in 4 of the 6 decided orders.**  `γ = ⌈δ⌉+1` at
  `k = 3, 5, 6, 7` (e.g. `k = 7`, `n = 128`: `δ = 122/7 ≈ 17.43`, `⌈δ⌉ = 18`, `γ = 19`);
  `γ = ⌈δ⌉` at `k = 2, 4`; `k = 8` (`n = 256`) is **undecided** (`[32, 34]` on `δ = 249/8`).
  The alternation is not a parity or a size effect that *I* can explain (lane C's note offers no
  mechanism either), and I do not conjecture a formula (§7).
* **Random text: `γ > ⌈δ⌉` almost always.**  Over `σ = 2`: 11 of the 12 rows with exact `γ`
  have gap ≥ 1, only `n = 16, s = 11` is tight (`δ = 9/4`, `γ = 3`).  Over `σ = 4`: 5 of 6.
  The largest *closed* gap in the whole sweep is `random σ=4, n = 128, s = 12`:
  `δ = 25` exactly, `γ = 31`, gap 6.
* **One repeated half: reversal multiplies the gap.**  For 9 of the 12 `S S` rows and 7 of
  the 12 `S S^R` rows `γ` is exact; `S S` is tight in 5 of those 9, `S S^R` in 2 of 7.  At
  `m = 256`, `n = 512`, the *same* `S` gives `S S`: `δ = 45/2`, `γ ∈ [24, 28]` (gap ≤ 5) and
  `S S^R`: `δ = 430/11 ≈ 39.09`, `γ ∈ [49, 50]` (gap ≥ 9).  Reversal is not a neutral
  perturbation: `δ` and the gap both grow.
* **Cross-checks against lane C's independent computation.**  `docs/research/gamma-equals-delta.md`
  §3.3 built *different* de Bruijn words (the lexicographically smallest ones) and reports
  `(δ, γ) = (2, 3)` for order 3 and `(28/5, 7)` for order 5, plus `(2, 3)` for TM `2³`: all three
  agree with rows in block 2.  Its `γ/δ ≈ 1.18–1.30` on random text at `n = 256 … 2048` is the
  same band as this table's ratios.  Nothing in the two notes contradicts the other.
* **Nothing ever came out below `⌈δ⌉`**, in 117 rows — as KNP23 requires.  `check.py`
  asserts `gap_lo ≥ 0` on every row, so a machinery bug that under-reported `lb` would fail
  there rather than silently violate the theorem.

## 5. Question 2 — how the gap scales with `n` (empirical, not a theorem)

### 5.1 Block 3 — the gap on every row where it is nonzero

| family | n | delta | ceil(delta) | gap range | gap / delta |
| --- | --- | --- | --- | --- | --- |
| Thue-Morse | 8 | 2 | 2 | [1, 1] | 0.50 |
| Thue-Morse | 16 | `5/2` | 3 | [1, 1] | 0.40 |
| Thue-Morse | 32 | `20/7` | 3 | [1, 1] | 0.35 |
| de Bruijn sigma=2 | 8 | 2 | 2 | [1, 1] | 0.50 |
| de Bruijn sigma=2 | 32 | `28/5` | 6 | [1, 1] | 0.18 |
| de Bruijn sigma=2 | 64 | `59/6` | 10 | [1, 1] | 0.10 |
| de Bruijn sigma=2 | 128 | `122/7` | 18 | [1, 1] | 0.06 |
| de Bruijn sigma=2 | 256 | `249/8` | 32 | [0, 2] | 0.00 |
| random sigma=2 | 16 | `8/3` | 3 | [1, 1] | 0.38 |
| random sigma=2 | 16 | `8/3` | 3 | [1, 1] | 0.38 |
| random sigma=2 | 32 | `11/3` | 4 | [1, 1] | 0.27 |
| random sigma=2 | 32 | `23/6` | 4 | [2, 2] | 0.52 |
| random sigma=2 | 32 | `23/6` | 4 | [2, 2] | 0.52 |
| random sigma=2 | 64 | `50/7` | 8 | [1, 1] | 0.14 |
| random sigma=2 | 64 | `53/7` | 8 | [1, 1] | 0.13 |
| random sigma=2 | 64 | `52/7` | 8 | [1, 1] | 0.13 |
| random sigma=2 | 128 | `99/8` | 13 | [2, 2] | 0.16 |
| random sigma=2 | 128 | `109/8` | 14 | [2, 2] | 0.15 |
| random sigma=2 | 128 | `25/2` | 13 | [3, 3] | 0.24 |
| random sigma=2 | 256 | `113/5` | 23 | [5, 6] | 0.22 |
| random sigma=2 | 512 | `453/11` | 42 | [8, 10] | 0.19 |
| random sigma=2 | 1024 | `917/12` | 77 | [14, 20] | 0.18 |
| random sigma=4 | 16 | `9/2` | 5 | [1, 1] | 0.22 |
| random sigma=4 | 32 | `25/3` | 9 | [1, 1] | 0.12 |
| random sigma=4 | 32 | `23/3` | 8 | [2, 2] | 0.26 |
| random sigma=4 | 64 | 14 | 14 | [2, 3] | 0.14 |
| random sigma=4 | 64 | 14 | 14 | [4, 4] | 0.29 |
| random sigma=4 | 128 | `97/4` | 25 | [3, 4] | 0.12 |
| random sigma=4 | 128 | 25 | 25 | [6, 6] | 0.24 |
| random sigma=4 | 256 | `219/5` | 44 | [8, 9] | 0.18 |
| random sigma=4 | 512 | 80 | 80 | [14, 19] | 0.17 |
| reverse square S S^R | 16 | 2 | 2 | [1, 1] | 0.50 |
| reverse square S S^R | 32 | `11/3` | 4 | [1, 1] | 0.27 |
| reverse square S S^R | 64 | `41/6` | 7 | [1, 1] | 0.15 |
| reverse square S S^R | 64 | `37/6` | 7 | [1, 1] | 0.16 |
| reverse square S S^R | 128 | `95/8` | 12 | [3, 4] | 0.25 |
| reverse square S S^R | 128 | `101/9` | 12 | [1, 1] | 0.09 |
| reverse square S S^R | 256 | 21 | 21 | [6, 7] | 0.29 |
| reverse square S S^R | 256 | `191/10` | 20 | [3, 5] | 0.16 |
| reverse square S S^R | 512 | `430/11` | 40 | [9, 10] | 0.23 |
| reverse square S S^R | 512 | `406/11` | 37 | [7, 10] | 0.19 |
| square S S | 16 | 2 | 2 | [1, 1] | 0.50 |
| square S S | 64 | `9/2` | 5 | [1, 1] | 0.22 |
| square S S | 128 | `58/7` | 9 | [0, 1] | 0.00 |
| square S S | 256 | `53/4` | 14 | [2, 2] | 0.15 |
| square S S | 256 | `106/9` | 12 | [3, 3] | 0.25 |
| square S S | 512 | `45/2` | 23 | [1, 5] | 0.04 |
| square S S | 512 | `227/10` | 23 | [0, 4] | 0.00 |

(`gap / δ` uses the certified lower end of the gap, so it is a lower bound on the true
ratio; `δ` as a fraction in the same row.)

### 5.2 Block 4 — the growth, against the named shapes

| family | n range | gap at n_min | gap at n_max | gap grew by | log-log exponent | constant | log2 n | sqrt n | n | delta | closest shape | n values |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Thue-Morse | 8..32 | 1 | 1 | x1.00 | 0.00 | x1.00 * | x1.67 | x2.00 | x4.00 | x1.43 | constant | 8, 16, 32 |
| de Bruijn sigma=2 | 8..128 | 1 | 1 | x1.00 | 0.00 | x1.00 * | x2.33 | x4.00 | x16.00 | x8.71 | constant | 8, 32, 64, 128 |
| random sigma=2 | 32..1024 | 1 | 14 | x14.00 | 0.76 | x1.00 | x2.00 | x5.66 | x32.00 | x20.84 * | delta | 32, 64, 128, 256, 512, 1024 |
| random sigma=4 | 32..512 | 1 | 14 | x14.00 | 0.95 | x1.00 | x1.80 | x4.00 | x16.00 * | x10.43 | n | 32, 64, 128, 256, 512 |
| reverse square S S^R | 64..512 | 1 | 7 | x7.00 | 0.94 | x1.00 | x1.50 | x2.83 | x8.00 | x6.34 * | delta | 64, 128, 256, 512 |

`delta` in that table is the factor by which `δ` itself grows over the same `n` range; the
shape closest to the observed factor (in log space) is starred.  The series there is the
**minimum** `gap_lo` over the seeds computed at each `n`, i.e. a statement that is true of
at least one text in the family at each `n`; the seed-to-seed spread is the difference
between the `[lo, hi]` intervals in block 3.

What that says, plainly (MY-INFERENCE from the two blocks — an empirical trend, **not** a
theorem):

1. **Constant at 1 where `γ` is an integer that stops moving while `δ` keeps growing.**
   Thue–Morse over `n = 8 … 32` and de Bruijn over `n = 8 … 128`: `gap` grows by ×1.00 while
   `n` grows ×4 and ×16 and while `δ` grows ×1.43 and ×8.71.  So on de Bruijn words the gap is
   *not* proportional to `δ` — it is one extra position.  A "gap ≈ c·δ" law is false there.
2. **Growing, at about `δ`'s rate, on random text and on `S S^R`.**  Random `σ = 2`,
   `n = 32 … 1024`: gap ×14, log–log exponent 0.76, against `sqrt n`'s ×5.66, `log₂ n`'s
   ×2.00, `n`'s ×32 and `δ`'s ×20.84 — closest to `δ`.  Random `σ = 4`, `n = 32 … 512`: ×14,
   exponent 0.95, against `n`'s ×16 and `δ`'s ×10.43 — between the two, closer to `n`
   (the gap there runs from 1 to 14 over a 16× range of `n`, which is closer to linear than
   to anything else in the list).  `S S^R`, `n = 64 … 512`: ×7, exponent 0.94, against `δ`'s
   ×6.34 (closest) and `sqrt n`'s ×2.83.
3. **Zero** in the 47 rows of §4's first bullet.

So the answer to *"is it constant, `sqrt n`, or `log n`?"* is: **on the families with a large
gap it is none of those three — it grows faster than `sqrt n` and no faster than `n`**, and the
multiplicative view fits better than any power of `n`: `gap/δ` has no visible trend in `n` on
those rows (0.12–0.52 on every random row here, 0.09–0.50 on `S S^R`, column 6 of block 3),
while `δ` itself on random text is `Θ(n/log n)` (MY-INFERENCE: all factors of length
`≤ (2−ε)log_σ n` are distinct w.h.p. — the standard random-string factor count).  Reading
`gap ≈ c·δ` with `c ∈ [0.1, 0.5]` then predicts a gap of order `n/log n`, i.e. an exponent
just below 1, which is what the three growing families show (0.76, 0.95, 0.94).  A gap of
order `n/log n` is a statement about `γ` that `δ ≤ γ` cannot see at all.

**The benchmark these numbers should be read against.**  The worst case is *proved*: KNP23
Thm III.3 + Lemma III.2 give a family with `δ ≤ 2` and `γ ≥ ½⌊log n⌋`, hence `gap = Θ(log n)`
(§1.1).  A single scale-free way to say where each family sits is therefore `gap/δ`, compared
with the proved worst case's `log(n/δ)`:

| regime | `gap` | `gap/δ` | families here |
| --- | --- | --- | --- |
| attained | 0 | 0 | unary, `(ab)^m`, Fibonacci/Sturmian, balanced `p/q`, run-length (47 rows) |
| constant | 1 | falls as `1/δ` | Thue–Morse (`n = 8 … 32`), de Bruijn (`n = 8 … 128`) |
| `≈ c·δ`, no log factor | grows | `0.04 … 0.52`, no trend in `n` | random `σ=2`, random `σ=4`, `S S^R`, `S S` |
| proved worst case | `Θ(δ log(n/δ))` | `log(n/δ)` | *not in this table* (KNP23's sparse-`b` strings) |

(MY-INFERENCE from blocks 1–4; both ends of the band are the generated "largest gap/delta"
and "smallest gap/delta" lines in §11, not hand arithmetic.)  Read this way the three measured regimes and the theorem are consistent: on
Thue–Morse `δ` is bounded (`δ < 10/3`), so "gap proportional to δ" predicts a *constant*, and a
constant is what is measured; on random text `δ ≈ n/log n`, so "gap proportional to δ" predicts
order `n/log n`, which is what the exponents 0.76–0.95 show.  What no family here does is pay
the extra `log(n/δ)` that the worst case guarantees somewhere — which is exactly why the
"`gap/δ ≤ 0.52`" figure must **not** be read as a bound (see §8).

Caveat with teeth: only five families have two or more `n` values with a certified nonzero
gap, three of them have just two seeds per size, and the two `σ = 4` and `σ = 2` series differ
in their best-fit shape (×14 either way, over different `n` ranges).  These are trends in a
117-row table, not asymptotics.

## 6. Question 3 — the most surprising row, and the row that refutes (N)

**The single most surprising row is `de Bruijn σ=2, k = 7` (`n = 128`): `δ = 122/7 ≈ 17.43`,
`⌈δ⌉ = 18`, `γ = 19`, bracket CLOSED, gap 1.**  The surprise is not the row by itself but the
comparison it forces at fixed `n`: the random binary text of the same length (`n = 128,
s = 11`) has `δ = 99/8 = 12.375`, `⌈δ⌉ = 13`, `γ = 15`, gap 2 (also closed).  The de Bruijn
word is the *less* repetitive of the two by `δ` (17.43 > 12.375 — it contains every 7-gram
exactly once, the extreme of non-repetitiveness) and yet its gap is *smaller* and its `δ`
bound is nearly attained (`γ/⌈δ⌉ = 19/18 ≈ 1.056` against `15/13 ≈ 1.15`).  Conclusion
(MY-INFERENCE): the gap is **not a monotone function of `δ`**, so no conjecture of the form
"the gap grows with `δ`" or "the gap grows with incompressibility" can be right; whatever
forces the gap is a property of the *positions* (the packing structure), not of the factor
count.  This is exactly the regime where `δ` is the wrong certificate: on de Bruijn words the
packing bound certifies `γ ≥ 19`, i.e. 1 above `⌈δ⌉`.

**The row that most clearly refutes (N) for repetitive strings is `Thue–Morse t_5`
(`n = 32`): `δ = 20/7 ≈ 2.857`, `⌈δ⌉ = 3`, `γ = 4`, gap 1, bracket CLOSED.**  It is a morphic
word whose `δ` is small in absolute terms and tiny relative to `n` (`δ/n ≈ 0.09`), the bracket
is closed so `γ = 4` is not an artefact of the search's upper bound, and `4 > ⌈20/7⌉ = 3`.

Three things make the row hard to dismiss:

1. **The upper end is not mine to doubt.**  KTMSIT20 prove `γ = 4` for Thue–Morse at every
   `n ≥ 4` (Thm 3) and give the closed form `δ(t_n) = 10/(3+2^{4−n})` (Thm 4), which is `20/7`
   at `n = 32` and `5/2` at `n = 16` — so the gap of 1 at those two lengths is a theorem about
   that family plus an exact `δ`, and this table supplies the matching certified bracket.
2. **The lower end is not `δ` in disguise.**  `lb = 4` does not come from `⌈δ⌉` (3), and not
   from the packing bound (3): it comes from the completed DFS that proved **no attractor of
   size 3 exists** (`lb_source = "exact tail"` in `results.json`).  The row therefore survives
   any objection of the form "your lower bound is the `δ` bound in disguise".
3. **The sharper variant needs no rounding slack at all.**  At `n = 8`, `t_3` has `δ = 2`
   *exactly*, so `⌈δ⌉ = δ = 2` while `γ = 3` — again with `lb = 3` from a completed DFS, since
   both `⌈δ⌉` and the packing bound are 2 there.

Two qualifications, because the word "repetitive" is doing work:

* If "repetitive" means **periodic**, (N) is *not* refuted here: all 47 rows of the five
  `δ ≤ 2` families have `γ = δ = ⌈δ⌉`, up to `n = 6765` (Fibonacci) and `n = 2048`
  (run-length).  (N) survives on every fully periodic text measured.
* If "repetitive" means **"has a long repeated half"**, the refutation is much larger than
  Thue–Morse's: `S S^R` at `n = 512` (`m = 256`, `s = 1`) has `δ = 430/11 ≈ 39.09`,
  `⌈δ⌉ = 40`, `γ ∈ [49, 50]`, so **gap ≥ 9 and ≤ 10** — the floor certified by a packing family
  of 49 disjoint factors, no search guess involved.  For scale, the *same* `S` as `S S` has
  `δ = 45/2 = 22.5` and `γ ∈ [24, 28]`, i.e. a certified gap floor of 1: reversing the second
  half raises the floor from 1 to 9 while raising `δ` by `430/11 − 45/2 ≈ 16.6`.

So (N) as stated — "for repetitive strings" — has no truth value until "repetitive" is
defined; what this note establishes is which *families* obey it (periodic, Sturmian,
run-length, unary) and which do not (Thue–Morse at small `n`, de Bruijn, one repeated half,
random), with closed brackets behind each.

## 7. Falsifiable statements, and what would settle the open ones

**Conjectures this table supports** (each is refutable by one closed bracket that disagrees):

1. `γ(F_k) = 2` for every Fibonacci word, i.e. `γ = δ` on Sturmian words.  Held for
   `k = 7 … 20`; refuted by any Sturmian word with `γ ≥ 3` (a closed bracket, or a proof that
   two positions cannot cover).
2. `γ(t_k) = 4` for every `k ≥ 4` (Thue–Morse prefixes).  Held for `k = 4 … 13`, i.e.
   `n = 16 … 8192`.
3. `γ(a^n) = γ((ab)^m) = γ((a^L b^L)^m) = γ(balanced p/q)` `= 2` for all sizes.  Held on all
   33 rows of those four families; the mechanism is the same in each (`δ = 2` plus two
   positions that cross everything).
4. `γ > ⌈δ⌉` on a random text of length `n ≥ 32` with probability → 1, with `gap/δ` inside
   `[0.1, 0.55]`.  Held in 11 of the 12 exact `σ = 2` rows (the exception is `n = 16,
   s = 11`) and in 5 of 6 exact `σ = 4` rows, and every `[lo, hi]` interval with `n ≥ 256`
   excludes 0.

**Open, and stated so they can be attacked:**

* **de Bruijn parity.** Is `gap(de Bruijn_2(k))` always 0 or 1?  `k = 8` (`n = 256`) is
  undecided (`[32, 34]`); closing it settles whether the `⌈δ⌉+1` pattern is a small-`k`
  artefact.  What would settle it: a closed bracket at `k = 8`, or a proof that
  `γ ≥ ⌈δ⌉ + 1` on de Bruijn words for `k ≡ 3 mod 2`-style conditions — and I have no
  candidate argument.
* **KNP23's sparse-`b` family, which is missing here.** `S_∞[i] = b ⟺ i = 2^j` has `δ ≤ 2` and
  `γ = Θ(log n)` (§1.1), so `gap = Θ(log n)` with `⌈δ⌉` a constant — the one family where the
  gap's growth rate is *known*.  It is cheap to add (`build_text` takes a spec; the family is
  three lines), and it would put the proved worst case next to the measured families in the same
  table.  What would settle the empirical part of §5: that row plus `S S^R` at `m = 1024, 2048`.
* **The growth rate on `S S^R` and random.** The measurement can only be pushed with a
  better lower bound or a much bigger budget (one row at `n = 4096` costs a minute of this
  Python and still leaves an interval).  A proof that `γ − ⌈δ⌉` is unbounded on `S S^R` would
  answer "yes" to §5's question sharply; nothing in this table decides between unbounded and
  bounded-below-only.
* **The Thue–Morse `δ` closed form — corroborated, not read.**  KTMSIT20 Thm 4 gives
  `δ(t_n) = 10/(3 + 2^{4−n})` (quoted in lane C's note §2; **I did not open the paper**).
  Evaluated at `n = 8 … 8192` it reproduces this table's exact rational `δ` **in all 11 cases**
  (`2, 5/2, 20/7, 40/13, 16/5, 160/49, 320/97, 640/193, 256/77, 2560/769, 5120/1537`), which is
  why the `10/3` limit is quoted here at all: an independently derived closed form agreeing with
  11 exact computations is stronger evidence than either alone.  It fails only at `n = 4`
  (formula `10/7`, truth `2` — the formula is stated for `n ≥ 6`).  What would still settle the
  `10/3` constant at the source: read Thm 4's statement in KTMSIT20 (arXiv:2005.09524).  Note
  this does not affect any `γ` claim: `γ = 4` at every `n ≥ 16` is certified independently of
  `δ`'s limit.

## 8. Reproducing, and what is and is not checked

```sh
cd tools/attractor/experiments
sh run.sh                 # sweep (~2 min) + check (~0.5 min); exits non-zero on failure
sh run.sh --no-doc        # same, but tolerates a note that has drifted (see below)
python3 run_families.py --only "thue,square" --base-budget 3   # a slice, for a smoke test
python3 check.py --quick  # skip the DFS re-proofs of lb
```

`run.sh` runs both stages under `timeout`, and `run_families.py` under
`faulthandler.dump_traceback_later`, so neither can hang.  Outputs land in this directory:
`results.json` (every row plus its certificates), `table.md`, `verdicts.md`, `trends.md`,
`rates.md`, `summary.md`.  The blocks in this note are those files **verbatim**.

`check.py` re-derives, for every row, from the text alone (it never trusts `results.json`):

| check | what it pins down |
| --- | --- |
| families | each text really is what its label says: unary, `abab…`, Fibonacci `d_k = k+1` on `k ≤ n/3` with `d_k ≤ 2k` everywhere (so `δ = 2`), the Thue–Morse morphism, de Bruijn (every cyclic `k`-gram exactly once, length `σ^k`), `q`-periodic mechanical words with `p` ones per period, `a^L b^L` runs, `S S` and `S S^R` halves |
| `δ` | recomputed and compared as an exact `Fraction` |
| `ub` | `Instance.verify` on the recorded positions, `|Γ| = ub`, positions distinct and in range |
| `lb` | re-derived as the max of `⌈δ⌉`, a freshly built packing family, the recorded packing family re-certified, and — when the row's `lb` exceeds both — a fresh DFS at `k = lb − 1` that must report *infeasible*; then `lb ≤ ub` and `lb ≥ ⌈δ⌉` |
| gap fields | `gap_lo = lb − ⌈δ⌉`, `gap_hi = ub − ⌈δ⌉`, `gap_lo ≥ 0` |
| exactness | a closed row has `lb = ub`; a "complete DFS" row is under the `n ≤ 14` limit; every `n ≤ 14` row gets a *fresh* complete DFS whose size must equal `ub` |
| the note | blocks 1–4 appear verbatim in `docs/research/gamma-delta-table.md`, every row label appears in it, and the 25 rows quoted in §4–§6 still have the quoted `δ`, `⌈δ⌉`, `lb`, `γ` |

That is 2 700+ assertions in about 30 s.  (This file is not yet listed in
`docs/research/README.md`'s status table: that index is edited by the integrator, and this
lane does not write outside `tools/attractor/experiments/` and this file.)  `--allow-doc-drift` exists because `ub` on an
*open* row is time-budgeted: on a slower machine the search may stop one position higher, the
regenerated `table.md` then differs from the committed note, and the right response is to
regenerate the note from the new `results.json` rather than to loosen the check.

**Not claimed:**

* No `γ` is claimed optimal on a row whose bracket is open (16 rows).  Those rows contribute
  a gap *interval*, and the lower end is the only part used for any trend.
* `δ`, `lb` and `ub` here are bounds, not theorems about a family: "`γ = 2` for Fibonacci
  words" is asserted for the 14 sizes computed, not for all `k` (§7 states it as a conjecture).
* No statistical claim: 117 texts, 2–3 seeds per size, one alphabet pair.  Families were
  chosen, not sampled.
* **No family here realizes the proved `Θ(log n)` worst case.**  The largest `gap/δ` in this
  table is 0.52 (§11) and it does not grow with `n`; KNP23's sparse-`b` family, where `δ ≤ 2`
  and `γ = Θ(log n)`, is not in the table.  So nothing here bounds `γ/δ` in general, and the
  observed "gap ≈ c·δ, c ≤ 0.52" is a statement about these 117 texts only.  Adding KNP23's
  family to this sweep is the obvious next measurement (§7).
* The packing bound is a heuristic *search* for a family whose *certificate* is then checked:
  a stronger lower bound may exist, so every `gap ≥` statement here is a floor that a better
  tool can only raise, and every `gap ≤` statement is a ceiling that a better upper bound can
  only lower.
* `γ` for `n ≤ 14` uses the tool's complete DFS, cross-checked against a second complete DFS
  in `check.py` — but both are the same `decision` procedure, so a *logic* error in it would
  be invisible here.  The mitigation is that the DFS's output is still checked by
  `Instance.verify`, which shares nothing with the DFS.

## 9. The tool bug these measurements had to route around

`anytime.search` **crashes** on some texts:

```
$ python3 tools/attractor/anytime.py --gen thue-morse:3 --budget 2
RuntimeError: greedy stalled with 1 uncovered nodes
```

The same happens for the ternary de Bruijn word of order 2 (`n = 9`) and random 4-ary
`n = 64, s = 11`.  The cause is in the GRASP restart phase of `search`:
`greedy(inst, rng=rng, top=3)` insists on collecting exactly `top = 3` picks, and when fewer
than 3 positions still have positive gain it pops the heap empty and raises
(`tools/attractor/anytime.py`, the `while len(picks) < top` loop) instead of returning the
picks it has.  A text with a distinct factor crossed by only one or two positions in the
endgame triggers it — which includes the tool's own documented `--gen thue-morse:3` example.

`tools/attractor` is outside this directory's ownership, so the bug is **reported, not
fixed**.  Three rows of this sweep hit it (`t_3`, de Bruijn `σ=3 k=2`, `random σ=4 n=64 s=11`);
those rows carry `path = "primitives-fallback"` in `results.json` and `CLOSED, fallback` (or
`open, fallback`) in block 2, and their bracket was computed by re-scheduling the *same*
primitives (`anytime.greedy`, `anytime.prune`, `anytime.local_search`,
`anytime.decision`) without the restart phase.  Their endpoints are verified exactly as
strictly as any other row's.  A one-line fix in `anytime.py` (return `picks` when the heap
empties, and skip the round if it is empty) would let `search` cover these texts itself.

## 10. Sources

* **KNP23** — T. Kociumaka, G. Navarro, N. Prezza, *Substring complexity in sublinear space*,
  IEEE Trans. Inf. Theory 2023, arXiv:1910.02151.  Lemma II.4: `δ ≤ γ` (PROVED; quoted in
  `docs/research/attractor-approx.md` §1.1; machine-checked here as
  `substringComplexity_le_card_attractor`).
* **KPRR18** — D. Kempa, A. Policriti, N. Prezza, M. Rotenberg, *String attractors:
  verification and optimization*, ESA 2018, LIPIcs 112, doi:10.4230/LIPIcs.ESA.2018.52,
  arXiv:1803.01695.  `γ` is NP-hard (Thm 8 per `docs/research/attractor-approx.md`).
* **KP18** — D. Kempa, N. Prezza, *At the roots of dictionary compression: string
  attractors*, STOC 2018, doi:10.1145/3188745.3188814, arXiv:1710.10964.  `γ ≤ g`, `γ ≤ z`.
* **MH40** — M. Morse, G. A. Hedlund, *Symbolic dynamics II: Sturmian trajectories*,
  Amer. J. Math. 62 (1940) 1–16.  Sturmian = aperiodic balanced, `p(k) = k+1`.
* **dB46** — N. G. de Bruijn, *A combinatorial problem*, Nederl. Akad. Wetensch. Proc. 49
  (1946) 758–764.  De Bruijn sequences of order `k` exist (every `k`-word appears once).
* **KTMSIT20** — K. Kutsukake, T. Matsumoto, Y. Nakashima, S. Inenaga, H. Bannai, M. Takeda,
  *On the size of overlap string attractors* (SPIRE 2020), doi:10.1007/978-3-030-59212-7_15,
  arXiv:2005.09524.  Thm 3 (`γ = 4` for Thue–Morse), Thm 4 (`δ(t_n) = 10/(3+2^{4−n})`).  Cited
  via `docs/research/gamma-equals-delta.md`; not read here (see §7).
* **MRRRS19** — S. Mantaci, A. Restivo, G. Rombo, G. Rosone, *A combinatorial view on string
  attractors* (ICTCS 2019), arXiv:1907.04660 (id as given in lane C's note, not checked here).
  Thm 5: `γ = 2` for every standard Sturmian word.
* **SS20** — L. Schaeffer, J. Shallit, arXiv:2012.06840 (id as in lane C's note).  Thm 5: the
  minimum attractor size of every Thue–Morse prefix — the statement that makes the refutation in
  §6 hold for all prefix lengths 25…59, not only the 2^k ones.
* **`docs/research/gamma-equals-delta.md`** — lane C's note, the source of the citations above
  and of the independent computations cross-checked in §4 and §7.

## 11. Generated summary of the sweep

```
rows listed: 117, computed: 117, not computed: 0
brackets CLOSED: 101 of 117
gamma known exactly (closed bracket or complete DFS): 101
among those: gamma == ceil(delta): 69, gamma > ceil(delta): 32
rows measured through the primitives fallback: 3 (['debruijn', 'random', 'thue-morse'])
largest gap/delta in this table: 0.52 at the certified lower ends (n=32 s=12), 0.52 at the upper ends (n=32 s=12)
smallest gap/delta among the rows with a proved positive gap: 0.04 (m=256 s=1 n=512)
```
