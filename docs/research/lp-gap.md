# The integrality gap of the attractor set-cover LP: measured, exactly

**Question B.** What is the integrality gap of the set-cover LP for the minimum attractor?
If it is `O(1)`, a constant-factor approximation is within reach; if it is `Theta(log n)`, the
log-factor bounds are essentially inherent for LP-based methods.  Nobody had measured it.

    gap(S) = gamma(S) / LP*(S)   >= 1

with `gamma` the minimum attractor and `LP*` the LP relaxation of the exact set-cover
formulation, **both computed exactly in rational arithmetic** (`fractions.Fraction`; no bound reported here
uses floating point — floats appear only in a parenthetical "≈" column for orientation and in
the trend fit of §3.1, which is a description and not a bound).  This note is the contract for `tools/gap/`; every number in it
is reproduced by `python3 gap.py` and re-checked by `python3 check.py`.

**Verdicts.** PROVED = read in a primary source or derived here with the derivation given;
OPEN = the sources say unknown; MY-INFERENCE = derived by me from cited facts; MY-COMPUTATION
= computed here (recipe and certificate given); UNVERIFIED = statement not confirmed in this
session, with what would settle it.

**Sources used.** **KP18** Kempa–Prezza, STOC 2018, doi:10.1145/3188745.3188814,
arXiv:1710.10964 (the set-cover formulation of attractors, §3).  **KPRR18** Kempa–Policriti–
Prezza–Rotenberg, ESA 2018, doi:10.4230/LIPIcs.ESA.2018.52, arXiv:1803.01695 (Lemma 11: the
universe may be taken to be the suffix-tree edges, `|U| <= 2n-2`; Thm 33: the
`H(k(k+1)/2)`-greedy).  **KNP23** Kociumaka–Navarro–Prezza, IEEE TIT 2023, arXiv:1910.02151
(`delta <= gamma`, substring complexity).  **Feige98** Feige, JACM 45(4):634–652, 1998,
doi:10.1145/285055.285059 (`ln n` threshold for set cover; the greedy `H_n` ratio is optimal
up to lower-order terms).  **Chvatal79** Chvátal, Math. Oper. Res. 4(3):233–235, 1979,
doi:10.1287/moor.4.3.233 (the greedy `H_d` bound).  **RT87** Raghavan–Tompson, Combinatorica
7:365–374, 1987, doi:10.1007/BF02579324 (randomized rounding: LP rounding gives `H_d`).
**Chvatal83** Chvátal, *Linear Programming*, Freeman 1983, ch. 5 (weak and strong duality,
shadow prices).  LP duality itself: Gale 1951 / Dantzig–von Neumann 1947 (equilibrium
theorem).

> Provenance note, in the spirit of `docs/research/README.md`: I did **not** open Feige98,
> Chvatal79, RT87 or Chvatal83 in this session.  They are quoted as the standard statements of
> facts every LP-based approximation paper uses (`H_d`-rounding, `Theta(log)` set-cover gap
> examples, weak/strong duality).  Their *precise numbering/wording is UNVERIFIED here*;
> opening the DOI settles it.  Nothing in the measurements below depends on them: the
> measurements use only weak duality, which `check.py` verifies concretely on the instances
> (a feasible primal and a feasible dual of equal value).

## 0. The answer, in one paragraph

Over **all** binary strings with `n <= 16` (131 070 texts), all ternary strings with `n <= 8`
(9840 texts), and 59 morphic/random texts up to `n = 987`, the measured gap is **at most
`15/11 = 1.3636`**, attained by exactly four binary texts at `n = 13`; 89.3 % of the binary and
92.3 % of the ternary instances are **exactly integral** (`gap = 1`), and on the Fibonacci words
the LP is exactly integral at every length measured (`gamma = LP* = 2` for `n` up to 987).
The per-length maximum over all binary strings is `1` (n <= 6), `6/5` (n = 7), `9/7`
(n = 8..11), `4/3` (n = 12), **`15/11` (n = 13)**, `4/3` (n = 14, 15, 16) — a bounded, slightly
wobbling plateau, not a `log` climb (`log2 16 = 4`).  **On this evidence the `O(1)`-gap hypothesis
survives and the `Theta(log n)` hypothesis is unsupported** — but `n <= 16` is far too small
to prove asymptotics, and no adversarial family with a growing gap was found.  So: *no
evidence of a growing gap; a `Theta(log n)` family, if it exists, is not among the natural
ones; a constant-factor LP-based approximation is not obviously blocked.*  The separate,
unresolved step is that even a `15/11`-gap LP needs a constructive `O(1)`-ratio rounding rule.

Three things the measurement **refutes**, two of them asserted or implied by the brief and one
of them my own pre-measurement inference:

1. *"The fixed-`k` instance has consecutive-ones structure, so its gap is 1."*  **False for
   `k >= 2`**: consecutive-ones needs *unique* occurrences.  Measured maxima over all binary
   `n <= 12`: `k = 1` gap `1` (and that one is PROVED below), `k = 2` gap `4/3`, `k = 3` gap
   `3/2`.  The single-`k` relaxations are strictly *weaker* than the full one.
2. *The conjecture "`gamma/LP* <= 4/3` for every binary string"* (the natural guess after the
   `n <= 12` scan, and the sharp form of C2 in `attractor-approx.md` restricted to `4/3`):
   **refuted at `n = 13`** by `0110101101110` (`gamma = 3`, `LP* = 11/5 = 2.2`, gap
   `15/11 = 1.3636`).  It survives only in the weaker form `<= 15/11`, for the lengths measured
   (`n <= 16` exhaustively, plus sampled/hill-climbed texts to `n = 64`).
3. *My own pre-measurement inference "`gap_full >= gap_k`"* — **false**.  Adding the longer
   factors adds constraints, which raises `LP*`, and can raise `gamma` not at all: the full
   instance of `111111101110` has gap `1` while its `k = 3` instance has gap `3/2`.  The
   difficulty is present **at a single fixed length**, and mixing lengths *reduces* the gap.

## 1. The instance, and the LP, exactly as specified

`S` is a text of length `n` over `[0, sigma)`, positions are `0..n-1`.  With
`f = S[i:i+L]` a nonempty factor,

    C(f)      = { p : some occurrence [i, i+L) of f has i <= p < i+L }
    set_p     = { f : p in C(f) },  U = all distinct nonempty factors
    Gamma is an attractor  <=>  union_{p in Gamma} set_p = U
    gamma     = min |Gamma|                      (the integer program)
    LP*       = min sum_p x_p  s.t.  sum_{p in C(f)} x_p >= 1  for all f in U,  x >= 0
    dual      = max sum_f y_f  s.t.  sum_{f : p in C(f)} y_f <= 1  for all p,  y >= 0

This is KP18 §3's formulation (PROVED-by-definition); `gamma` is its integer optimum.

**(1a) The universe can be reduced to suffix-tree nodes, for the LP as well as the integer
program (MY-INFERENCE from KPRR18 Lemma 11's decomposition; the integer part is
tools/attractor's R1, the LP part is the observation that an implied constraint may be
dropped).**  Two factors owned by one
suffix-tree node share their occurrence set, and a longer window at the same start contains
the shorter one, so `C(f) ⊇ C(shortest factor of the node)`.  A covering constraint for a
superset set is *implied* by the constraint for the subset, so deleting every non-shortest
factor changes neither `gamma` nor `LP*`.  Consequence: `|U| <= 2n-1` constraints, `n`
variables — the LP is small.  MY-COMPUTATION checks it: `gamma` and `LP*` agree between the
`2n-1`-element node universe and the definition-level `n(n+1)/2`-element factor universe on
all 2046 binary texts `n <= 10` and all 3279 ternary texts `n <= 7`.

**(1b) `LP* >= delta` (MY-INFERENCE, checked exactly on every instance).**  Let `F_k` be the
distinct factors of length `k`, `|F_k| = d_k`, `delta = max_k d_k/k` (KNP23).  Summing the
constraints of `F_k` for any feasible `x`:

    d_k <= sum_{f in F_k} sum_{p in C(f)} x_p = sum_p x_p * #{f in F_k : p in C(f)} <= k sum_p x_p,

because a position `p` crosses only the length-`k` factors occurring in `[p-k+1, p+k-1]` — at
most `k` of them.  Hence `LP* >= d_k/k` for every `k`, in particular `LP* >= delta`.  The
same argument inside one universe gives `LP*_k >= d_k/k` for the single-`k` universe, and
`LP*_{<=k} >= max_{j<=k} d_j/j`.  (A tempting stronger claim `LP*_k >= delta` is **false**:
`01` at `k = 2` has `LP*_2 = 1` while `delta = 2`.  Recorded here because it was my first
mistake.)

**(1c) The generic bound for context.**  For a set-cover instance with maximum set size `d`,
LP rounding gives `gamma <= H_d · LP*` (RT87, Chvatal79 — UNVERIFIED numbering, standard).
Here `d = max_f |C(f)| <= n`, so `gamma/LP* <= H_n` is the literature bound that a constant
gap would dramatically improve on.  Conversely the set-cover LP *can* have gap
`Theta(log |U|)` — the folklore family is: universe = all `k`-subsets of `[m]`, one set per
point `i in [m]`; then `x = 1/k` is feasible with `sum x = m/k` while any integral cover
needs `m-k+1` points, so the ratio `k(m-k+1)/m = Theta(m) = Theta(log |U|)` for `k = m/2`
(MY-INFERENCE; standard).  Since `|U| <= 2n` here, a `Theta(log n)` gap would mean
`Theta(log n)` on texts of length `n` — which is exactly what these measurements do not see.

## 2. Method: what makes each number a certificate

`tools/gap/simplex.py` is an exact rational simplex (one phase on the dual, whose all-slack
basis is feasible; two phases on the primal).  Entering rule: Dantzig, switching to Bland's
rule after a fixed number of pivots so cycling is impossible in exact arithmetic.

**The certificate shape is the pair.**  `cover_lp` returns a value only together with a
primal-feasible `x` and a dual-feasible `y`, both *re-checked after the solve*, with
`sum(x) == sum(y)`.  By weak duality, `sum y <= LP* <= sum x` (Chvatal83; PROVED, checked
concretely), so such a pair **is** a proof that the reported value is the LP optimum.  A bug
in the pivot rule can then only *fail to find* the optimum, and that failure shows up as a
certificate that does not close → `LPCertificateError`, never a number.  The primal `x` is
read off the dual tableau as the shadow prices of the dual's constraints (the reduced cost of
each slack column, `x_p = -d_{slack_p}`); `cover_lp_primal` recomputes `LP*` by two-phase
simplex on the primal itself, and `check.py` requires the two to agree everywhere, and
requires agreement with a third, fully independent solver — **exhaustive enumeration of every
basic feasible solution** — on all binary `n <= 6` (both universes) and 200 random covering
LPs.

`gamma` is exact by branch and bound (exhaustive; branch on the uncovered element with the
fewest free positions, prune with the incumbent and with a greedy packing of pairwise
disjoint rows).  The returned position set is re-checked against **every** row, and then by
two definition-level verifiers: tools/attractor's `Instance.verify` (independent of the
masks) and repmeter's `verify_attractor_bruteforce` (enumerates every factor and occurrence).
Agreement with exhaustive subset enumeration and with `gamma_bruteforce` is asserted on every
binary `n <= 10` / ternary `n <= 7` text.

Sourcing: SA/LCP, `delta`, the node universe, the verifiers are **reused from
`tools/repmeter` and `tools/attractor`** via `sys.path` (loaded under the alias
`attractor_instance`, since both directories contain an `instance.py`); nothing existing was
rewritten or modified.

## 3. Results

### 3.1 Growth of the maximum gap, per length (exhaustive)

Maximum over **all** `2^n` binary and `3^n` ternary texts of each length.  Last two columns:
how many texts exceed 1, and the argmax text with its `(gamma, LP*)`.  Generated by
`python3 gap.py --growth 12 --growth-ternary 8 --ks 1,2,3 --fast` (40 s) for `n <= 12`, then
`--growth 16 --ks 1 --fast` (15 min, 131 070 texts) for the rest.  The single-`k` column was not
recomputed for `n >= 13` (only the full universe was, to keep the scan inside its budget), so
those cells read `–`: the `k <= 3` maxima are established for `n <= 12` only.

| n | binary texts | **max gap** | # gap > 1 | argmax text | (gamma, LP*) | max single-k gap |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 2 | 1 | 0 | `0` | (1, 1) | 1 |
| 2 | 4 | 1 | 0 | `00` | (1, 1) | 1 |
| 3 | 8 | 1 | 0 | `000` | (1, 1) | 1 |
| 4 | 16 | 1 | 0 | `0000` | (1, 1) | 1 |
| 5 | 32 | 1 | 0 | `00000` | (1, 1) | 4/3 (k=2) |
| 6 | 64 | 1 | 0 | `000000` | (1, 1) | 4/3 (k=2) |
| 7 | 128 | **6/5** | 4 | `0010110` | (3, 5/2) | 4/3 (k=3) |
| 8 | 256 | **9/7** | 16 | `01101001` | (3, 7/3) | 3/2 (k=3) |
| 9 | 512 | **9/7** | 36 | `001001101` | (3, 7/3) | 3/2 (k=3) |
| 10 | 1024 | **9/7** | 110 | `0010011010` | (3, 7/3) | 3/2 (k=3) |
| 11 | 2048 | **9/7** | 200 | `00100110100` | (3, 7/3) | 3/2 (k=3) |
| 12 | 4096 | **4/3** | 408 | `001010010001` | (3, 9/4) | 3/2 (k=3) |
| 13 | 8192 | **15/11** | 808 | `0110101101110` | (3, 11/5) | – |
| 14 | 16384 | **4/3** | 1668 | `00110111101001` | (4, 3) | – |
| 15 | 32768 | **4/3** | 3424 | `001000010110011` | (4, 3) | – |
| 16 | 65536 | **4/3** | 7312 | `0001000010110011` | (4, 3) | – |

| n | ternary texts | max gap | # gap > 1 | argmax text | (gamma, LP*) |
| --- | --- | --- | --- | --- | --- |
| 1 | 3 | 1 | 0 | `0` | (1, 1) |
| 2 | 9 | 1 | 0 | `00` | (1, 1) |
| 3 | 27 | 1 | 0 | `000` | (1, 1) |
| 4 | 81 | 1 | 0 | `0000` | (1, 1) |
| 5 | 243 | 1 | 0 | `00000` | (1, 1) |
| 6 | 729 | **4/3** | 18 | `010212` | (4, 3) |
| 7 | 2187 | 6/5 | 162 | `0010110` | (3, 5/2) |
| 8 | 6561 | **4/3** | 576 | `01021201` | (4, 3) |

**The distribution over the whole exhaustive range** (not just the maximum):

| alphabet | texts | distinct gap values | gap = 1 | next | max |
| --- | --- | --- | --- | --- | --- |
| binary `n <= 12` | 8190 | 9 | 7416 (90.55 %) | `6/5` ×546, `9/7` ×156 | `4/3` ×4 |
| ternary `n <= 8` | 9840 | 6 | 9084 (92.32 %) | `8/7` ×540, `6/5` ×162 | `4/3` ×24 |

The full binary histogram: `1`: 7416, `6/5`: 546, `9/7`: 156, `9/8`: 40, `5/4`: 12, `15/13`:
8, `4/3`: 4, `21/17`: 4, `12/11`: 4.  It is a tight cluster just above 1: no instance with
`n <= 12` is worse than `4/3`, nothing with `n <= 16` is worse than `15/11`, and nothing is
worse than `3/2` in any single-`k` universe at `n <= 12`.  Over `n <= 16` the number of
non-integral binary texts is 4, 16, 36, 110, 200, 408, 808, 1668, 3424, 7312 for `n = 7..16`
— it doubles every length, i.e. the *fraction* settles at about 11 %, while the maximum stays
put.  That is the signature of a bounded gap that a small fraction of instances approach, not
of a gap that grows with `n`.

**The four `4/3` texts** (each `gamma = 3`, `LP* = 9/4`; the LP certificate is on file in
`check.py`, which recomputes the pair):

| text | gamma positions | LP* | dual (fractional) |
| --- | --- | --- | --- |
| `001010010001` | 2, 7, 8 | 9/4 | `y(000)=3/4`, `y(00101)=1/2`, `y(0010)=y(001)=y(01001)=y(1001)=1/4` |
| `011101101011` | 1, 4, 7 | 9/4 | `y(0111)=3/4`, `y(010)=y(0110)=1/2`, `y(011)=y(1011)=1/4` |
| `100010010100` | 1, 4, 7 | 9/4 | `y(000)=3/4`, `y(1001)=y(101)=1/2`, `y(0100)=y(100)=1/4` |
| `110101101110` | 2, 7, 8 | 9/4 | `y(111)=3/4`, `y(010)=y(0110)=1/2`, `y(1101)=y(110)=1/4` |

What the witness looks like: the fractional solution splits its weight over positions that
cover repeated *short* factors (`000`, `010`, `0010`, `0110`), and no integral set of 9/4-sized
positions can do the same job with 3 positions — the integral optimum needs 3, the LP only 2.25.
This is a "fractional cover of a handful of repeated short factors" gap, not a big gadget.

**The maximum over all binary strings with `n <= 16` is `15/11 = 1.3636`, at `n = 13`**, and it is
attained by exactly four texts (verified by scanning all 8192 texts of length 13):

| text | n | gamma | gamma positions | LP* | gap | dual support |
| --- | --- | --- | --- | --- | --- | --- |
| `0110101101110` | 13 | 3 | 3, 8, 9 | 11/5 | 15/11 | `y(0)=1/5`, `y(1101)=y(110)=y(11)=1/5`, `y(011010)=y(10110)=2/5`, `y(111)=3/5` |
| `0111011010110` | 13 | 3 | 1, 4, 7 | 11/5 | 15/11 | (same shape) |
| `1000100101001` | 13 | 3 | 1, 4, 7 | 11/5 | 15/11 | (same shape) |
| `1001010010001` | 13 | 3 | 3, 8, 9 | 11/5 | 15/11 | (same shape) |

Each is a one-symbol extension of an `n = 12` `4/3` witness (`001010010001` → `1001010010001`),
so the two maxima are the same construction at consecutive lengths, not two phenomena.  The LP
for `0110101101110` is `x = (3:1/5, 4:1/5, 5:3/5, 8:1/5, 9:2/5, 10:3/5)`, `sum x = 11/5`, and the
pair certificate (both sides feasible, `sum x = sum y = 11/5`) closes; the primal route and the
`n(n+1)/2`-element factor universe both agree (`gamma = 3`, `LP* = 11/5`).  Note `delta = 2` in all eight witnesses,
so the LP is 10 % above KNP's `delta` at `n = 13` and 12.5 % above it at `n = 12` — the
`delta <= gamma` bound of KNP23 is *not* what the LP is tracking: the LP sees more than `delta`
does, which is why the gap here is small in the first place.

**Fit of the trend** (`gap.py --growth 16` prints this; `n >= 3`, 14 points; floats are used
*only* for the fit — no bound in this note comes from it):

| model | c | residual SS / total SS | max abs residual |
| --- | --- | --- | --- |
| constant | 1.217 | **0.300** | 0.217 |
| `1 + c/n^(1/3)` | 0.380 | 0.456 | 0.263 |
| `1 + c/sqrt(n)` | 0.481 | 0.539 | 0.278 |
| `1 + c/log2 n` | 0.474 | 0.562 | 0.299 |

The **bounded-constant** model explains the observed maxima best (residual 0.30 of the total),
and among the three decaying shapes the faster-decaying `n^(-1/3)` beats `1/log n` — the opposite
of log-driven growth.  More telling than the residuals is *what each model predicts next*, because
all three decaying shapes are monotone **decreasing** in `n` while the observed maxima rise
(`1` → `6/5` → `9/7` → `4/3` → `15/11`) and then hold:

| model (fitted on `n <= 16`) | c | predicts at `n = 16` | at `n = 64` | at `n = 128` | at `n = 1024` |
| --- | --- | --- | --- | --- | --- |
| constant | 1.217 | 1.217 | 1.217 | 1.217 | 1.217 |
| `1 + c/n^(1/3)` | 0.380 | 1.151 | 1.095 | 1.075 | 1.038 |
| `1 + c/sqrt(n)` | 0.481 | 1.120 | 1.060 | 1.042 | 1.015 |
| `1 + c/log2 n` | 0.474 | 1.118 | 1.079 | 1.068 | 1.047 |
| **measured maximum** | — | **1.333** | — | — | — |

So the decaying models pay for their fit by predicting that *no* instance above `~1.08` exists at
`n = 128`, while the plateau model predicts the maximum stays near `1.2–1.36`.  That is a sharp,
falsifiable split, and it needs no exhaustive `2^128` sweep: **the instrument is `--hunt` at
`n = 64, 128, 256` for hours.**  A single instance with gap `> 1.15` at `n = 128` refutes all three
decaying shapes; a maximum of `~1.05` there supports them and refutes the plateau.  The exhaustive
sweep that would settle it directly is `n = 20` (`10^6` texts, a day of this exact LP) and is out
of reach beyond that.

### 3.2 Families and random texts (large n)

`python3 gap.py --family all --ks 1,2,3 --le-k --fast --max-seconds 180` — 59 instances
measured; one (`thue-morse 2^9`, n = 512) hit its 180 s LP budget and is reported as
*not computed* rather than with a bound.

| family | instances | n range | max gap | median | # gap > 1 |
| --- | --- | --- | --- | --- | --- |
| Fibonacci `F_2..F_16` | 15 | 2 … **987** | **1** | 1 | 0 |
| Thue–Morse `2^1..2^8` | 8 | 2 … **256** | 9/7 (n = 8) | 1 | 3 |
| random binary | 36 | 8 … **128** | 15/13 (n = 24) | 1 | 3 |

* **Fibonacci: exactly integral at every length measured**, `gamma = LP* = 2` up to `n = 987`
  (the LP solves in 6.5 s there because the instance is repetitive).  Since `gamma = delta = 2`
  on Fibonacci words (tools/attractor's table), the LP *attains* KNP's `delta` bound here.
* **Thue–Morse: `8/7` at `n = 16, 32`, then exactly `1` at `n = 64, 128, 256`.**  Not monotone
  along the family: `LP*` reaches 4 and closes the gap at `n = 64` and stays there.
* **Random binary: 33 of 36 are exactly integral**; the worst is `15/13 = 1.1538` at `n = 24`
  (`gamma = 5`, `LP* = 13/3`).  On incompressible text the gap is *small* — as one expects,
  since there most factors occur once, `C(f)` is a single interval, and the instance is an
  interval-stabbing-like one, which is LP-integral.
* **Hill-climbing over texts** (`--hunt`: random restarts, single-symbol mutations, accept on
  ties, 150 s per length) at `n = 13, 16, 20, 24, 32, 48, 64`: the best gaps found were `4/3`
  (n = 13, 20, 24), `9/7` (n = 16), `6/5` (n = 32), `21/19` (n = 48), `12/11` (n = 64).  Beyond
  `n ≈ 24` the search **loses** ground — random-ish long texts are nearly integral — so the only
  way to keep the maximum up is the structured construction behind the `n = 12, 13` witnesses, and
  the hunt did not rediscover it from scratch at `n >= 20`.  A search, not a bound; it says the
  maximum did not grow, not that it cannot.

### 3.3 The single-`k` universes — where the fractional difficulty lives

| universe | max gap, all binary `n <= 12` | first seen | witness | certificate |
| --- | --- | --- | --- | --- |
| `k = 1` | **1** | — | `sigma` positions, one per symbol | PROVED: `gamma_1 = LP*_1 = sigma` |
| `k = 2` | **4/3** | n = 5 | `01001` | `gamma_2 = 2`, `LP*_2 = 3/2` |
| `k = 3` | **3/2** | n = 8 | `01100110`, `111111101110` | `gamma_3 = 2`, `LP*_3 = 4/3` |
| `k <= 2` | **1** on binary; 4/3 on ternary | n = 6 (ternary) | binary: all 8188 texts integral; ternary: `010212` | `gamma_{<=2} = 4`, `LP*_{<=2} = 3` |
| `k <= 3` | **4/3** | n = 11 | `00100110100` | `gamma = 3`, `LP* = 9/4` |
| `k <= 4` | 4/3 | n = 12 | `001010010001` | `gamma = 3`, `LP* = 9/4` |
| all factors | 4/3 | n = 12 | `001010010001` | `gamma = 3`, `LP* = 9/4` |

**`k = 1` is exactly integral — PROVED.**  The universe is the `sigma` distinct symbols and
`C(c)` is the occurrence set of `c`.  Integer: `gamma_1 = sigma` (each of the `sigma` rows
needs its own position, and one occurrence per symbol suffices).  LP: `x_p = 1/count(S[p])` is
feasible with value `sigma`, and summing the `sigma` constraints gives the same lower bound.
`check.py` asserts `gamma_1 = LP*_1 = sigma` on every text swept.

**The single-`k` maximum does not grow either.**  A hill-climb in the `k = 3` universe
(`--hunt-k 3`, 150 s per length) found `3/2` at `n = 10` (`1102110211`, `gamma_3 = 2`,
`LP*_3 = 4/3`) and `n = 14` (`01110110111101`, same values), then `9/7` at `n = 20`, `5/4` at
`n = 28`, `6/5` at `n = 40`: the same picture as the full universe — a maximum that stays at
`3/2` and then loses ground.  `3/2` is the largest gap seen anywhere in this lane, and it is a
*single-length* instance.

**`k >= 2` is not integral, and the brief's reason for expecting otherwise is wrong.**  The
consecutive-ones property holds only when every factor has a *unique* occurrence: then `C(f)`
is the single interval `[i, i+k)`, each row of the matrix is consecutive, and (by total
unimodularity of a consecutive-ones matrix — Fulkerson–Gross, *Incidence matrices and interval
graphs*, Pacific J. Math. 15(3):835–855, 1965, doi:10.2140/pjm.1965.15.835; UNVERIFIED
citation from memory, standard fact) the LP is integral.  With two occurrences `C(f)` is a *union*
of intervals: `abracadabra` at `k = 2` has `C(ab) = {0,1} ∪ {7,8}`, the matrix is not
consecutive-ones, and indeed `gamma_2 = 4 > LP*_2 = 7/2`.

**A striking pair of rows.**  The *length-2-only* universe has gap `4/3`, but the
**{length 1 and 2}** universe is exactly integral on all 8188 binary texts with `n <= 12`
(MY-COMPUTATION; the scope *binary* is part of the claim — on ternary texts it fails, `010212`
has gap `4/3` in the {1,2} universe).  Adding the single-symbol constraints — the most "trivial" rows there are —
removes the fractional optimum entirely.  So it is not the number of lengths but *which*
lengths: the repeated short factors of length `k >= 2` carry the fractional weight, and the
length-1 rows cut it off.  The `k <= 2` row is also a warning against reading the
single-`k` numbers as a localisation of the *full* problem's difficulty: `{1,2}` is integral
while `{2}` is not, and `{1,2,3}` is back to `4/3`.

**Consequence for localisation (the brief's step 4).**  The measured picture is the opposite
of the hoped-for one: the fixed-`k` gap is 1 only at `k = 1`; at `k = 2, 3` it is *larger* than
the full instance's maximum (`3/2 > 9/7`, and `3/2 > 1` on the same text).  So the fractional
weakness is a property of a **single length** with repeated factors, and the full instance is
*easier* for the LP because the additional long-factor constraints raise `LP*` faster than they
raise `gamma`.  If one wanted to build a family with a growing gap, the measurements point at
the single-`k` universes (fixed `k`, large `n`), not at the full one.  That is a concrete next
experiment, not a result.

## 4. What this says about Question B — and what it does not say

**Supported by the data (MY-COMPUTATION; empirical, not a theorem).**

1. `gamma/LP* <= 15/11` on every instance solved exactly here: 131 070 binary texts with
   `n <= 16` (exhaustively, so this is the *true* maximum for those lengths), 9840 ternary
   texts with `n <= 8`, 59 morphic/random texts to `n = 987`, plus hill-climbed texts to
   `n = 64`.  The maximum `15/11 = 1.3636` is at `n = 13`; every length `12..16` has its
   maximum in `[4/3, 15/11]`.
2. The typical instance is exactly integral (89.3 % of binary texts `n <= 16`, 92.3 % of
   ternary `n <= 8`, 33/36 random texts to `n = 128`, all 15 Fibonacci words).
3. The per-length maximum is a *plateau* (`1, 6/5, 9/7, 9/7, 9/7, 9/7, 4/3, 15/11, 4/3, 4/3,
   4/3` for `n = 6..16`), and a one-parameter fit prefers a **bounded constant** over
   `1 + c/log n`, `1 + c/sqrt(n)` or `1 + c/n^(1/3)`.  The count of non-integral texts doubles
   with `n` (4, 16, 36, 110, 200, 408, 808, 1668, 3424, 7312 for `n = 7..16`), so the *fraction*
   stays at `10-11 %` (9.9 % at `n = 13`, 11.2 % at `n = 16`) while the maximum does not move.  Neither
   the maximum nor its trend looks like `Theta(log n)` over this range (`log2 16 = 4`).

**Not claimed.**  That the gap is `O(1)` as a theorem.  `n <= 16` cannot separate `O(1)` from
`Theta(log n)`: fitted on `n <= 16`, `1 + c/log2 n` needs `c = 0.47` and then predicts `1.07` at
`n = 128` — i.e. it predicts the gap is *already decaying*, which the exhaustive data contradicts
(the maxima rise through `n = 13`).  The discriminating experiments are in §3.1's prediction table:
`--hunt` at `n = 64..256` (one instance with gap `> 1.15` at `n = 128` refutes every decaying
shape), and the exhaustive sweep at `n = 17..20` if a day of compute is available.  What *is* excluded is the crude hypothesis "the
attractor LP inherits the generic `Theta(log |U|)` set-cover gap on ordinary texts" — on the
texts measured the LP is tight or nearly tight.  Also not claimed: that a small gap gives a
constant-factor *algorithm*; rounding a fractional cover of these `C`-sets is a separate
problem, untouched here.

**UNVERIFIED, and what would settle each point.**

| claim | status | what settles it |
| --- | --- | --- |
| `gamma/LP* = O(1)` uniformly | OPEN — the maximum is `15/11` over all `n <= 16` binary texts, `1` on Fibonacci up to `n = 987` | a family with a growing gap (`--hunt` at `n = 64..256`, or an adversarial construction); or a duality/TDI proof on the node matrix |
| `gamma/LP* <= 15/11` for **every** binary string | VERIFIED for `n <= 16` and open above; the weaker `<= 4/3` is **REFUTED** (`n = 13`) | the `n <= 16` sweep is exhaustive (see §3.1); above it, search |
| `gamma/LP* = Theta(log n)` for some family | UNSUPPORTED — none found | exhibit one: the single-`k` universes are the plausible place (see 3.3) |
| the maximum `15/11` is attained only at `n = 13` among `n <= 16` | MY-COMPUTATION (exhaustive) | the exhaustive scan at `n = 17..20` (`2^20` texts is already impractical; `--hunt` is the instrument) |
| `LP* >= delta` | MY-INFERENCE, checked exactly on ~18 000 instances | the one-paragraph proof in §1b is complete; a Lean lane could formalize it |
| the literature facts (`H_d` rounding, `Theta(log)` set-cover gap, consecutive-ones TU) | UNVERIFIED here (not opened this session) | open the DOIs listed under *Sources* |

## 5. Reproduce

```sh
cd tools/gap
timeout 300 python3 instance.py                                   # all universes on a few texts
timeout 900 python3 gap.py --growth 12 --growth-ternary 8 --ks 1,2,3 --fast   # §3.1, 40 s
timeout 1800 python3 gap.py --growth 16 --ks 1 --fast                          # §3.1, 15 min
timeout 600 python3 gap.py --family all --ks 1,2,3 --le-k --fast --max-seconds 180  # §3.2
timeout 900 python3 gap.py --hunt 20,24,32,48 --hunt-seconds 150 --ks 1 --fast      # §3.2
timeout 900 python3 check.py                                      # the acceptance tests, ~140 s
```

Every run above is under `timeout`; every loop in the code asserts progress (the exact search
raises on its node cap, the LP raises `LPTimeout` at its deadline, the sweeps raise on any
invariant violation) so a hang or a budget overrun produces *no* number rather than a wrong
one.  `check.py` (142 347 checks, 138 s on this machine) exits non-zero if any of these fails: the
invariants `LP* <= gamma` and `LP* >= delta` (or `>= d_k/k` for the single-`k` universes), the
dual/primal certificate closure, agreement of the two LP routes, the vertex-enumeration
cross-check, or the `gamma` cross-checks.

## 6. Relation to the earlier note and to the Lean lane

* `docs/research/attractor-approx.md` §2(d) leaves the integrality gap OPEN and conjectures
  **C2**: "*the LP integrality gap on this family is `O(1)`, sharply `OPT_LP >= gamma/2`*",
  with the experiment "for all `2^n` binary strings, `n <= 12`, exact `gamma` and the LP
  optimum in exact rational arithmetic".  **That experiment is now run and
  C2's sharp form is confirmed at these scales**: the worst ratio over all binary `n <= 16` is
  `gamma/LP* = 15/11`, i.e. `LP* >= 0.733 gamma`, comfortably above the conjectured `gamma/2`.
  C2 as stated (`O(1)`) is *not* refuted by anything measured here — and C2 is sharper than what
  the data supports in one direction: its `O(1)` is not established, only `<= 15/11` on
  `n <= 16`.  The same note's claim in §2(b)-(c) that "the
  problem is already NP-complete for one fixed constant `k >= 3`" (KPRR18) is consistent with
  3.3 above: the single-`k` universe is where the fractional weakness (and the hardness) sits.
* `docs/research/attractor-approx.md` §3 lists "LP dual" as a lower bound with "unknown"
  tightness and "needs a checkable rational dual".  This lane supplies exactly that machine
  (`Cover.lp` returns the dual `y` with the certificate), and the measurement says the LP dual
  is *very* tight: on the exhaustive range `LP* >= (11/15) gamma ≈ 0.733 gamma`, so an LP-dual
  lower bound is within 27 % of `gamma` on every binary instance with `n <= 16` and exactly tight
  on ~89 % of them.  That is the practical answer to "should a tool ship an LP-dual lower bound?":
  yes — it dominates the 0/1 packing bound and `delta` on most instances, and it is certified by
  a rational dual vector.
* **Terminology, to avoid the collision AGENTS.md warns about.**  `factors_k` in this note is
  the *`k`-sharp* attractor of `hardness-attractor.md` §2(f) — factors of length **exactly** `k`
  — and `factors_le_k` is the `k`-attractor (all factors of length **at most** `k`).  The brief
  said "universe = length-k factors only", so its table is the `k`-sharp one; both are reported
  because they behave differently (`{2}`-sharp has gap `4/3` while `{<=2}` is integral).
  `hardness-related-binary.md` §4 states the correct condition for integrality ("with one
  occurrence per factor … consecutive-ones/TU; with ≥ 2 occurrences … a union of equal-length
  intervals and no TU structure survives"), and §3.3 here measures exactly that: `k`-sharp `= 1`
  is integral, `k`-sharp `>= 2` is not.  `docs/research/attractor-approx.md` §2(b)'s phrasing
  ("the LP is integral by the consecutive-ones property", with no uniqueness caveat) is the one
  place that reads as a claim about *all* fixed-`k` instances; the measurement refutes it and the
  sibling note already carries the correction.  I did not edit that file (not this lane's).
* For a Lean lane: the only formalizable item produced here is `LP* >= delta` (§1b), a
  counting argument over `d_k`; and `gamma_1 = sigma = LP*_1` (§3.3).  The measurements
  themselves are Python, cheap to re-run, and are the honest source for the numbers.
