# gap — the integrality gap of the attractor set-cover LP, measured exactly

The question (Question B of the brief): **what is the integrality gap of the set-cover LP
for the minimum attractor?**  If it is `O(1)`, a constant-factor approximation is within
reach by LP rounding; if it is `Theta(log n)`, the `log`-factor bounds are essentially
inherent for LP-based methods.  Nobody had measured it.

    gap(S) = gamma(S) / LP*(S)    (>= 1 always)

with `gamma` the minimum attractor (an integer covering problem) and `LP*` its LP
relaxation, both **exact** (`fractions.Fraction`, no floating point anywhere in a bound).

## The instance, exactly as specified

`S` is a text of length `n`, positions are `0..n-1`, `f = S[i:i+L]` is a factor, and

    C(f)       = { p : some occurrence [i, i+L) of f has i <= p < i+L }
    set_p      = { f : p in C(f) }
    attractor  = a position set Gamma with union_{p in Gamma} set_p = all distinct factors
    gamma      = min |Gamma|

That is a set-cover instance with universe = distinct factors and one set per position.
`instance.py` builds it three ways:

| universe | elements | how it is built |
| --- | --- | --- |
| `factors` | `<= n(n+1)/2` distinct factors | definition-level brute force: every window, grouped by the factor it spells. No suffix tree, no SA. |
| `nodes` | `<= 2n-1` suffix-tree nodes | tools/attractor's `Instance` (SA/LCP, exact `delta`, independent verifier) |
| `factors_k` / `factors_le_k` | distinct factors of length `= k` / `<= k` | the same brute force restricted in length |

**The node reduction is exact for the LP too, not just for the integer optimum.**  Two
factors owned by one suffix-tree node share their occurrence set, and a longer window
contains the shorter one at the same start, so `C(f) ⊇ C(shortest factor of the node)`.
A covering constraint for a *superset* `C`-set is implied by the constraint for the subset,
so dropping every non-shortest factor changes neither the integer optimum (tools/attractor's
R1) nor the LP optimum.  `check.py` verifies `gamma` and `LP*` agree between the `nodes` and
`factors` universes on every binary text `n <= 10` and every ternary text `n <= 7`
(11 606 texts, both values, both universes).  This is what makes the measurement cheap
enough to run exhaustively.

## What is certified, and how

Nothing here is printed without a certificate, and there is no floating point in any bound.

| quantity | certificate |
| --- | --- |
| `gamma` | branch and bound (exhaustive, hence exact); the returned position set is re-checked against **every row**, then by tools/attractor's `Instance.verify` and by repmeter's `verify_attractor_bruteforce`, both of which are definition-level. `check.py` also compares against exhaustive subset enumeration and `gamma_bruteforce` on every binary `n <= 10` / ternary `n <= 7`. |
| `LP*` | a **primal-feasible `x` and dual-feasible `y` of equal objective**, both re-checked against the instance after the solve (`simplex.check_primal`, `simplex.check_dual`). By weak duality (`sum y <= LP* <= sum x`, Chvatal 1983 Thm 5.1) that pair *is* a proof that the reported value is the LP optimum — a pivot bug could only fail to find the optimum, and that failure shows up as a certificate that does not close and raises instead of returning a number. |
| LP* is not a solver's word | the value is reached by two routes: simplex on the dual (with the primal read off the slack columns' reduced costs) and two-phase simplex on the primal itself. `check.py` requires agreement, and on every binary text `n <= 6` also requires agreement with an **independent LP solver**: exhaustive enumeration of all basic feasible solutions. |
| `LP* <= gamma` | checked on every instance measured (`check.py` sweeping, and again inside `gap.measure`). |
| `LP* >= delta` | checked as an exact Fraction on every instance (see the proof below). |

**`LP* >= delta` (MY-INFERENCE, checked exactly on every instance).**  Let `F_k` be the
distinct factors of length `k`, `|F_k| = d_k`, so `delta = max_k d_k/k` (KNP's
substring complexity).  For any primal-feasible `x`, summing the constraints of the elements
of `F_k`,

    d_k <= sum_{f in F_k} sum_{p in C(f)} x_p = sum_p x_p * #{f in F_k : p in C(f)} <= k * sum_p x_p,

because a position `p` crosses only the length-`k` factors occurring in `[p-k+1, p+k-1]`, at
most `k` of them.  So `LP* >= d_k/k` for every `k`, in particular `LP* >= delta`.  The same
argument restricted to one `k` gives `LP*_k >= d_k/k`, which is the bound checked for the
single-`k` universes.

Two relations that are *not* true, and which the brief assumed or implied:

* **the single-`k` gap is not 1.**  The brief's reasoning was "the fixed-`k` case has
  consecutive-ones structure, so its gap should be 1".  Consecutive-ones holds only when each
  factor has **one** occurrence: then `C(f)` is the single interval `[i, i+k)`.  With two or
  more occurrences `C(f)` is a *union* of intervals, the matrix is not consecutive-ones, and
  the LP is genuinely fractional.  Measured: `k=1` gap 1 (proved below), `k=2` gap up to
  `4/3`, `k=3` gap up to `3/2`;
* **`gap_full >= gap_k` is false**, so the gap is not monotone in the universe: adding the
  longer factors *adds constraints* (`LP*` can only go up) while `gamma` can also go up.  The
  measured counterexample: `111111101110` has `gamma_3 = 2, LP*_3 = 4/3` (gap `3/2`) but
  `gamma = 2, LP* = 2` (gap `1`) in the full universe.  So the single-`k` instance is *harder*
  for the LP than the full instance, not easier.

**`k = 1` has gap exactly 1 (PROVED by hand).**  The universe is the `sigma` distinct
symbols and `C(c)` = the positions where `c` occurs, so `gamma_1 = sigma` (one position per
symbol; fewer cannot hit all `sigma` rows, and distinct symbols need distinct positions) and
the LP is `sigma` too, by `x_p = 1/count(S[p])` (feasible) and by summing the `sigma`
constraints (lower bound).  `check.py` asserts `gamma_1 = LP*_1 = sigma` on every text swept.

## Results

Run on this machine; every number below is produced by `gap.py` and re-checked by
`check.py`.  `delta` is exact; `gamma` and `LP*` are exactly as described above.

### (a)+(b) Growth of the maximum gap, per length (exhaustive)

`gap.py --growth 12 --growth-ternary 8 --ks 1,2,3 --fast`, 40 s.  "max gap" is the maximum
over **all** `2^n` binary (`3^n` ternary) texts of that length; the last column is the maximum
gap of the single-`k` universes at that length.

| n | binary: texts | max gap | # with gap > 1 | argmax (gamma, LP*) | single-k max k=1,2,3 |
| --- | --- | --- | --- | --- | --- |
| 1 | 2 | 1 | 0 | `0` (1, 1) | 1, –, – |
| 2 | 4 | 1 | 0 | `00` (1, 1) | 1, 1, – |
| 3 | 8 | 1 | 0 | `000` (1, 1) | 1, 1, 1 |
| 4 | 16 | 1 | 0 | `0000` (1, 1) | 1, 1, 1 |
| 5 | 32 | 1 | 0 | `00000` (1, 1) | 1, 4/3, 1 |
| 6 | 64 | 1 | 0 | `000000` (1, 1) | 1, 4/3, 1 |
| 7 | 128 | 6/5 | 4 | `0010110` (3, 5/2) | 1, 4/3, 4/3 |
| 8 | 256 | 9/7 | 16 | `01101001` (3, 7/3) | 1, 4/3, 3/2 |
| 9 | 512 | 9/7 | 36 | `001001101` (3, 7/3) | 1, 4/3, 3/2 |
| 10 | 1024 | 9/7 | 110 | `0010011010` (3, 7/3) | 1, 4/3, 3/2 |
| 11 | 2048 | 9/7 | 200 | `00100110100` (3, 7/3) | 1, 4/3, 3/2 |
| 12 | 4096 | **4/3** | 408 | `001010010001` (3, 9/4) | 1, 4/3, 3/2 |

| n | ternary: texts | max gap | # with gap > 1 | argmax (gamma, LP*) |
| --- | --- | --- | --- | --- |
| 1 | 3 | 1 | 0 | `0` (1, 1) |
| 2 | 9 | 1 | 0 | `00` (1, 1) |
| 3 | 27 | 1 | 0 | `000` (1, 1) |
| 4 | 81 | 1 | 0 | `0000` (1, 1) |
| 5 | 243 | 1 | 0 | `00000` (1, 1) |
| 6 | 729 | 4/3 | 18 | `010212` (4, 3) |
| 7 | 2187 | 6/5 | 162 | `0010110` (3, 5/2) |
| 8 | 6561 | 4/3 | 576 | `01021201` (4, 3) |

Over all 8190 binary texts with `n <= 12` the gap takes exactly nine values —
`1, 6/5, 9/7, 9/8, 5/4, 15/13, 4/3, 21/17, 12/11` — with `1` in 7416 of 8190 (90.55 %),
`6/5` in 546, `9/7` in 156, and the maximum `4/3` attained by exactly four texts.  Over all
9840 ternary texts with `n <= 8` there are six values — `1` in 9084 (92.3 %), `8/7` in 540,
`6/5` in 162, `16/13` in 24, `4/3` in 24, `9/7` in 6 — again with maximum `4/3`.  The binary
`4/3` texts:

| text | n | gamma | gamma positions | LP* | gap |
| --- | --- | --- | --- | --- | --- |
| `001010010001` | 12 | 3 | 2, 7, 8 | 9/4 | 4/3 |
| `011101101011` | 12 | 3 | 1, 4, 7 | 9/4 | 4/3 |
| `100010010100` | 12 | 3 | 1, 4, 7 | 9/4 | 4/3 |
| `110101101110` | 12 | 3 | 2, 7, 8 | 9/4 | 4/3 |

The LP solution of the first is fractional (`x_4 = 3/4, x_8 = x_9 = 1/2, x_2 = x_5 = 1/4`;
dual `y = 3/4` on factor `000`, `1/2` on `00101`, `1/4` on `0010, 001, 01001, 1001`): the
integrality gap comes from fractional *coverage of repeated short factors*, not from a big
gadget.

**Shape of the growth.**  The per-length maximum is `1` up to `n = 6`, then `6/5` at `n = 7`,
`9/7 = 1.2857` at `n = 8..11`, and `4/3 = 1.3333` at `n = 12`.  The number of instances with
gap `> 1` grows by roughly `2x` per step (4, 16, 36, 110, 200, 408 — i.e. ~10 % of all
texts).  Over this range the maximum is **bounded by 4/3 and drifts up slowly**; it is
certainly not climbing like `log n` (`log2 12 = 3.58`).  Twelve is far too small to
distinguish `O(1)` from `Theta(log n)` asymptotically — see *What would settle it*.

### (c)+(d) Families and random texts

`gap.py --family all --ks 1,2,3 --le-k --fast --max-seconds 180`.  59 instances measured,
one (`thue-morse 2^9`, n = 512) not computed inside its LP budget and reported as such.

| family | instances | n range | max gap | median | # gap > 1 |
| --- | --- | --- | --- | --- | --- |
| Fibonacci `F_2..F_16` | 15 | 2 … **987** | **1** | 1 | 0 |
| Thue–Morse `2^1..2^8` | 8 | 2 … **256** | 9/7 (n = 8) | 1 | 3 |
| random binary | 36 | 8 … **128** | 15/13 (n = 24) | 1 | 3 |

Details that matter:

* **Fibonacci words: the LP is exactly integral at every length measured**, up to `n = 987`
  (`gamma = LP* = 2`).  That is the strongest single statement here: `gamma` hits KNP's
  `delta` and the LP hits `gamma`.
* **Thue–Morse:** `8/7` at `n = 16` and `n = 32` (`gamma = 4`, `LP* = 7/2`), then exactly `1`
  at `n = 64`, 128, 256 (`LP*` reaches 4).  The gap is not monotone in `n` along a family
  either: the single-`k` universes also wobble (`4/3` at `n = 16`, `9/8` at `n = 32`).
* **Random binary:** 33 of 36 instances are exactly integral; the worst is `15/13 = 1.1538`
  at `n = 24` (`gamma = 5`, `LP* = 13/3`), i.e. the gap on incompressible text is *small*.
  Search over random text at `n` up to 128 never produced a gap above `4/3`.
* A **hill-climb over texts** (`--hunt`, single-symbol mutations, many restarts) at
  `n = 13, 16, 20, 24` found `4/3` at `n = 13` (`1100110100010`, `gamma = 4, LP* = 3`), `9/7`
  at `n = 16`, and `4/3` again at `n = 20` and `n = 24` — never more.  This is a search, not
  a bound: it says the maximum did not grow, not that it cannot.

### (d) The single-`k` universes — where the difficulty actually is

`k = 1` is integral, as proved above.  For `k >= 2` it is not:

| universe | max gap over all binary `n <= 12` | where | witness |
| --- | --- | --- | --- |
| `k = 1` | **1** (exactly, proved) | — | `sigma` positions, one per symbol |
| `k = 2` | **4/3** | n = 5 | `01001`: `gamma_2 = 2`, `LP*_2 = 3/2` |
| `k = 3` | **3/2** | n = 8 | `01100110` (`111111101110`): `gamma_3 = 2`, `LP*_3 = 4/3` |
| `k <= 2` | **1** (binary only) | — | all 8188 binary texts `n <= 12` are exactly integral; ternary already has `4/3` (`010212`) |
| `k <= 3` | **4/3** | n = 11 | `00100110100`: `gamma_{<=3} = 3`, `LP*_{<=3} = 9/4` |
| `k <= 4` | **4/3** | n = 12 | `001010010001`: `gamma = 3`, `LP* = 9/4` |
| all factors | **4/3** | n = 12 | `001010010001`: `gamma = 3`, `LP* = 9/4` |

Note the length-2-only universe (`4/3`) versus the {1,2} universe (`1` on every binary text
`n <= 12`): adding the single-symbol rows removes the fractional optimum, so it is *which*
lengths that matters, not how many.  So: the fixed-`k` gap is 1 only for `k = 1`; at `k = 2, 3` it already exceeds the full
instance's maximum (`3/2 > 4/3 > 9/7`).  **The brief's localisation is inverted**: the
difficulty is present at a *single* fixed length, and mixing lengths *reduces* the gap,
because the longer factors' constraints raise `LP*` faster than they raise `gamma`.

### The answer to Question B, stated as evidence rather than theorem

* The measured integrality gap is **at most 4/3** on all 8190 binary strings `n <= 12`, all
  9840 ternary strings `n <= 8`, 59 morphic/random texts up to `n = 987`, and a hill-climb at
  `n <= 64`.  Most instances are exactly integral (90.6 % of binary `n <= 12`, 33/36 random
  texts, all 15 Fibonacci words).
* There is **no evidence of a growing gap**, and in particular none of a `Theta(log n)` gap on
  these families: at the lengths where an LP-based method would already be losing a constant
  factor 2–3, the LP is either exactly tight or off by at most 4/3.
* This does **not** prove a constant gap.  A `Theta(log n)` gap family, if it exists, is not
  among the natural ones sampled here, and `n <= 12` cannot see asymptotics.  What the data
  does rule out is the *cheap* hypothesis "the attractor LP has the generic `Theta(log n)`
  set-cover gap on ordinary texts": on ordinary texts it is `1` or `1 + O(1/log n)`-ish.
* Consequence for the strategy in the brief: an `O(1)`-gap conjecture survives every test
  here (best measured: `4/3`), so LP-rounding is **not obviously blocked**; but LP rounding
  of a `4/3`-gap LP would still only give a `4/3`-factor algorithm if one could solve the LP
  and round *constructively* — the gap being small says nothing about the rounding step.
  With `OPT_LP >= gamma * 3/4` one gets `gamma <= 4/3 OPT_LP`; rounding a fractional solution
  to an integral one with `O(1)` blow-up is a separate (unresolved here) problem.

### What would settle it

1. **A family with a growing gap.**  The natural test is `n` up to a few hundred over *all*
   binary strings — impossible exhaustively, so the honest instrument is the hill-climb
   already in `gap.py --hunt`, run for hours at `n = 64, 128, 256`, plus structured
   adversarial families (concatenations of blocks like the `4/3` witnesses, de Bruijn-like
   texts, `a^k b^k` shapes).  If the maximum stays near `4/3` at `n = 256`, the "gap is
   `O(1)`" claim has real support; if it climbs, the maximum's growth rate is the answer.
2. **A theorem either way.**  The LP here is a covering LP whose rows are the `C`-sets of the
   suffix-tree nodes; a proof that the *node* matrix has bounded integrality gap (e.g. via a
   balanced/separable-matrix argument, or via total dual integrality of some active
   submatrix) would settle it in the positive direction.  This measurement supplies the
   exact instances on which such a proof can be tested (`Cover.rows` is the matrix).

## Files

| file | what it is |
| --- | --- |
| `instance.py` | the three universes as `Cover` objects; exact `gamma` by branch and bound; the definition-level verifier; `delta`, `d_k`, and the `d_k/k` LP bound |
| `simplex.py` | exact rational simplex (one-phase on the dual, two-phase on the primal), the primal/dual certificate, `cover_lp`, `cover_lp_primal` |
| `gap.py` | the experiment driver: corpora, per-length growth table, hill-climb, summaries with the full distribution |
| `check.py` | acceptance tests; exits non-zero on the first class of failure |
| `README.md` | this file |

```sh
timeout 120 python3 instance.py                     # sanity: a few texts, all universes
timeout 900 python3 gap.py --all --max-seconds 60   # the tables (long)
timeout 900 python3 gap.py --growth 12 --growth-ternary 8 --ks 1,2,3 --fast
timeout 600 python3 gap.py --family all --ks 1,2,3 --fast --max-seconds 180
timeout 900 python3 check.py                       # the acceptance tests
```

## Costs and limits, honestly

* The LP has `n` variables and at most `2n-1` rows (`nodes`) or `n(n+1)/2` rows (`factors`),
  and the exact simplex is written in `Fraction` arithmetic with no pivoting heuristics
  beyond Dantzig-then-Bland.  Measured: `n = 64` 0.5 s, `n = 128` 11 s, `n = 256` 41 s,
  `n = 512` beyond a 180 s budget.  **That is the wall**: the largest `n` this exact LP
  handles is a few hundred, which is why the families stop at 987 (Fibonacci, 6.5 s —
  repetitive texts are easy) and 512 (Thue–Morse, not reached).
* `gamma` is exact by branch and bound with a packing lower bound; it is fast on repetitive
  text and hits its node cap on random text beyond `n ≈ 150` (reported as *not computed*).
  Attractor's own `Instance.uncovered`-based counting is not used as a certificate anywhere
  here; the verifiers are the definition-level ones.
* Division of labour with `tools/attractor`: SA/LCP, `delta`, the suffix-tree node universe
  and the independent verifier come from there (`sys.path`, loaded under the alias
  `attractor_instance` so the two `instance.py` files cannot collide); the LP, the exact
  branch and bound, and the covering-universe bookkeeping are here.

## What did not work (so it is not retried)

1. **"The fixed-`k` instance has consecutive-ones structure, so its gap is 1."**  False for
   `k >= 2`: consecutive-ones needs *unique* occurrences.  `abracadabra` at `k = 2` already
   refutes it (`gamma_2 = 4`, `LP*_2 = 7/2`, gap `8/7`).
2. **"`gap_full >= gap_k`"** (my own inference, written before measuring): false, see above.
3. **"`LP*_k >= delta`"** (my first version of the invariant): false — the `d_k/k` bound is
   only available for the lengths *inside* the universe.  `01` at `k = 2` has `LP*_2 = 1` and
   `delta = 2`.  The invariant was corrected to `LP*_universe >= max_{j in lengths} d_j/j`.
4. **A single uniform tableau size does not scale.**  The first version solved both the
   primal and the dual on every text, which made the exhaustive scan 6x slower than needed
   for no extra information: the pair certificate already pins `LP*`, and `check.py` runs both
   routes on everything small.

## Self-tests

`timeout 900 python3 check.py` — 41 171 checks, 0 failures, ~75 s:

| test | what it pins down |
| --- | --- |
| 1 | the simplex equals exhaustive **vertex enumeration** on all binary `n <= 6` (both universes) and 200 random covering LPs; its two routes always agree; hand cases including a fractional optimum (`3/2`) and an infeasible instance |
| 2-4 | on every binary `n <= 10` and ternary `n <= 7`: `LP* <= gamma`, `LP* >= delta`, `gamma` = exhaustive subset enumeration = `gamma_bruteforce`, the reported `Gamma` passes two independent verifiers, `nodes` and `factors` give the same `gamma` and the same `LP*`, and `gamma_k <= gamma`, `LP*_k <= LP*_full` |
| 5 | the single-`k` maxima (`4/3` at `k=2`, `3/2` at `k=3`), with the full primal/dual certificate printed for the witness, plus the fact that the `k=3` gap *exceeds* the full gap of the same text |
| 6 | the headline maximum: `4/3` over all binary `n <= 12`, at exactly the four texts listed, each with `gamma = 3`, `LP* = 9/4` and a closed certificate |
| 7 | the family spot checks (`thue-morse` 16/64, `fibonacci` 55/144, random 32/64) |
| 8 | the certificate plumbing itself: an overloaded dual and an under-covering primal are rejected, valid ones accepted |
