# C — `γ` vs `⌈δ⌉`: what is proved, what the closed brackets show, what controls the gap

Labels: **PROVED** (quoted/cited), **MY-INFERENCE**, **MY-COMPUTATION** (ran here, §7), **MY-CONJECTURE**,
**UNVERIFIED**. `σ = d_1` = distinct letters; `d_k` = distinct length-`k` factors; `δ = max_k d_k/k`;
`γ` = smallest attractor; `P(S)` = max number of pairwise **disjoint** coverage sets
`C(f) = {p : p crosses an occurrence of f}` (so `γ ≥ P`); `P̂` = the packing `tools/attractor` certifies
(`P̂ ≤ P`). Logs base 2.

## 0. Verdicts

1. **PROVED** `δ ≤ γ ≤ z = O(δ log(n/δ))`, and `γ = Ω(δ log(n/δ))` is attained for every `(n, δ)`:
   "`γ/2 ≤ δ`" is false and **no** `γ ≤ ⌈δ⌉ + c` holds in general (§3).
2. `γ = δ` **is PROVED** for unary, standard Sturmian (hence Christoffel, Fibonacci) and CS Rote
   pseudopalindromic prefixes — always because `δ = d_1 = σ = γ`. By §2's lemma `γ = δ ⟹ δ = σ`; on
   binary text `γ = δ` forces `δ = 2`.
3. `γ = ⌈δ⌉` **is PROVED** for Thue–Morse `t_n`, `n ≥ 6` (KTMSIT20's own proof of `γ = 4`), and **fails**
   at `n = 4, 5` (`γ = 4 > 3 = ⌈δ⌉`) and at every TM prefix of length 25…59: a theorem about that
   family, not a general rule.
4. **MY-COMPUTATION**: `γ` is **not a function of the `d`-profile** (41 of 123 profile classes over
   binary `n ≤ 12` carry two different `γ`), so no formula in `δ`, `σ`, `#{1,2}-grams` or `r/δ` works;
   the positional quantity that tracks `γ` is `P` (§4). Sharpest surviving conjecture:
   **`γ ≤ ⌈max(δ, P̂)⌉ + 1`** (§5); four existing brackets decide it.

## 1. The true relation, verbatim

**PROVED** [KNP23 Lemma II.4, quoting its ref. [27] Lemma 5.6]: "Every string `S` satisfies `δ ≤ γ`."
**PROVED** [KNP23 Lemma II.2]: "It always holds that `z = O(δ log(n/δ))`" (via Raskhodnikova et al.:
`d_ℓ ≤ m·ℓ` for `ℓ ≤ ℓ_0` ⇒ `z ≤ 4(m log ℓ_0 + n/ℓ_0)`). With `γ ≤ b ≤ z` [KP18 Thm 3.5, Lemma 3.7]:

> **PROVED** `δ(S) ≤ γ(S) ≤ z(S) ≤ 4(δ log(n/δ) + δ)`, i.e. `γ = O(δ log(n/δ))`.

The converse is **false**: **PROVED** [KNP23 §III, Thm III.3] "For every length
`n` and integer value `δ ∈ [2..n]`, there is a string `S[1..n]` with `γ = Ω(δ log(n/δ))`" — Def. III.1
(`S_∞[i] = b` iff `i = 2^j`, else `a`), where Lemma III.2 states "`S_n` satisfies `δ ≤ 2` and
`γ ≥ ½⌊log n⌋`".

## 2. `γ = δ` is PROVED — always because `δ = σ`

**Lemma (trivial).** `σ = d_1/1 ≤ δ`; every attractor covers all single letters, so `γ ≥ σ`
[KP18 Ex. 3.3]. Hence `σ ≤ δ ≤ γ` and **`γ = δ ⟹ δ = σ`**; the converse is false (§3).
**Unary** `a^n`: `δ = γ = 1`.

* **Standard Sturmian words** (all Christoffel, all Fibonacci): **PROVED** `γ = 2` [MRRRS19 Thm 5: for
  each `w ∈ Stand`, `|w| ≥ 2`, a 2-position set is a minimum attractor], and `d_k ≤ k+1` (classical
  `p(k) = k+1`), so `d_k/k ≤ 2 = d_1`. Hence **`γ = δ = 2`**.
* **CS Rote sequences**: complexity `2k` *by definition* (**PROVED** [RR25 Def. 11])
  ⇒ `δ = d_1 = 2`; and **PROVED** [RR25 Thm 19] the minimal attractor of any pseudopalindromic prefix
  equals the number of letters in it. Again `γ = δ = 2`.
* **Period-doubling**: **PROVED** `γ = 2` for every prefix length `n ≥ 2` [SS20 Thm 3];
  **MY-COMPUTATION** `δ = 2` up to `n = 16384` (`d_k ≤ 2k`) ⇒ `γ = δ`. The `d_k ≤ 2k` half is
  **UNVERIFIED** in general.
* **MY-COMPUTATION**: `(ab)^m`, `(aabb)^m`, `(aab)^m`, `(aaab)^m`, `(abc)^m` all have `γ = δ = σ`.
  **MY-INFERENCE**: for `p`-periodic `S`, `n ≥ 3p`, `d_k ≤ p` gives `δ ≤ p`, and `p` suitably placed
  consecutive positions form an attractor, so `γ ≤ p` — a bound, not `γ ≤ ⌈δ⌉`.

**The one proved `γ = ⌈δ⌉` family, and where it breaks.** **PROVED** `γ(t_n) = 4` for `n ≥ 4`
[KTMSIT20 Thm 3] and `δ(t_n) = 10/(3+2^{4−n}) > 3` for `n ≥ 6` [KTMSIT20 Thm 4]; as `γ ≥ δ` is an
integer, that is `γ = ⌈δ⌉ = 4` for `n ≥ 6`. For `n = 4, 5` (lengths 16, 32) they say "it can be verified
by computation", precisely because `δ = 5/2, 20/7` give `⌈δ⌉ = 3 < 4 = γ`. The failure region is explicit
over all prefixes: **PROVED** [SS20 Thm 5] `a_n = 3` for `7 ≤ n ≤ 14` and `17 ≤ n ≤ 24`, `a_n = 4` for
`n = 15, 16`, `n ≥ 25`; **MY-COMPUTATION** `⌈δ⌉ = 3` for every prefix length ≤ 59 (`δ` = 5/2 → 20/7 →
38/13 → 3; `40/13` from length 60, where SS20's `γ ≥ δ > 3` takes over). So every TM prefix of length
25…59 has `γ = 4 > ⌈δ⌉ = 3`.

## 3. Witnesses that kill `γ ≤ ⌈δ⌉`

1. **PROVED**: KNP23 Thm III.3 (§1).
2. **MY-COMPUTATION, tiny**: prefixes of KNP's family have `δ = 2` exactly for `n ≤ 28`, while
   `γ = 3` for `n = 8…20`, `γ = 4` at `n = 24, 28`: `bbabaaab` (`δ=2, γ=3`),
   `bbabaaabaaaaaaabaaaaaaaaaaaa` (`δ=2, γ=4`) — exhaustive `k`-subset search with `Instance.verify`.
3. **MY-COMPUTATION**, all with `δ = d_1`: `aababb` (`2,3`), TM `2³` = `abbabaab` (`2,3`), de Bruijn
   `B(2,3)` = `aaababbb` (`2,3`), `B(2,5)` (`28/5, 7`), paperfolding `n = 64, 128` (`4, 5`). So neither
   "`γ = ⌈δ⌉` when `δ = d_1`" nor "`γ ≤ δ + 1`" holds (TM `2⁴`: `δ = 5/2`, `γ = 4`).
4. **Run-length bounds do not rescue it**: random text with all runs `≤ 2`: `n = 128`,
   `δ = 94/11 ≈ 8.545`, `γ = 11 = ⌈δ⌉ + 2`.
5. **Repo data**: random binary `n = 2048`, `δ = 1824/13 ≈ 140.31`, packing LB `γ ≥ 165 > ⌈δ⌉ = 141`.
   Over binary `n ≤ 12`: `γ − ⌈δ⌉ ∈ {0,1,2}`, mostly `≤ 1`.

**Reading the closed brackets.** `[2,2]` on `F₁₄`/`F₁₈`, `[4,4]` on `mississippi`/`abracadabra`: closed by
`δ = σ = γ` (§2). TM `2⁸`/`2¹⁰`: closed by KNP's bound plus KTMSIT20's `γ ≤ 4`. Four of the five test the
*σ*-lemma, not the strength of `δ`.

## 4. What controls the gap: position, via the disjoint-coverage packing

**The `d`-profile does not determine `γ`.** Grouping all binary strings `n ≤ 12` by the full profile
`(d_1,…,d_n)` gives 123 classes; 41 carry two different `γ`. Profile `(2,4,4,3,2,1)` is shared by
`aaabba` (`γ = 2`) and `aababb` (`γ = 3`) — same `n`, `σ`, `δ`, profile. That kills
every profile-based candidate at once (1-/2-gram counts, `d_k/k` shape, `r/δ`).

**Separating experiment (run): fixed `n = 28`, `σ = 2`, `δ = 2`; only the rare symbol's spacing varies.**

| text | `δ` | `P̂` | `γ` (exhaustive) | unique-factor mass |
|---|---|---|---|---|
| `b` at `1,3,7,15` (`2^j−1`, `j ≥ 1`) | 2 | 3 | 3 | 0.83 |
| `b` at every 2nd position | 2 | 2 | 2 | 0.07 |
| `b` at `0,1,3,7,15` | 2 | 4 | 4 | 0.84 |
| `b` at `1,3,7`, then every 8 | 2 | 2 | 3 | 0.66 |

`δ`, `σ`, `n`, alphabet fixed; `γ` moves by 2. What tracks it: `P̂` and the fraction of distinct factors
occurring exactly once ("unique-factor mass", an arrangement statistic). That is also the mechanism of the
literature's separation: **PROVED** [KNP23, proof of Lemma III.2] the factors `ba^{2^j−1}b` have unique
occurrences whose "covered regions are disjoint across even integers `j`, so each one requires a distinct
attractor position". Over the 8176 binary texts of length 4…12, `γ = P̂` in 90 % (7358) of cases and
`γ ≤ ⌈max(δ, P̂)⌉ + 1` in all.

## 5. Sharpest conjecture I can defend

**MY-CONJECTURE C1.** `γ(S) ≤ ⌈max(δ(S), P(S))⌉ + 1` for every string (true max packing `P`; using `P̂`
only makes the test easier). *Status*: no violation anywhere computed here — the 8176 binary texts
`n ≤ 12`, TM (`δ = 10/3, P̂ = 3, γ = 4`), KNP `n = 28` (`P̂ = 4 = γ`), paperfolding (`δ = 4, γ = 5`);
the `+1` is attained by §4's last table row. TM `2⁴` shows both devices are needed: `P = 3 = ⌈max⌉` yet
`γ = 4`. *Refuted by* any text closing at `ub ≥ ⌈max(δ, P̂)⌉ + 2` — the four open
brackets are the test: `n = 2048` `[165,179]` (bound 166), `n = 1024` `[91,99]` (93), `n = 512` `[49,52]`
(53), `n = 4096` `[305,332]`; longer runs decide it.

**MY-CONJECTURE C2.** Every prefix of a linearly recurrent word has `γ ≤ ⌈δ⌉ + 1` (TM attains `+1` at
lengths 25…59; Sturmian, period-doubling: `0`). Refuted by one morphic word with an unbounded gap;
decidable per word by [SS20 Thm 1] plus the `O(n)` `δ`.

## 6. Practical consequence

* **In the `σ`-regime the anytime search is provably unnecessary**: if `δ = σ` *and* an explicit
  `σ`-sized attractor verifies, then `γ = σ = d_1`: the `O(n)` SA/δ pass is exact and no search beats
  `σ`. `δ = d_1` alone does **not** suffice (`aababb`, TM `2³`, `B(2,3)`: `δ = d_1 = 2`, `γ = 3`).
* **Outside it, `γ = ⌈δ⌉` is not a rule**: true for TM `2^n` (`n ≥ 6`), false for TM prefixes of length
  25…59, false for paperfolding at `n = 64, 128`, false by `+2` on run-bounded random, and `⌈δ⌉` sits
  15–25 % below certified `γ` on random text. Estimate with `[max(δ, P̂), ub]`, never `⌈δ⌉`.
* **Measure the growth of `γ − max(δ, P̂)`** (`γ/δ` on random text: ≈ 1.18–1.30 at `n = 256…2048`,
  plateauing): growth refutes C1; a bound of 1 says the bracket machinery is near-optimal.

## 7. Reproduction, unverified, one tool defect

Recipe (stdlib, `timeout` everywhere): `Instance`/`delta()`/`packing_bound()` from
`tools/attractor/instance.py`; exact `γ` by `anytime.exact_gamma` **and** independently by
`itertools.combinations` + `Instance.verify` (all numbers passed both). **UNVERIFIED**: (a) `d_k ≤ 2k`
for period-doubling at all `k` (to `n = 16384`); (b) whether the true `P` pins `γ` on incompressible text;
(c) C1, C2; (d) complexity of `γ` at `σ = 2`. **Tool defect**:
`anytime.search` raises `RuntimeError('greedy stalled with 1 uncovered nodes')` on some inputs (e.g.
`abbabaab`, `B(3,2)`) — phase-1 greedy is not total. `exact_gamma`, `packing_bound`, `Instance` are
unaffected.

## Sources

* **KNP23** Kociumaka–Navarro–Prezza, IEEE TIT 2023, [arXiv:1910.02151](https://arxiv.org/abs/1910.02151):
  Lemma II.2, II.4, §III (Def. III.1, Lemma III.2, Thm III.3).
* **KP18** Kempa–Prezza, STOC 2018, [arXiv:1710.10964](https://arxiv.org/abs/1710.10964)
  ([doi:10.1145/3188745.3188814](https://doi.org/10.1145/3188745.3188814)): Thm 3.5, Lemma 3.7, Ex. 3.3.
* **MRRRS19** Mantaci–Restivo–Rombo–Rosone, ICTCS 2019, [arXiv:1907.04660](https://arxiv.org/abs/1907.04660):
  Thm 5. **KTMSIT20** Kutsukake et al., SPIRE 2020, [arXiv:2005.09524](https://arxiv.org/abs/2005.09524):
  Thm 3, 4.
* **SS20** Schaeffer–Shallit, [arXiv:2012.06840](https://arxiv.org/abs/2012.06840): Thm 1, 3, 5.
  **RR25** *String attractors of Rote sequences*, [arXiv:2308.00850](https://arxiv.org/abs/2308.00850):
  Def. 11, Thm 19.
* **BBGKM26** [arXiv:2602.16152](https://arxiv.org/abs/2602.16152): all minimal attractors of Fibonacci /
  period-doubling / Thue–Morse words.
