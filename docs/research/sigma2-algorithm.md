# The minimum attractor on a binary alphabet: is `γ` computable?

**Lane:** `tools/sigma2-alg/` (the "opposite bet" of `tools/sigma2/`: try to *algorithmise*
`γ` at `σ = 2` instead of reducing hardness into it).
**Question attacked:** does `γ` have exploitable structure at `σ = 2`? (`docs/research/hardness-attractor.md`
§3–5 records this as OPEN: no source proves hardness at `σ = 2`, none gives an algorithm.)

**Labels.** PROVED = proof given here or in the cited source. COMPUTATIONALLY-CHECKED = exact
certified computation, scope stated. MY-CONJECTURE = my extrapolation from data, not proved.
UNVERIFIED = asserted, not checked.

---

## 0. Verdict

**No structure found that yields an algorithm.** Every cheap structural parameter I tested fails to
determine `γ`, and the one route that would have given an algorithm (compute `γ_k` for small `k`,
which is polynomial at `σ = 2`) dies because the necessary `k` grows like `n/2` on the measured range.

What the numbers *do* settle, and which is worth more than the negative:

| question | answer | strength |
|---|---|---|
| Is `γ ≤ γ₂ + c` for a constant `c`? | **NO — refuted for every `c`.** `γ − γ₂ → ∞` along binary de Bruijn words, and `γ/γ₂ → ∞` too | PROVED (§3) |
| Is `γ ≤ ⌈δ⌉ + c` for a small `c`? | **Not refuted.** `c = 0` fails from `n = 6`, `c = 1` from `n = 12`, `c = 2` **fails** at `n = 32` (witness in §4). No family with a growing gap was found; on de Bruijn words `γ = ⌈δ⌉` exactly | COMPUTATIONALLY-CHECKED to `n = 13` exhaustive + hill-climb to `n = 48` |
| Is `γ` a function of `(δ, d_k profile, γ₂, runs, period, rare-symbol gap, packing)`? | **NO** for each of those, and for all their combinations I tried; smallest witnesses in §5 | PROVED by exhaustive counterexample, `n ≤ 10` |
| Exact algorithm via `γ_k` for small `k`? | **Dead.** `k*(s) = min{k : γ_k = γ}` has max `1,2,3,4,5` at `n = 5,6,8,10,12` — it grows ≈ `n/2` | COMPUTATIONALLY-CHECKED, `n ≤ 12` exhaustive |
| Tightest surviving lower-bound description | `γ ≤ max(⌈δ⌉, packing) + 1` on every binary word, `n ≤ 12`; gap `0` on de Bruijn words up to `n = 69`, `1` at `n = 48` | COMPUTATIONALLY-CHECKED (and `packing` exact is MIS-hard, so this is *not* an algorithm) |

**The single most useful line for the hardness lane** (`tools/sigma2/`): the difficulty is **not**
localised in short factors. `γ − γ₂` is unbounded, so no reduction needs to hide anything in the
short-`k` part — the hardness (`γ`) genuinely lives in factors of length up to `n`, even though the
*value* of `γ` at `σ = 2` stays within a small additive window of `⌈δ⌉` on everything I measured.

---

## 1. What is computed, and why the numbers can be trusted

`γ` is taken from `../attractor/anytime.py`'s iterative deepening, and a value is reported **only**
when the bracket is closed: an explicit position set that passes the definition-level
`Instance.witness`, plus an exhausted DFS over every position set smaller than it
(`features.gamma_certified`). A run that hits its node budget or its per-call wall-clock cap (≤ 5 s in
all sweeps) raises `NotClosed` and is counted as *incomplete*, never reported as a number.

Three independent cross-checks (`check.py validate`, all passing):

1. **Two solvers, one universe from the suffix tree, one from scratch.** `features.gamma_k(s, n)`
   builds the distinct-factor universe directly from the string and solves min set cover by iterative
   deepening; it agrees with `anytime` on all 1023 words with `n ≤ 10`.
2. **`γ` is complement-invariant** on all `2^n` words, `n ≤ 12` (8190 words) — used only as a check,
   and to halve the enumeration: `check.py` iterates the `2^(n−1)` words starting with `a`, so the
   `words` column of Table 2 is the number of *representatives* while the exhaustive claim covers
   all `2^n` words (the complement of each representative, which has the same `γ`).
3. **Literature anchors reproduce**: `γ(Fibonacci_m) = 2` for `|F| ∈ {8,13,21,34,55,89,100}`
   (MRRRS19 / BBGKM26), `γ(t_n) = 4` for Thue–Morse of length 16, 32 (KTMSIT20).

Two facts measured in passing, both COMPUTATIONALLY-CHECKED and both new to me:

* **`γ(T) = γ(T^R)`**: reversal invariance held on **all** 4095 binary words with `n ≤ 12`, although
  the attractor condition is not reversal-symmetric (a factor and its reverse have unrelated
  occurrence sets). I do not have a proof; it is a data point, not a claim.
* **`γ`(Thue–Morse)**: `2, 2, 3, 4, 4` at lengths `2, 4, 8, 16, 32`. So `γ(t_n) = 4` first holds at
  length 16, i.e. at index `n = 4`. `docs/research/attractor-approx.md` §3 writes
  "`γ(t_n) = 4` for `4 ≤ n ≤ 8`", which is only consistent if `n` is the *index* (length `2^n`); read
  as a length it is false at lengths 4 and 8. **Repo nit worth fixing** (I did not edit that file).

---

## 2. The gap table (`check.py gap`)

`cd tools/sigma2-alg && timeout 1800 python3 check.py gap --nmax 13 --samples 2000 --top 17`
Rows `n ≤ 13` are **exhaustive over all `2^n` binary words**; rows `14 ≤ n ≤ 17` are **2000 uniform
random words each** (marked SAMPLED). No word was excluded for an unclosed bracket (`incomplete = 0`).

| n | words (rep.) | max(γ−⌈δ⌉) | max(γ−γ₂) | #{γ>⌈δ⌉} | argmax γ−⌈δ⌉ | argmax γ−γ₂ |
|---|---|---|---|---|---|---|
| 2 | 2 | 0 | 0 | 0/2 | `ab` | `ab` |
| 3 | 4 | 0 | 0 | 0/4 | | |
| 4 | 8 | 0 | 0 | 0/8 | | |
| 5 | 16 | 0 | 0 | 0/16 | | |
| 6 | 32 | **1** | 0 | 1/32 | `aababb` (γ=3, ⌈δ⌉=2, δ=2) | `abbbbb` |
| 7 | 64 | 1 | **1** | 6/64 | `abbabaa` | `abbabaa` (γ=3, γ₂=2) |
| 8 | 128 | 1 | 1 | 25/128 | `abbbabaa` | `abbbabaa` |
| 9 | 256 | 1 | 1 | 61/256 | `abbbbabaa` | `abbbbabaa` |
| 10 | 512 | 1 | 1 | 145/512 | `abbbbbabaa` | `abbbbbabaa` |
| 11 | 1024 | 1 | 1 | 304/1024 | `abbbbbbabaa` | `abbbbbbabaa` |
| 12 | 2048 | **2** | **2** | 592/2048 | `aabababbabbb` (γ=4, ⌈δ⌉=2, δ=2) | `abbbbabaaaab` (γ=4, γ₂=2) |
| 13 | 4096 | 2 | 2 | 1172/4096 | `abbbabbababaa` (γ=4, ⌈δ⌉=2) | `abbbbbababbaa` |
| 14 | 2000 S | 2 | 2 | 609/2000 | `bbbbabbbababaa` | `bbbbbabbaabaaa` |
| 15 | 2000 S | 2 | 2 | 663/2000 | `bbaababaabaaaaa` | `bbbbbabbbaaaaba` |
| 16 | 2000 S | 2 | 2 | 758/2000 | `bbaababaaabaabaa` | `bbbbbbababaabbaa` |
| 17 | 2000 S | 2 | **3** | 885/2000 | `bbbaabaabbababaaa` (γ=5, ⌈δ⌉=3, δ=11/4) | `bbbaabaabbababaaa` (γ=5, γ₂=2) |

First `n` where `γ > ⌈δ⌉`: **6**, smallest witness `aababb` (`γ=3`, `δ=2` exactly, so `⌈δ⌉=2`;
`γ = δ+1`).
First `n` where `γ > γ₂`: **7**, smallest witness `abbabaa` (`γ=3`, `γ₂=2`).

`γ > ⌈δ⌉` is not exotic: it holds for **29 %** of binary words at `n = 13` and **44 %** of the
sampled words at `n = 17`. So `δ` is a *tight* lower bound (`γ = ⌈δ⌉` is the common case) but not an
exact formula.

An earlier inline run of the same solver completed the exhaustive enumeration to `n = 18` for these
two maxima: `max(γ−⌈δ⌉) = 2` and `max(γ−γ₂) = 2, 2, 3, 3, 3` at `n = 14,15,16,17,18`.

---

## 3. `γ ≤ γ₂ + c` — REFUTED for every constant `c` (PROVED), and `γ/γ₂` is unbounded too

**Lemma 1 (trivial).** For every word over `{a,b}`, `γ₂ ≤ 6`. (One position inside an occurrence of
each distinct factor of length ≤ 2; there are at most `2 + 4 = 6` of them.)

**Lemma 2 (elementary).** Let `B_k` be a binary de Bruijn word of order `k`: `|B_k| = 2^k + k − 1`
and every `k`-mer occurs in it, exactly once. Then `d_k(B_k) = 2^k`, hence
`δ(B_k) = max_j d_j/j ≥ 2^k/k`.

**Lemma 3 (KNP, cited in `docs/research/attractor-approx.md` §3: `δ ≤ γ`).** `γ ≥ δ`.

**Theorem.** `γ(B_k) − γ₂(B_k) ≥ 2^k/k − 6 → ∞` and `γ(B_k)/γ₂(B_k) ≥ (2^k/k)/6 → ∞`.
Hence **for every constant `c` there is a binary word with `γ > γ₂ + c`, and one with
`γ > c·γ₂`.** PROVED from Lemmas 1–3; no computation needed beyond the existence of de Bruijn words.

Measured, with exact `γ` (`check.py bruijn --kmax 6`, brackets closed):

| `k` | `n = \|B_k\|` | `d_k` | `δ` | `⌈δ⌉` | `γ` | `γ₂` | `γ−γ₂` | `γ−⌈δ⌉` |
|---|---|---|---|---|---|---|---|---|
| 2 | 5 | 4 | 2 | 2 | 2 | 2 | 0 | 0 |
| 3 | 10 | 8 | 8/3 | 3 | 3 | 2 | 1 | 0 |
| 4 | 19 | 16 | 4 | 4 | 4 | 2 | 2 | 0 |
| 5 | 36 | 32 | 32/5 | 7 | 7 | 2 | 5 | 0 |
| 6 | 69 | 64 | 32/3 | 11 | 11 | 2 | **9** | **0** |

(`k = 7`, `n = 133`: bracket **not** closed in 150 s; the certified lower bound is `19 = ⌈δ⌉` with
`γ₂ = 2`, so `γ − γ₂ ≥ 17` there by the same argument — a lower-bound-only statement.)

**Two consequences.**

1. The "localisation" hope — that all the difficulty sits in factors of length 2, so an exact `γ₂`
   (linear time at `σ = 2`) plus a bounded correction would solve `γ` — is **false**, definitively.
   There is no `c` and no multiplicative factor.
2. `γ ≤ 3γ₂`, `γ ≤ γ₂ + 10` etc. are all false; anything phrased against `γ₂` must have an
   `n`-dependent factor.

---

## 4. `γ ≤ ⌈δ⌉ + c` — not refuted, and `c = 2` is refuted

`δ` is computable in linear time (KNP), so a bounded additive gap `γ ≤ ⌈δ⌉ + c` would make `γ`
*determined* to within `c` by a linear-time quantity — the closest thing to structure I found.

What the data says:

* `c = 0` fails at `n = 6` (`aababb`, `γ = 3 = δ+1`);
* `c = 1` fails at `n = 12` (`aabababbabbb`, `γ = 4`, `δ = 2`);
* **`c = 2` fails at `n = 32`**: single-flip hill climbing (`check.py hunt`) found
  ```
  s = bbbaaaabbabbaaabbaaaabbaabbaabaa      (n = 32)
  γ = 6   δ = 3 (exactly)   ⌈δ⌉ = 3   γ₂ = 2   packing = 6
  Γ = [2, 3, 10, 15, 22, 28]                 (verified from the definition)
  ```
  so `γ − ⌈δ⌉ = 3` and `γ/δ = 2`. Re-checked with the definition-level solver (`γ₃₂ = 6`), the raw
  factor-count profile (`δ = 3` by direct counting, agreeing with the suffix-array route), and the
  `anytime` bracket `lb = ub = 6`.
* hill-climb maxima of `γ − ⌈δ⌉`: `2, 2, 2, 2, 3, 2, 3` at `n = 16, 20, 24, 28, 32, 40, 48`
  (`n = 16,20,24`: `hunt --ns 16,20,24 --rounds 10`; `n = 28,32,40`:
  `hunt --ns 28,32,40 --rounds 10`; `n = 48`: `hunt --ns 48,64 --rounds 8`, which was killed at
  `n = 64` before finishing — 200–650 certified `γ` calls per row, single-symbol flips to a local
  optimum from uniform random starts, seed 0). `n = 32` witness as above; `n = 48` witness
  `bbabbabbbbabaababaabbabbbabbbaaababbabaaaaabaabb` with `γ = 9`, `δ = 35/6`, `⌈δ⌉ = 6`, `γ₂ = 2`,
  `packing = 8`. **These maxima are lower bounds on the true maximum over all binary words**: a
  hill climb can witness a large gap and can never certify its absence, so `max = 2` in a row means
  "no gap of 3 was found", nothing stronger.
* On **10384 structured words** (`check.py families`, run grids `a^i b^j a^k b^l`, `(a^i b^j)^t`,
  `a^i (ab)^j`, `(aab)^i (abb)^j`, Thue–Morse and Fibonacci with `a`-padding, `n ≤ 64`) the maximum
  is `2`, at `aaabbabaabbaababbabaababbaabbabaab` (`γ = 5`, `⌈δ⌉ = 3`).
* On de Bruijn words (Table §3) `γ = ⌈δ⌉` exactly for `k = 2..6`, the only family where I have an
  unbounded `δ`.

**Verdict on this question:** `γ ∈ {⌈δ⌉, …, ⌈δ⌉+2}` is false; `γ ≤ ⌈δ⌉ + 3` is consistent with
everything measured (`n ≤ 48`). Whether `max(γ − ⌈δ⌉)` is bounded at all is **not settled** by my
data: it steps `0 → 1` at `n = 6`, `1 → 2` at `n = 12`, `2 → 3` at `n = 32`, and two of the three
steps are exactly where a new "block" becomes affordable — a step pattern that could either saturate
at 3 or continue as `Θ(log n)`. **MY-CONJECTURE (weak, falsifiable):** `max(γ−⌈δ⌉)` is unbounded but
grows like `Θ(log n)`; the first test that would decide it is hill climbing at `n = 64, 80, 100`,
where I ran out of budget (`n = 64` needs minutes per restart).

---

## 5. What determines `γ`, and what does not (`check.py dependence`)

Method (no statistics): for each feature set `F`, group every binary word by `F(s)`; a group holding
two different `γ` values refutes "`γ` is a function of `F`". Exhaustive over all `2^n` words,
`n ≤ 10`.

| feature set | verdict `n ≤ 10` | smallest witness (two words, same vector, different `γ`) |
|---|---|---|
| `⌈δ⌉` | **refuted** (n=6) | `aaaaab` γ=2 vs `aababb` γ=3, both `⌈δ⌉=2` (`δ=2`) |
| `d_k` profile `(d_1..d_n)` | **refuted** (n=6) | `aaabba` γ=2 vs `aababb` γ=3, **both profile `(2,4,4,3,2,1)`** |
| `γ₂` | **refuted** (n=7) | `aaaaaab` γ=2 vs `aababba` γ=3, both `γ₂=2` |
| `(⌈δ⌉, γ₂)` | **refuted** (n=7) | same pair (both `⌈δ⌉=2`, `γ₂=2`) |
| `(profile, γ₂)` | **refuted** (n=7) | `aaabbaa` γ=2 vs `aaababb` γ=3, both `((2,4,5,4,3,2,1), 2)` |
| `(runs, max run, period, rare-symbol gap)` | **refuted** (n=6) | `aabbab` γ=2 vs `aababb` γ=3, both `(4, 2, 6, 1)` |
| `(packing, ⌈δ⌉)` | **refuted** (n=7) | `aaaaaab` vs `aababba`, both `packing=2`, `⌈δ⌉=2` |
| `(γ_1..γ_4)` | determines | — (but see §6: this is `γ_n` in disguise, not a shortcut) |
| `(γ_1..γ_6)` | determines | — |
| everything above together | determines | — |

The pattern in the witnesses is the whole story of this lane: **`aababb` is the smallest word with
`γ = 3`, and it shares its `d_k` profile with `aaabba`, whose `γ = 2`.** So `γ` depends on *which*
factors of a given length are replaced by others (the arrangement), not on how many there are of each
length — and `δ`, the `d_k` profile, the run structure and the period are all blind to exactly that.
The pair `aaaaaab` (γ=2) / `aababba` (γ=3) does the same job for `γ₂` and for `packing`.

So `γ` is not a function of any single computable scalar I tried, nor of the natural pairs. The only
vectors that determine it at these sizes contain `γ_k` for `k` up to 4 — and §6 shows why that is
circular.

The tightest *quantitative* statement I have, from the same machinery (exhaustive, `n ≤ 12`):

> `max(γ − max(⌈δ⌉, packing)) = 1` on every binary word with `n ≤ 12`
> (witness `aaaaaaababba`: `γ=3`, `⌈δ⌉=2`, `packing=2`).

and `γ − packing = 0` at the hill-climbed extremal words `n = 32` (`packing = γ = 6`) and `n = 40`
(`packing = γ = 8`), `1` at `n = 48`. `packing` here is `Instance.packing_bound`, i.e. a **heuristic**
maximum independent set in the co-coverability graph — the exact optimum is NP-hard, so this is a
description of `γ`, not an algorithm for it.

---

## 6. The one candidate algorithm, and exactly why it dies (`check.py lift`)

At `σ = 2` and fixed `k`, `γ_k` is computable in `O(n) + exp(O(2^k·k))` time (KPRR18 Thm 29 — every
fixed `k` is polynomial, per `docs/research/hardness-attractor.md` §3). Since `γ_k ≤ γ_{k+1} ≤ γ` and
`γ_n = γ`, the natural hope was: **`γ = γ_{k(n)}` for a small `k(n)`** (then `γ` is computable, and
at `k = O(log log n)` even in polynomial time).

`k*(s) = min{k : γ_k(s) = γ(s)}`, exhaustive:

| n | k* distribution | worst witness | max k* |
|---|---|---|---|
| 2–5 | `{1: all}` | — | 1 |
| 6 | `{1:31, 2:1}` | `aababb` | 2 |
| 7 | `{1:58, 2:2, 3:4}` | `aababba` | 3 |
| 8 | `{1:103, 2:4, 3:21}` | `aaabaabb` | 3 |
| 9 | `{1:175, 2:6, 3:73, 4:2}` | `aabbbabba` | 4 |
| 10 | `{1:283, 2:9, 3:193, 4:27}` | `aaaabaaabb` | 4 |
| 11 | `{1:443, 2:12, 3:473, 4:88, 5:8}` | `aaababaabaa` | 5 |
| 12 | `{1:667, 2:16, 3:1101, 4:224, 5:40}` | `aaaaabaaaabb` | 5 |

(counts are over `2^(n−1)` complement representatives). `max k* = 1, 2, 3, 4, 5` at
`n = 5, 6, 8, 10, 12`: **`k*` grows with `n`**, at least like `n/2` on this range, and the strings
needing large `k*` are common (`γ_3 < γ` for **54 %** of words at `n = 12`). So there is no small
`K` with `γ = γ_K`, and the route is dead. The most common `k*` is 3 (huge mass at `k* = 3`), which
is consistent with the `γ_2 < γ` phenomena of §2, but the tail is what matters and it is `Θ(n)`.

**Second, sharper negative inside this route**: the bound `k* ≤ minlen_max` (the longest
"shortest factor" over suffix-tree nodes — once `k` reaches it every node's own representative is
covered) is the only *a priori* bound I have, and `minlen_max` is `Θ(n)` on the witnesses above
(`minlen_max = 6` for the `n=12` witness `aaaaabaaaabb`, `7` for `abababab`), so even the structural
bound is not small.

---

## 7. What failed, precisely

Per route, with the exact step that breaks:

1. **"`γ` is a function of `δ` (or `γ₂`, or the `d_k` profile, or runs/period/gap)."** Breaks at
   `n = 6`: `aaabba` and `aababb` have the **same `d_k` profile `(2,4,4,3,2,1)`** and `γ = 2` vs
   `γ = 3`; `aaaaab` and `aababb` share `δ = 2`. Nothing a count-based summary can see distinguishes
   them; the difference is *arrangement* (which factors of each length occur), which is exactly what
   the profile forgets.
2. **"`γ ≤ γ₂ + c`."** Breaks for every `c`, at `n = 32` already for `c < 4` (witness in §4), and
   for all `c` by de Bruijn words (§3). The mechanism: `γ₂ ≤ 6` always, while `γ ≥ δ` is unbounded
   along words with many distinct `k`-mers. Short factors cannot see the long unique-ish factors
   that force positions.
3. **"`γ ≤ ⌈δ⌉ + 2`."** Breaks at `n = 32` (§4). This is the only one of the three I could not push
   to a family; the extremal example is isolated, which is why I flag `γ ≤ ⌈δ⌉ + 3` as still open.
4. **"`γ = γ_K` for a constant (or `log log n`) `K`."** Breaks at `n = 6` and then repeatedly;
   `k*(s)` reaches `n/2` on this range (§6).
5. **"`γ` is bounded below tightly by an exactly-computable combinatorial bound."** `max(⌈δ⌉,
   packing)` is within `1` of `γ` on all `n ≤ 12`, but the exact `packing` is a maximum independent
   set in the co-coverability graph (NP-hard), and the *greedy* packing used as a feature is a
   heuristic — so this is a description, not an algorithm. Undetermined: whether `packing` (exact)
   equals `γ` on every binary word (the LP-gap lane's data says `LP* ≥ 0.733γ`, so an exact-packing
   route would have to beat the LP on instances where the LP is not integral).
6. **"Look for the structure in `γ_k` for `k ≤ 6` and extrapolate."** `(γ_1..γ_4)` determines `γ` on
   `n ≤ 10` *because* `k* ≤ 4` there; the determination disappears exactly when `k*` passes the cap.

---

## 8. Honest bottom line

* **Verdict: no structure found; the binary case stays OPEN as far as this lane can see.** No exact
  algorithm fell out, and the two most natural approximations of it are either refuted
  (`γ₂ + c`, for all `c`) or only numerically supported (`⌈δ⌉ + 3`).
* The *positive* residue is a small, testable conjecture: **`γ` is within an additive `O(log n)` of
  `⌈δ⌉` on binary words, with `max(γ−⌈δ⌉) = 3` already at `n = 32`** (MY-CONJECTURE; `γ ≤ ⌈δ⌉+3`
  unrefuted to `n = 48`). If true, binary `γ` is *value-wise* pinned by a linear-time quantity — a
  strong statement about the problem, though still not an algorithm (deciding which of `c+1` values
  it takes is the hard part, and even *constructing* an attractor of size `⌈δ⌉+3` is open).
* **What would settle it, in the order I would try:** (a) hill-climb `γ − ⌈δ⌉` at
  `n = 64, 80, 100` (needs minutes per restart at `n = 64`; the code is `check.py hunt --ns 64,80`);
  (b) a family search guided by the `n = 32` witness structure (`aaab`/`bbab` block concatentation)
  instead of blind flips; (c) decide whether exact `packing = γ` at `σ = 2`, which would give an
  FPT-flavoured algorithm; (d) an LP-dual certificate from `tools/gap/` reaching `γ` on the extremal
  words above — if the LP is integral there, the `15/11` gap may be an artefact of small `n`.

---

## 9. Files, commands, reproducibility

Everything is stdlib-only Python 3, imports `../attractor/{instance,anytime}.py` read-only, writes
nothing outside `tools/sigma2-alg/`. Every loop asserts progress (the exact searches raise on their
node cap; `gamma_certified` raises `NotClosed` instead of returning an open bracket). All runs below
were wrapped in `timeout`; no run was allowed to exceed the caps stated.

```bash
cd tools/sigma2-alg
timeout  600 python3 check.py validate  --solver-nmax 10        # solvers agree, anchors reproduce
timeout 1500 python3 check.py gap       --nmax 13 --samples 2000 --top 17
timeout  500 python3 check.py dependence --nmax 10              # what determines gamma
timeout  420 python3 check.py lift      --nmax 12 --klift 5     # k* grows, route dead
timeout 1200 python3 check.py bruijn    --kmax 6                # gamma - gamma_2 unbounded (PROOF family)
timeout  550 python3 check.py families  --maxlen 64             # 10384 structured words
timeout  600 python3 check.py hunt      --ns 28,32,40 --rounds 10
```

| file | what it is |
|---|---|
| `features.py` | exact features of a binary word (`d_k` profile, `δ`, `γ_k` for small `k`, runs, period, rare-symbol gap, packing, node statistics) + `gamma_certified` (closed-bracket-only `γ`) + `gamma_k` (independent definition-level exact `k`-attractor solver) |
| `check.py` | the six experiments above: `validate`, `gap`, `dependence`, `lift`, `bruijn`, `families`, `hunt` |
| `sigma2-algorithm.md` | this report |

**Labels recap.** PROVED: Lemmas 1–3 and the theorem of §3; the de Bruijn facts; `γ_k` monotone and
`γ_n = γ`. COMPUTATIONALLY-CHECKED: every number in every table, with the enumeration/sample size
printed with it. MY-CONJECTURE: `max(γ−⌈δ⌉) = Θ(log n)`; `γ(T) = γ(T^R)` for all binary `T`
(measured `n ≤ 12`, no proof). UNVERIFIED: that no polynomial algorithm for binary `γ` exists
(nothing here bears on it beyond the failed routes).
