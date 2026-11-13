# Guaranteed-bound attractor constructions, and the structure that might beat them

`γ` is the size of the smallest string attractor. This note keeps only *pre-measured* bounds:
constructions whose output size is bounded by a computable measure, i.e. approximation
algorithms with a stated ratio. It is the theory contract for `tools/approx/` and a later
Lean lane; `docs/research/space.md` is the companion measure-hierarchy note. Logs base 2.

**Verdicts.** PROVED = read in a primary source (quoted when short); OPEN = source says
unknown; MY-INFERENCE = derived by me from cited facts; MY-COMPUTATION = computed here
(recipe given); UNVERIFIED = primary statement not confirmed.

**Sources.** **KP18** Kempa–Prezza, STOC 2018, doi:10.1145/3188745.3188814, arXiv:1710.10964
(numbers from v4; KPRR18 cites the NP-hardness as "Thm 8"). **KPRR18** Kempa–Policriti–
Prezza–Rotenberg, *String attractors: verification and optimization*, ESA 2018, LIPIcs 112
(doi:10.4230/LIPIcs.ESA.2018.52), arXiv:1803.01695. **KNP23** Kociumaka–Navarro–Prezza,
IEEE Trans. Inf. Theory 2023, arXiv:1910.02151. **KTMSIT20** Kutsukake et al., SPIRE 2020,
doi:10.1007/978-3-030-59212-7_15, arXiv:2005.09524. **W25** Whittington, *Online string
attractors*, LNCS 2025, doi:10.1007/978-3-031-81396-2_15, arXiv:2407.15599. **BBGKM26**
Banbara et al., CPM 2026, doi:10.4230/LIPIcs.CPM.2026.33, arXiv:2602.16152. **TM26**
arXiv:2610.10950.

## 1. State of the art

### 1.1 The three constructive bounds, verbatim

KP18, **Theorem 3.5** (PROVED, read): "Let `C` be a collage system of size `c` generating
`T`. Then, `T` has an attractor of size at most `c`." An SLP is a collage system, so
`γ ≤ g`. KP18, **Lemma 3.7** (PROVED, read, constructive): "Let `z` be the number of factors
of the Lempel-Ziv factorization of a string `T`. Then, `T` has an attractor of size `z`."
Proof, verbatim: "We insert in `Γ_LZ77` all positions at the end of a phrase" — so
`|Γ_LZ| = z` exactly. Likewise `γ ≤ r` (Thm 3.9), `γ ≤ e`, `γ ≤ 2b`.

KNP23, **Lemma II.2** (PROVED, read): "It always holds that `z = O(δ log(n/δ))`"; the proof
gives `z ≤ 4(δ log(n/δ) + δ)`. KNP23, **Lemma II.4** (PROVED, read): "Every string `S`
satisfies `δ ≤ γ`" — already machine-checked here
(`substringComplexity_le_card_attractor`, `SortBounds/Projects/Repetitiveness/Attractor.lean`).

Chaining, with `δ ≤ γ`:
**`|Γ_LZ| = z ≤ 4(δ log(n/δ)+δ)`** and hence `z/γ ≤ 4 log(n/δ) + 4` (MY-INFERENCE from the
three quoted items; `γ ≥ δ` and `h(x) = x log(n/x) + x` is *not* monotone on `[0,n]` — it
peaks near `0.74n` — so the ratio must be stated against `δ`, not by writing
`h(δ) ≤ h(γ)`). The O(log n) headline is unaffected; the sharper-looking constant form
`4 log(n/γ)+4` is **not** proved. Hierarchy (proved): `δ ≤ γ ≤ 2b ≤ 2c ≤ 2z ≤ 2g_rl ≤ 2g`
(KP18 Thm 3.6 gives a factor 2 at the macro-scheme step); the honest summary is
`γ = O(min(b,c,z,r,g_rl,g))` up to constants, **not** a total order
(KNP23 §VI), separated by `γ = Ω(δ log(n/δ))` (KNP23 Thm III.3) and `γ = o(b)` on Thue–Morse
(arXiv:2104.09985). Consequence: `δ` is the only polynomial-time-computable **lower** bound in the
chain and can sit a `Θ(log(n/δ))` factor below `γ`, so no algorithm certified by `δ` alone
can claim better than `log n`.

### 1.2 Hardness and approximation, per `k`

`k`-attractor = cover all factors of length `≤ k`; the full attractor is `k = n`.

* **PROVED** (KP18 Thm 4.2, read): "For `k ≥ 3`, `k`-Attractor is NP-complete."
* **PROVED** (KP18, read): "In particular, this proves the NP-completeness of the original
  string attractor problem (i.e., the case `k=n`)." The lift from constant `k` to `k = n`
  uses the monotonicity gadget `γ_k(T_C) = γ_{k'}(T_C)` for `k < k' ≤ |T_C|` (KP18 proof of
  Thm 4.2 and Cor 4.4).
* **PROVED** (KP18 Thm 4.3, read): "For any constant `k ≥ 3`, Minimum-`k`-Attractor is
  APX-complete" — a `2k`-approximation computable in linear time plus a reduction from
  bounded-degree vertex cover. **PROVED** (KP18 Cor 4.4, read): "For every constant `ε>0` and
  every (not necessarily constant) `k≥3`, it is NP-hard to approximate Minimum-`k`-Attractor
  within factor `11809/11808 − ε`." Since `k` may be non-constant and ranges up to `|T_C|`,
  this covers `k = n`: the **full attractor has no PTAS**, threshold `1.0000847`
  (MY-INFERENCE for `k=n`; the corollary does not say so).
* **PROVED** (KPRR18 Thm 33, read): "A `H(k(k+1)/2)`-approximation of a minimum `k`-attractor
  can be computed in `O(min{n², nk², n+σ^{2k-1}k²})` expected time", with
  `H(k(k+1)/2) ≤ 1 + 2ln((k+1)/√2) ∈ O(log k)`. At `k = n` this is `1+2ln(n/√2) ≈ 1.39 log₂ n + 0.3`
  in `O(n²)` expected time — the best proved constant for the full attractor that I found.
* **PROVED** (KPRR18 Thm 31, read): "Any minimal `k`-attractor is a `k`-approximation to the
  minimum `k`-attractor" (useless at `k=n`); and a **2.45-approximation for `k=3`** in `O(n)`
  expected time (`H(6) = 2.45`).
* **PROVED** (W25 Thm 13/14, read): the greedy online algorithm (`Lazy` = "the self-referencing,
  novel Lempel-Ziv factorization", W25 §2) is `O(log n)`-competitive, and "The approximation
  guarantee of a Lempel-Ziv-based compression algorithm for the string attractor problem is
  at most `Ω(log n)`". So `O(log n)` is attained *and tight for the LZ route* — see §4.
* **OPEN / UNVERIFIED**: a poly-time `o(log n)`- or `O(1)`-ratio algorithm for the full
  attractor? No source found states one; the `11809/11808` hardness only excludes ratios
  below `1.0000847`. KPRR18 says outright: "such a result is not known for `k`-attractors
  (the case `k=2` being the only one still open)" — the complexity of the **2-attractor** is
  OPEN.

## 2. The structure

**(a) The set-cover formulation (PROVED-by-definition).** Universe `U` = distinct nonempty
factors of `S`; for position `p`, `s_p = {f ∈ U : f has an occurrence covering p}`. Then `Γ`
is an attractor iff `⋃_{p∈Γ} s_p = U`. `|s_p| ≤ n(n+1)/2`, which is where `H(n(n+1)/2)` comes
from. KPRR18 replaces `U` by the edges of the `k`-truncated suffix tree —
**Lemma 11** (PROVED, read): "`Γ` is a `k`-attractor if and only if it is a suffix tree
`k`-marking" — so `|U| ≤ 2n−2`, and by Lemma 13 candidate positions collapse to
`|[1..n]/≡_k| ≤ min{n, σ^{2k-1}+2k-2}` classes: the trick behind Thm 33 being near-linear
for small `k`, `σ`.

**(b) What consecutive positions buy at a single `k`.** A factor occurring at `i` is covered
exactly by the `k` consecutive positions `[i, i+k)`, so each *occurrence* contributes one
interval. With one occurrence per factor the constraints are "pick a point in this interval" —
interval stabbing, solved exactly by the right-endpoint greedy (PROVED, folklore; the LP is
integral by the consecutive-ones property, MY-INFERENCE from Fulkerson–Gross TU).

**(c) What actually breaks it.** Two occurrences suffice: each constraint becomes a *union* of
equal-length intervals. Correction to the brief: it is **not** the union over all `k` that
destroys tractability — the problem is already NP-complete for one fixed constant `k ≥ 3`
(KP18 Thm 4.2). At `k=1` it is trivial (`γ_1 = σ`); at `k=2` the *sharp* variant is in P
(KPRR18 Thm 35, edge cover) while the `k=2` attractor is the open case. What `k=n` adds is a
`Θ(n²)`-element universe plus KP18's monotonicity gadget.

**(d) The integrality gap.** **OPEN** — no source I read states it for this family; the
`H(k(k+1)/2)` figure is greedy's guarantee, not the gap. A constant gap would give a
constant-factor algorithm, which the known hardness does **not** exclude (only ratios below
`1.0000847` are). Reductions from `k`-set cover do not transfer LP gaps. Measurable: C2.

**(e) `σ = 2`.** Every hardness reduction I read uses a growing alphabet: KP18's `Σ` has
`Θ(uk + t + t')` symbols; KPRR18 says "our reduction requires large alphabet" (sharp-`k`)
and "on large alphabets" (for `k`-attractor). Conversely hardness cannot survive fixed `k`
*and* fixed `σ`: KPRR18 Thm 29 gives exact minimum `k`-attractor in
`O(n) + exp(O(σ^k log σ^k))`, so with `σ=2` and constant `k` the exponential term is a
constant and **exact `γ_k` is computable in `O(n)` on binary strings for every fixed `k`**
(MY-INFERENCE from Thm 29 + Cor 7). Unknown: whether the **full** attractor (`k=n`) is NP-hard
on binary strings — no source asserting hardness or a polynomial algorithm for `σ=2` was
found, so treat it as **OPEN** (UNVERIFIED ABSENCE). What would settle it: a binary encoding of
KP18's gadgets (in particular the monotonicity gadget), or an algorithm exploiting
`d_k ≤ 2^k`.

## 3. Certified lower bounds beyond `δ`

| bound | statement | verdict | cost | tightness |
|---|---|---|---|---|
| `δ` | `δ ≤ γ` (KNP23 II.4) | PROVED, machine-checked here | `O(n)` (KNP23: "`δ` … can be computed in linear time") | `γ/δ = Θ(log(n/δ))` achievable (KNP23 III.3); Fibonacci `δ = γ = 2`, Thue–Morse `γ/δ → 1.2` (MY-COMPUTATION) |
| `σ` | `γ ≥ σ` (KP18 Ex 3.3) | PROVED | `O(n)` | tight on Fibonacci (`γ_1 = σ = γ = 2`) |
| packing | factors pairwise non-co-coverable `⇒ γ ≥ m` | PROVED (definition); the `0/1` part of the LP dual | exact = MIS on the co-coverability graph; `O(n)`-per-`k` sufficient version: unique `k`-mers at pairwise distance `≥ k` | **below `δ`** on Thue–Morse: `m ≤ 3 < δ → 10/3 < γ = 4` (MY-COMPUTATION) |
| LP dual | `y_f ≥ 0`, `Σ_{f ∋ p} y_f ≤ 1 ∀p ⇒ γ ≥ Σ_f y_f` | PROVED (weak duality) | `Θ(n²)` constraints; truncate to `O(n)` via KPRR18 Lemma 11 | unknown; needs a checkable rational dual |
| `γ_k` | `γ_k ≤ γ`, nondecreasing in `k`, `γ_n = γ` | PROVED (folklore) | `O(n)` per fixed `k` with `σ` fixed (Thm 29) | Thue–Morse `2,2,2,3,3,…` vs `γ=4`; Fibonacci `γ_1 = 2 = γ` (MY-COMPUTATION) |
| `z, r, g, 2b, e` | `γ ≤` these | PROVED (KP18 §3) | — | upper bounds only |

MY-COMPUTATION recipe (~40 lines, stdlib only): suffix automaton over `S`; per-state
end-position bitset propagated down suffix links; for each state and length
`L ∈ (len(link(v)), len(v)]` the coverage bitset `cov(L) = cov(L−1) | (endpos >> (L−1))`;
inclusion-minimal coverages; exact `γ` = min hitting set of those (branch on an unhit
coverage); packing = max family of pairwise disjoint coverages. Anchors: minimal coverages
count `8n−22` for `t_n`, `5 ≤ n ≤ 11`, matching TM26; `γ(t_n) = 4` for `4 ≤ n ≤ 8`, matching
KTMSIT20.

## 4. Falsifiable conjectures

**C1 — "the LZ construction is within a constant factor of `γ` on highly repetitive
corpora": REFUTED.** KTMSIT20: `z(t_n) = 2n` for the `n`-th Thue–Morse word (`|t_n| = 2^n`)
and `γ(t_n) = 4` (`n ≥ 4`), so `|Γ_LZ|/γ = log₂|t_n|/2`. W25 Thm 10: the LZ greedy marks `m`
positions on the `m`-th Fibonacci word `F_m` (`|F_m| ≈ φ^m`) and `γ(F_m) = 2` (BBGKM26), so the
ratio is `≈ 0.72 log₂ n` there too. *The experiment that settles it* is now a **regression
test**: `tools/approx` must reproduce `|Γ_LZ| = z = 2n` on `t_n` and `|Γ_LZ| = m` on `F_m`; a
bounded value would refute KTMSIT20/W25.

**C1′.** "On real repetitive corpora, `|Γ_LZ|/γ ≤ 4` and greedy is within `2γ`." Experiment:
run `tools/approx` (`|Γ_LZ|`, `/z`, `/δ`) against `tools/attractor`'s certified bracket on each
text; one text with an `LB`-certified ratio `> 4` refutes. The provable statement is
`4 log(n/γ)+4`, so C1′ asserts the `log` never bites on real data.

**C2 — "the LP integrality gap on this family is `O(1)`", sharply: `OPT_LP ≥ γ/2` for every
string.** Experiment: for all `2^n` binary strings, `n ≤ 12`, exact `γ` (min hitting set over
minimal coverages) and the LP optimum of §2(a) in exact rational arithmetic; repeat on `F_m`,
`t_n`, `a^n`. One string with `OPT_LP < γ/2` refutes; `n ≤ 12` settles only small scale, so
the portable form is the family statement.

**C3 — "the packing bound exceeds `δ` on some family": REFUTED on Thue–Morse**
(MY-COMPUTATION): the exact packing is `≤ 3` for `n ≤ 11`, while `δ(t_n) = 10/(3+2^{4-n}) →
3.33` for `n ≥ 6` (KTMSIT20), and `γ = 4`. Both certified bounds fall short of `γ` on the
canonical highly repetitive family, and `max(δ, packing) = δ` there. *Surviving, falsifiable
version* **C3′**: "`max(δ, packing) ≥ γ/1.25` on binary morphic words" (measured
`4/3.333 = 1.2` on `t_n`); one family with `γ > 1.25·max(δ, packing)` refutes it.

## 5. One page for the implementer

| construction | certified size | ratio vs `γ` | cost | source |
|---|---|---|---|---|
| LZ77 phrase ends | `z` | `4 log(n/γ) + 4` | `O(n)` parse + one verification pass | KP18 Lemma 3.7 + KNP23 II.2/II.4 |
| `k`-truncated set-cover greedy, `k=n` | `≤ H(n(n+1)/2)·γ` | `≤ 1 + 2ln(n/√2) ≈ 1.39 log₂ n + 0.3` | `O(n²)` expected | KPRR18 Thm 33 |
| same, `k` fixed | `≤ H(k(k+1)/2)·γ` | `≤ 1+2ln((k+1)/√2)`; `2.45` at `k=3` | `O(nk²)` expected | KPRR18 Thm 33 |
| minimal `k`-attractor | — | `k` | `O(n+σ^{2k-1}k²)` expected | KPRR18 Thm 30/31 |
| SLP (collage system) | `g` | worse: `g = O(δ log²(n/δ))` | grammar construction dominates | KP18 Thm 3.5 |
| BWT runs | `r` | worse: `r = O(δ log δ max(1, log(n/(δ log δ))))` | `O(n)` BWT | KP18 Thm 3.9 |

Build order, each step independently checkable: (1) **`z`-attractor** (Lemma 3.7, one
position per phrase end) — the baseline certificate `δ ≤ |Γ| ≤ z`, both ends cheap;
(2) **greedy set cover** on the KPRR18 Lemma-11 universe (suffix-tree edges): best proved
constant, seed for the anytime search; (3) **lower bounds** in this order — `δ`, `γ_k` for
small `k` (cheap, rarely above `δ`), packing, then an LP dual with a checkable rational
certificate; (4) **never** print a ratio not in the table. In particular `γ ≠ z` (Lemma 3.7
is an inequality, `γ/z → 0` on `t_n`) and no constant-factor claim is proved for any
construction.

For Lean, only two items are cheap: `IsAttractor T Γ → |Γ| ≤ z` given a parse (Lemma 3.7,
induction over phrase ends) and `γ_k ≤ γ` (immediate from the definition). Anything using
`z ≤ 4(δ log(n/δ)+δ)` is research-level (`space.md`). Side condition: `k ≥ 1` (the empty
factor has no covering occurrence).
