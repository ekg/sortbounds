# The space thread of compressed text indexing: is `r` the right measure?

Web-only note; no Lean file or sibling note touched. Tags: **PROVED** =
statement, direction and proof in a primary source I read; **OPEN** = source says
unknown; **FOLKLORE** = immediate from definitions; **UNVERIFIED** = could not read the
primary statement. `X = O(Y)`: *X cannot be much larger than Y*.

## 0. The prompt's labels are swapped against the literature

Kempa–Prezza (STOC'18) and everything after it uses **γ = size of the smallest
string attractor**, **δ = substring complexity** `max{d_k(S)/k : k ∈ [1..n]}`
(`d_k` = #distinct length-`k` substrings; KNP Def. II.1), plus `g` = smallest SLP,
`g_rl` = smallest run-length SLP, `z` = #LZ77 phrases, `b` = smallest bidirectional
macro scheme, `r` = #equal-letter runs in the BWT, `e` = #CDAWG nodes+edges, `v` =
lex-parse size. The question's labels are reversed: read `γ` where it says δ, and
`g` where it says γ.

## 1. The measure hierarchy

Attractor (Kempa–Prezza, doi:10.1145/3188745.3188814, arXiv:1710.10964), verbatim:
"A string attractor of a string T ∈ Σ^n is a set of γ positions Γ={j_1,…,j_γ} such
that every substring T[i..j] has an occurrence T[i′..j′]=T[i..j] with j_k ∈ [i′,j′],
for some j_k ∈ Γ."

**Proved, with direction:**

1. **δ ≤ γ** — PROVED, elementary. KNP Lemma II.4, proof verbatim: "Every length-k
   substring has an occurrence covering an attractor position, so there can be at
   most kγ distinct substrings of length k, that is, d_k(S)/k ≤ γ for all k ≤ n."
2. **γ ≤ z, r, g, c, 2b, e** — PROVED (Kempa–Prezza §3.1): an attractor of size
   `c` from any collage system of size `c` (Thm 3.5; an SLP is one, so γ ≤ g), `2b`
   from a macro scheme (Thm 3.6), `z` from LZ77 (Lemma 3.7), `e` from a CDAWG
   (Thm 3.10), and Thm 3.9 verbatim: "Let r be the number of equal-letter runs in the
   Burrows–Wheeler transform of T. Then, T has an attractor of size r". So γ
   lower-bounds all of them; Navarro's survey (ACM CSUR 54(2), 2021,
   doi:10.1145/3434399, arXiv:2004.02781, §3.9) puts it as
   `γ = O(min(b, c, z, z_no, r, g_rl, g))`.
3. **z = O(δ log(n/δ))** — PROVED, KNP Lemma II.2 (after Raskhodnikova et al.):
   "z ≤ 4(δ log(n/δ) + δ)", hence `γ, b, c = O(δ log(n/δ))`.
4. **g_rl = O(δ log(n/δ))**, **g = O(z log(n/z))** — PROVED (KNP §V; the second
   per survey §3.4), hence `g = O(δ log²(n/δ))`.
5. **r = O(δ log δ max(1, log(n/(δ log δ))))** — PROVED, Kempa–Kociumaka (FOCS'20,
   doi:10.1109/FOCS46700.2020.00097, arXiv:1910.10631), Thm 3.7 verbatim: "Every
   string of length n satisfies r = O(δ log δ max(1, log(n/(δ log δ))))"; likewise
   `r = O(z log z max(1, log(n/(z log z))))`, and `δ ≤ r` (used in KK Cor. 3.8).
6. **e = Ω(max(z,r)), e = Ω(g)** — PROVED; `e` is the weakest (survey §3.8).

**Separations:**

* **γ = Ω(δ log(n/δ))** — PROVED, KNP Thm III.3: "For every length n and integer
  value δ ∈ [2..n], there is a string S[1..n] with γ = Ω(δ log(n/δ))." With (3) this
  pins `δ ≤ γ ≤ z ≤ O(δ log(n/δ))`.
* **r exceeds δ by a log-squared factor** — PROVED, KK Thm 4.3: strings exist with
  `n = Θ(N)`, `δ = Θ(Δ)`, `r = Θ(min(n, δ log δ max(1, log(n/(δ log δ)))))` for every
  `N` and `Δ ∈ [1..N]`; at δ = n^ε, `r/δ = Θ(log n log log n)`.
* **r vs g**: binary de Bruijn sequences have `r = Θ(n)`, `g = O(n/log n)`, so
  `r = Ω(g log n)`. **r vs z**: even Fibonacci words have `r = O(1)`,
  `z = Θ(log n)`, so `z = Ω(r log n)` (both survey §3.6).
* **g vs g_rl** — PROVED, KNP Cor. V.1: `g = Ω(δ log²(n/δ)/log log(n/δ))` while
  `g_rl = O(δ log(n/δ))`.

**Is `r` comparable to γ/z?** One-directional only. `r` is always within a polylog of
`z` and of `γ` (item 5), and that is tight (KK Thm 4.3); but on other families
`z = Ω(r log n)` (even Fibonacci words) and `r = Ω(g log n)` (de Bruijn). `r` is also the one measure that supports fast
searching without access (survey §3.12) and is not reversal-invariant.

## 2. Is `O(r)` space optimal?

**No lower bound stated in terms of `r` was found** (arXiv listings, KNP, KK, the
r-index papers, the survey). What exists:

* **Index-space lower bounds are stated in δ.** KNP Thm IV.5 (PROVED): string families
  of common measure δ exist "that need Ω(δ log(n/δ) log n) bits to be encoded". Any
  index is such an encoding, so this binds indexes; KNP §VII: "o(δ log n) space is
  unreachable in general".
* **The σ-refined optimum.** KNP Thm VI.6 gives a block tree of
  `O(δ log(n log σ/(δ log n)))` words; Kociumaka–Navarro–Olivares (Algorithmica 86,
  2024, arXiv:2206.00781) call exactly that "the optimal O(δ log(n log σ/(δ log n)))
  space". The matching lower bound `Ω(δ log(n log σ/(δ log n)) log n)` bits is
  attributed to KNP's TIT version by Nishimoto–Tabei (arXiv:2604.24080, §1) —
  **UNVERIFIED**: only KNP arXiv v2 is open access and its Thm IV.5 has no σ.
* **Measure lower bounds ≠ index lower bounds.** `γ = Ω(δ log(n/δ))` and KK Thm 4.3
  compare two *measures*; they say nothing about data structure space. The only
  index-space bound in this family is the δ one.

**Consequence**: the r-index is `O(r)` words = `O(r log n)` bits with
`r = O(δ log δ max(1, log(n/(δ log δ))))`, i.e. within a `polylog(n)` factor of the
δ-optimal space (a `log² n`-scale gap). Nothing known rules out an index of `o(r)`
space, and no source claims `O(r)` is optimal: **OPEN**.

## 3. Is an `O(γ)`- or `O(δ)`-space index with fast queries possible?

Space in words; `m` pattern length, `occ` output size.

* **r-index** (Gagie–Navarro–Prezza, JACM 67, 2020, doi:10.1145/3375890;
  arXiv:1705.10382, 1809.02792): `O(r)` words, count `O(m log log_w(σ+n/r))`, locate
  `+ occ log log_w(n/r)`; with `O(r log log_w(σ+n/r))` words: `O(m)` count,
  `O(m+occ)` locate.
* **Attractor/δ indexes** (Christiansen–Ettienne–Kociumaka–Navarro–Prezza, TALG 17,
  2021, doi:10.1145/3426473, arXiv:1811.12779): `O(γ log(n/γ))` words, count
  `O(m+log^{2+ε}n)`, locate `O(m+(occ+1)log^ε n)`; an extra `log^ε n` (resp. `log n`)
  factor buys optimal locate `O(m+occ)` (resp. count `O(m)`).
* **δ-optimal** (Kociumaka–Navarro–Olivares, Algorithmica 86, 2024, arXiv:2206.00781):
  `O(δ log(n log σ/(δ log n)))` words, same near-optimal times; a sublog resp. log
  factor buys `O(m+occ)` resp. `O(m)` count.
* **Grammar only** (Claude–Navarro–Pacheco, arXiv:2004.01032): `O(G lg n)` bits,
  `O((m²+occ) lg G)` locate, quadratic in `m`.

Open problems, as stated:

1. **Reachability of γ** — KNP abstract: "it is unknown if one can always represent a
   string in `o(γ log n)` space"; §VII: "no string family is known to require `ω(γ)`
   space, nor it is known if `o(γ log n)` space can always be reached". **OPEN.** (γ is
   NP-hard to compute and non-monotone.)
2. **Search time in δ-optimal space** — KNO, verbatim: "the near-optimal search time
   `O(m+(occ+1)log^ε n)` has been achieved only within `O(γ log(n/γ))` space. … The
   question of whether the better search time could be supported within the δ-optimal
   space remained open." They settled it. **PROVED (2024)**; open only in the residual
   `log^ε n`/`log` factors, i.e. `O(m+occ)` in exactly optimal space.

An `O(γ log(n/γ))`-space index with `O(m + occ·polylog)` queries is known; `O(γ)`
space with polylog queries is **OPEN**.

## 4. The alphabet term

**(a) σ as an additive space term — unnecessary.** `σ ≤ min(γ,r)`: Kempa–Prezza Ex.
3.3, "any attractor Γ must satisfy |Γ| ≥ σ"; the r-index paper writes "`σ ≤ r` is the
alphabet size of T" (arXiv:1809.02792 §4). Reason (FOLKLORE): every run is one symbol
and all σ symbols occur, so `σ ≤ r`; distinct symbols need distinct attractor
positions. Hence `O(σ + f(r)) = O(f(r))`, `O(σ + f(γ)) = O(f(γ))`; no structure here
has a σ-only term, and σ never multiplies a measure — the bounds are `γ log(n/γ)`,
`δ log(n log σ/(δ log n))`, `r`, `r log log_w(σ+n/r)`.

**(b) σ inside the log — three appearances.**

* r-index: σ is only the universe size of the range-predecessor structure —
  `O(m log log_w(σ+n/r))` time, `O(r log log_w(σ+n/r))` space in the optimal-locate
  variant. Since `σ ≤ r`, the live regime is `σ < n/r`, where it collapses to
  `log log_w(n/r)`.
* δ-optimal space: `δ log(n log σ/(δ log n)) = δ(log(n/δ) − log(log n/log σ))` —
  "subtract `log log_σ n`", the number of symbols a word holds. For `σ = O(1)` this
  is `Θ(log(n/δ))`: a lower-order correction, never a factor.
* packed variants: `O(r w log_σ log_w(σ+n/r))`.

Genuinely σ-dependent bounds are statistical (`n H_k + o(n log σ)` bits), a family
blind to repetitiveness.

## 5. What is formalizable in Lean

**Elementary, definitions-heavy.** The engine of the hierarchy is the `d_k ≤ kγ` count,
a `Finset.card_le_card` injection. Repository style (`AGENTS.md`): hypothesis
statements (`IsAttractor T Γ → …`) instead of an `sInf`-defined minimum, plus a
non-vacuity witness.

**Moderate, one construction each.** KNP Lemma III.2 / Thm III.3: for `S_n` = `b` at
powers of two, `δ(S_n) ≤ 2` and `γ(S_n) ≥ ½⌊log n⌋`, via uniqueness of `b a^{2^j−1} b`
and disjointness of the intervals `[2^j, 2^{j+1}]` for even `j` — elementary, but a
slog. KP Lemma 3.7 (LZ77 → attractor of size `z`) is comparable given an LZ77 parse.

**Research-level, do not start.** `γ ≤ g` (collage-system induction on nonterminals);
`γ ≤ r` / `δ ≤ r` (KP Thm 3.9 needs BWT, runs, LF-mapping, inversion termination); KNP
Thm IV.5 (a model of "any encoding" plus counting a family); `z = O(δ log(n/δ))`,
`g = O(z log(n/z))`, `r = O(δ log² n)`, and every separation of §1 beyond
powers-of-two.

**Unverified**: (i) the σ-refined δ lower bound (TIT, paywalled) — the TIT PDF would
settle it; (ii) any index-space lower bound in terms of `r` — found none: absence of
evidence, not a theorem; (iii) the one-line proofs of `σ ≤ r`, `γ ≥ σ` are mine,
not quoted.

## Candidates for formalization, in order of tractability

1. `alphabet_card_le_attractorCard : IsAttractor T Γ → T.toFinset.card ≤ Γ.card`
   (γ ≥ σ); needs `IsAttractor` on `List α`, positions as `Finset ℕ`.
2. `substring_card_le_of_isAttractor : IsAttractor T Γ →
   (substringsOfLen T k).card ≤ k * Γ.card` — needs `substringsOfLen : List α → ℕ →
   Finset (List α)` and the "an occurrence covering one position has one of `k`
   offsets" injection. This is all of **δ ≤ γ**.
3. `delta_le_attractorCard`, the `∀ k` form of (2), skipping maxima entirely.
4. `alphabet_card_le_runs : T.toFinset.card ≤ bwtRuns T` (σ ≤ r) — needs a BWT
   definition, far cheaper than attractors-from-runs; checks §4(a).
5. `attractorCard_pow2_ge : IsAttractor (S n) Γ → Nat.log 2 n / 2 ≤ Γ.card` — the KNP
   Thm III.3 lower bound, in "every attractor is large" form.
6. `attractorCard_le_phraseCount` (KP Lemma 3.7), then `attractorCard_le_slpSize`
   (KP Thm 3.5, SLPs as collage systems).
7. KNP Lemma IV.2's encoding bound via this repo's `card_le_pow` machinery:
   `2^bits ≥ (family).card` for the perturbed powers-of-two family — the only
   elementary *space* lower bound.
