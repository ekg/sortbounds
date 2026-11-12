# T4 — Fast queries at **grammar** and **attractor** space

The small-space end of the frontier: with `δ ≤ γ = O(r)` and `O(m)`/`O(m+occ)`
queries at `O(r)` words, what survives at `O(γ)` and `O(δ)`?

Labels: **PROVED** = quoted theorem, **OPEN** = quoted open question,
**MY-INFERENCE** = my reading, **UNVERIFIED** = unchecked. Space is in words
(`log n` bits) unless a bound says "bits".

## 0. The measure chain, and one correction to the brief

**PROVED** `δ ≤ γ ≤ b ≤ c ≤ z ≤ grl ≤ g` (Kociumaka–Navarro–Prezza,
*IEEE Trans. Inf. Theory* 2023, §VII: "all the intermediate measures,
δ ≤ γ ≤ b ≤ c ≤ z ≤ grl ≤ g"; and "Lemma II.4 ([27, Lemma 5.6]). Every string S
satisfies δ ≤ γ").

The brief writes `δ ≤ γ ≤ r`; `r` (BWT runs) is **not** in that chain. Only, up to
constants: **PROVED** `γ = O(min(b, c, z, z_no, r, grl, g))` (Kempa–Prezza STOC
2018, quoted in Navarro, *ACM CSUR* 2021, §3.9). So "`O(γ)` space" is an
*optimisation over the r-index*, not something `γ = O(r)` gives.

Two facts fix the floor:

- **PROVED** δ is a reachable, tight space measure: "there are string families
  needing `Ω(δ log(n/δ))` space to be encoded, so this space is optimal for every
  `n` and `δ`" (KNP 2023, abstract); in bits, `Ω(δ log(n/δ) log n)`.
- **OPEN** for `γ`: "we do not know if it is reachable, that is, if we can
  represent S within space `O(γ)`"; "`o(δ log n)` space is unreachable in general,
  whereas it is unknown if `o(γ log n)` space can always be reached" (Navarro CSUR
  2021, §3.9–3.10).

So the smallest index space anyone can name is `O(δ log(n log σ/(δ log n)))` words
— **δ-optimal space**. At `δ` the open quantity is therefore **time**; at `γ` both.

## 1. The table

`g`/`G`: sum of right-hand-side lengths of a grammar (per paper). `er(T)`:
right-extensions of maximal repeats. `ra(m)`: grammar random access time for `P`.

| Structure | Space | Count | Locate | Citation |
|---|---|---|---|---|
| Grammar index, first log-in-grammar bound | `O(N lg u)` bits | — | `O((m²/ε)lg(lg u/lg n) + occ lg n)` | Claude–Navarro, *Improved Grammar-Based Compressed Indexes*, arXiv:1110.4493 |
| Grammar index | `O(G lg n)` bits | — | `O((m²+occ) lg G)` | Claude–Navarro–Pacheco, *JCSS* 2020, arXiv:2004.01032 |
| SLP+LZ77 grid index | `O(r + z lg lg n)` | — | `O(m² + occ lg lg n)`; `O(m log m)` Monte Carlo if SLP balanced | Gagie–Gawrychowski–Kärkkäinen–Nekrich–Puglisi, arXiv:1109.3954 |
| Lyndon-SLP index | `O(g)` | — | `O(m + lg m lg n + occ lg g)` | Tsuruta–Köppl–Nakashima–Inenaga–Bannai–Takeda, arXiv:2004.05309 |
| Grammar index, induced suffix sorting | `O(g)` | — | `O(m lg|S| + occ_C lg|S| lg n + occ)` | Akagi–Köppl–Nakashima–Inenaga–Bannai–Takeda, SPIRE 2021, arXiv:2105.13744 |
| CDAWG index on grammar-compressed `T` | `O(er(T))` | — | `O(ra(m) + occ)` | Cleary–Winjum–Dood–Inenaga, arXiv:2407.08826 |
| Counting on grammars | `O(g)` | `O(m log^{2+ε} n)` | — | CEKNP *TALG* 2021 (arXiv:1811.12779); run-length: Navarro–Pacheco, CPM 2024 (arXiv:2406.00221), solving their open problem |
| Universal attractor index | `O(γ log(n/γ))` | — | `O(m log n + occ log^ε n)` | Navarro–Prezza, *JCSS* 2020, arXiv:1803.09520 |
| LCP-grammar (γ) index | `O(γ log(n/γ))` | `O(m + log^{2+ε} n)` | `O(m + (occ+1) log^ε n)` | Christiansen–Ettienne–Kociumaka–Navarro–Prezza, *TALG* 2021, arXiv:1811.12779 |
| same, `×log^ε n` / `×log n` space | `O(γ log(n/γ) log^ε n)` / `… log n` | `O(m)` (latter) | `O(m+occ)` (former) | ibid. |
| δ-index | `O(δ log(n log σ/(δ log n)))` | — | `O(m log n + occ log^ε n)` | Kociumaka–Navarro–Prezza, *IEEE TIT* 2023, arXiv:1910.02151 |
| δ-index, near-optimal time | `O(δ log(n log σ/(δ log n)))` | `O(m + log^{2+ε} n)` | `O(m + (occ+1) log^ε n)` | Kociumaka–Navarro–Olivares, *Algorithmica* 2023, arXiv:2206.00781 |
| δ-SA, δ-LCE | `O(δ log(n log σ/(δ log n)))` | SA / SA⁻¹ / LCE in `O(log^{4+ε} n)` | — | Kempa–Kociumaka, FOCS 2023, arXiv:2308.03635 |
| δ-index, streaming construction | `O(δ log(n/δ))` | — | `O(m + (occ+1) log^ε n)` | Kosolobov, CPM 2026, arXiv:2602.13735 |
| Dynamic RR-index (δ-optimal) | δ-optimal *bits*, expected | — | `O(m + log m log² n + occ·log n/loglog n)` expected | Nishimoto–Tabei, arXiv:2604.24080 |
| r-index | `O(r)` | `O(m)` | `O(m+occ)` | OptBWTR: Nishimoto–Tabei, ICALP 2021, arXiv:2006.05104; Gagie–Navarro–Prezza, J. ACM 2020, arXiv:1705.10382 |

## 2. Grammar (SLP) side, in order

The SLP timeline is one story about **primary/secondary occurrences**: enumerate
nonterminal occurrences in right-hand sides (a grid), follow parent pointers; cost
`= (partitions of P) × (grid query) + occ`. Claude–Navarro 2012 fixes "partitions"
at `O(m²)` and pays `log` per occurrence; Claude–Navarro–Pacheco 2020 removes the
`log u`, still `O(m²)`; Gagie et al. 2014 drop occurrence cost to `log log n`,
reaching `O(m log m)` only for balanced SLPs *and* a faulty index. Locally
consistent parsing removes `m²` — it "requires one to test only `O(log m)`
partitions of `P`" (survey §7.1) — but parses a run-length grammar of size
`O(γ log(n/γ))` rather than the given `g`.
Honest grammar row: at a *given* grammar's space the best per-character behaviour
is `O(m)` plus a `log g`/`log n` correction (Lyndon SLPs), counting is
`O(m log^{2+ε} n)`, and **no published index gives `O(m + log n)` locate at `O(g)`
space**. No source found for the brief's "Bille–Gørtz–Landau–Weimann" index (§7).

## 3. Attractor/δ side, in order

`O(γ)` space is not reachable; `O(γ log(n/γ))` is, and buys
`O(m + (occ+1) log^ε n)` locate / `O(m + log^{2+ε} n)` count. Kociumaka–Navarro–
Olivares 2023 gave the *same* times in the *smaller* δ-optimal space, answering
"whether the better search time could be supported within the δ-optimal space".
There too: SA/LCE in polylog time (Kempa–Kociumaka FOCS 2023), streaming
construction (Kosolobov 2026). **MY-INFERENCE**: via the δ-SA + LCE, pattern
matching is available there in `O((m+occ) log^{5+ε} n)` — worse in `m` than KNO's,
so not cited as state of the art.

## 4. The gap, in one line per row

- **`O(r)`**: frontier — count `O(m)`, locate `O(m+occ)`, optimal. Pay nothing.
- **`O(γ log(n/γ))`**: pay `log^ε n` **per occurrence** and an additive
  `log^{2+ε} n` (count) to sit a log factor below `r` — plus `log^ε n`/`log n` in
  *space* to buy back optimal `occ`/`m` terms.
- **`O(γ)`**: no index exists; even the *representation* is open. Price: unknown.
- **δ-optimal**: same time as the γ row, provably optimal space; the whole price
  of the space saving is `log^ε n` per occurrence — the only quantitatively clean
  "price of space" in the hierarchy.
- **`O(grl)`** (grammar, run-length): space `⊆ O(δ log(n/δ))`, i.e. *the same
  asymptotic space* as the δ row, but time `O(m log n + occ log^ε n)` — you pay
  **`log n` per pattern character** for being handed a grammar rather than a
  locally consistent parse.
- **`O(g)`** (plain SLP): space up to `Θ(log n/log log n)` larger than the smallest
  RLSLP (KNP 2023); best times still carry a `log g`/`log n` term.

## 5. What would be needed, and what has been conjectured

One explicit statement of the target:
**OPEN** "An important open question is whether this final gap can be closed: can
we search or count in optimal time within δ-optimal space, `O(δ log(n/δ) log σ/(log n))`?
With our best results, space or time must be multiplied by `O(log^ε n)` or `O(log n)`"
(KNO 2023, §VII).

Sharpest change since 2023 — what is now *proved impossible* in δ-ish space:
**PROVED** SA, SA⁻¹, LCP, LCE "all require `Ω(log n/log log n)` time within
`O(δ(T) log^{O(1)} n)` space", and BWT, PLCP, LF, inverse LF, Φ, Φ⁻¹ "require
`Ω(log log n)` time", both "matching known upper bounds", even on binary
alphabets (Kempa–Kociumaka, SODA 2026, arXiv:2510.19820). So a
`O(δ polylog n)`-space structure with `polylog`-time per-character queries **does
exist and is optimal** for those queries; pattern-matching count/locate is not
covered (**MY-INFERENCE**), so its `log^ε n`-per-occurrence term stays open.

Grammar side: **PROVED** `Ω(log N/log log N)` random access for RePair, Greedy,
LongestMatch, Sequential, Bisection "within space `O(n polylog N)`" and
`Ω(log log N)` for LZ78, all matching upper bounds (De–Kempa, SODA 2023,
arXiv:2307.08833); a trade-off curve in structure size `M` with "a matching
unconditional lower bound" in almost all regimes (Duyster–Kociumaka, ICALP 2026,
arXiv:2602.10864); BMM/OV-conditional bounds for rank and symbol-occurrence
queries on SLP text (De–Kempa, ESA 2026, arXiv:2607.07366). None concerns pattern
matching, and **no one states a conjecture on the achievable (space, time)
trade-off for γ- or δ-space pattern matching** beyond KNO's question.

## 6. Formalizable pieces

- **Formalizable (accounting over explicit definitions).** `δ ≤ γ` is a pigeonhole
  on distinct substrings; `γ = O(b)` and the other ratios are reductions between
  explicit parsings; KNP's lower-bound families are witness strings plus a
  counting argument; every *query-time bound given a structure* (grid + range
  counting, parent-pointer reporting, block-tree access) is amortised accounting.
- **Not formalizable at reasonable cost.** Locally consistent parsing with
  Karp–Rabin fingerprints, recompression (Jeż 2015), the δ-SA: deep results with
  randomised construction and delicate collision analysis; the lower bounds are
  communication-complexity / BMM-conditional. A Lean lane should stop at the
  hierarchy and at "given this structure, this cost bound holds" — thread S's split.

## 7. Unverified / discrepancies

- **UNVERIFIED**: an SLP text index by Bille–Gørtz–Landau–Weimann. arXiv shows
  only Bille–Landau–Raman–Sadakane–Satti–Weimann (random access, `O(log N)` time,
  `O(n)` space, arXiv:1001.1565) and Bille–Christiansen–Cording–Gørtz (finger
  search, arXiv:1507.02853). Likely a garbled reference; I cite the verified lineage.
- **Units conflict**: arXiv:2604.24080 gives δ-optimal space "in bits" while
  KNP/KNO/KK give the same formula in words and KNP's lower bound is in bits. I
  read the formula as words; the 2026 wording is probably a slip.
- arXiv:1910.02151's abstract page is truncated ("…we can not only…"); I quoted
  its PDF (v3, 15 Jan 2021). 2025–2026 items are quoted from abstracts only.
