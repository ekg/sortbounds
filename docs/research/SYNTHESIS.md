# Synthesis: is the r-index optimal? (space and time)

Answers below are grounded in `docs/research/{space,time-*}.md`, which quote primary
sources. Verdicts: **PROVED** (theorem in a paper), **OPEN**, **UNVERIFIED** (quoted
second-hand, flagged in the brief).

## The one-line answer

**Time: yes, up to a `log log` factor that space can buy back. Space: no — `r` is not
the right measure, and no lower bound is known in terms of `r`, so "optimal" is
unproven in that direction either way.**

## Space

### `r` is not the right measure — PROVED, and it is tight

* `r = O(δ log δ · max(1, log(n/(δ log δ))))` (Kempa–Kociumaka, FOCS'20, Thm 3.7),
  **and Thm 4.3 shows the bound is tight**: there are strings with
  `r/δ = Θ(log n log log n)` (at `δ = n^ε`).
* So an `O(r)`-space index can be a `Θ(log n log log n)` factor larger than necessary.
  The r-index is **not** space-optimal, and `r` is not a proxy for `δ`.
* Hierarchy (Kempa–Prezza Thm 3.5–3.9): `γ ≤ min(z, r, g, c, b, e)` — in particular
  "T has an attractor of size r", so `δ ≤ r` always.

### `δ` is the floor, and `σ` is not an order

* Space is ordered by `δ`, not by the alphabet: the δ-optimal space is
  `O(δ log(n log σ/(δ log n)))` **words** (KNP, IEEE TIT 2023, Thm VI.6). The `σ` sits
  **inside a log**, with a `log log n` denominator — it is not an additive term and not
  the order of the bound. (`σ ≤ r` and `γ ≥ σ` are elementary.)
* Encoding lower bound: `Ω(δ log(n/δ) log n)` bits (KNP Thm IV.5) — so `δ` is minimal
  up to polylog among these measures. (`σ`-refined version quoted only second-hand:
  UNVERIFIED.)

### "Can we have `O(γ)`/`O(δ)` space *and* fast queries?" — essentially yes

* **δ-optimal, near-optimal time** (Kociumaka–Navarro–Olivares, Algorithmica 2024):
  `O(δ log(n log σ/(δ log n)))` words with count `O(m + log^{2+ε} n)`, locate
  `O(m + (occ+1) log^ε n)`; **an extra `log^ε n` factor of space buys `O(m+occ)`
  locate, an extra `log n` buys `O(m)` count.**
* Grammar-based: `O(γ log(n/γ))` words, count `O(m + log^{2+ε} n)` (Christiansen et al.,
  TALG 2021); grammar-only is much worse (`O((m²+occ) log G)`, quadratic in `m`).
* **Still OPEN**: "reachability of γ" — whether `o(γ log n)` space is always achievable
  (KNP §VII: no family is known to require `ω(γ)` space, and `o(γ log n)` is not known
  to suffice).

### Space lower bounds: the honest position

* **No** lower bound phrased in terms of `r` exists — not in the r-index papers, KK,
  KNP, or Navarro's survey. Reported as absence of evidence, not a theorem.
* The one strong classical bound, **Demaine–López-Ortiz (J. Algorithms 2003, Thm 2.1)**:
  *"If I is an index supporting a search for the substring P in S(|P|,|T|) = O(|P|) bit
  probes **to the text T**, then |I| = Ω(|T|)."* — a bit-probe model in which the text
  is stored verbatim. **The r-index stores no text**, so the bound does not apply. That
  is precisely why a self-index can be both fast and small, and it means nobody has a
  lower bound covering self-indexes.
* Gál–Miltersen state the obstruction in their own words: *"We don't know how to prove
  similar lower bounds for natural storage and retrieval problems such as Substring
  Search"* — their proofs run through an error-correcting-code property, which substring
  search lacks because occurrences overlap.

## Time

### The frontier (space in words; `m` pattern length, `occ` output size)

| space | count | locate | status |
| --- | --- | --- | --- |
| `O(r)` (r-index, GNP'20) | `O(m log log_w(σ + n/r))` | `+ occ·log log_w(n/r)` | PROVED |
| `O(r)` (OptBWTR, NT'21 Thm 9) | `O(m log log_w σ)` | `O(m log log_w σ + occ)` | PROVED |
| `O(r log(n/r))` (GNP Thm 9 + Thm 3) | **`O(m)`** | **`O(m+occ)`** | PROVED |
| `O(δ log(n log σ/(δ log n)))` (KNO'24) | `O(m + log^{2+ε} n)` | `O(m + (occ+1) log^ε n)` | PROVED |

**Correction to an earlier draft of this file** (and to what I had said verbally): at
`O(r)` space there is **no unconditional `O(m)` count**. OptBWTR gives
`O(m log log_w σ)`, and `O(m)` follows only under `σ = O(polylog n)`. Unconditional
`O(m)` count / `O(m+occ)` locate costs **`O(r log(n/r))` words** — a `log(n/r)` factor of
space. That is the precise trade, and it is a good one: at `r/n ≈ 1/488`, `log₂(n/r) ≈ 9`.

Two lessons: (i) what space buys is the `log log` factor, not an asymptotic class —
`log(n/r)` extra space removes it; (ii) the small-space (`δ`) end is within polylog of the
large-space end, so "compressed versus fast" is not the dichotomy it sounds like.

*Discrepancy recorded, not resolved:* `space.md` quotes "`O(r log log_w(σ+n/r))` words ⇒
`O(m)` count" from GNP; `time-1` ties the unconditional `O(m)` row to `O(r log(n/r))`
words. `log log_w(σ+n/r) ≤ log(n/r)`, so the first is the stronger claim; we use the
second (primary, GNP Thm 9/Thm 3) and mark the first UNVERIFIED pending the paper text.

### How to get faster, concretely

1. **Move structures** (Nishimoto–Tabei 2021; Move-r, SEA 2024): the `move` operation
   replaces rank/select round-trips; Move-r reports 2–35× (typically 15×) faster locate
   at 0.8–2.5× (typically 2×) the space — a *trade*, not free speed.
2. **Spend space on the `log log`**: `O(r log(n/r))` or `O(r log log(·))` for `O(m)`.
3. **Go to δ-space with near-optimal time** (KNO 2024) if `r ≫ δ`.
4. **Engineering**: sr-index (1.5–4× less space at the same speed); Movi (cache-miss
   minimisation, prefetching, "up to 30× faster backward search"); measured r-index:
   13.1 MiB index for 629 MB of DNA (`r = 1.29 M`), 8.03 µs/count, 0.149 µs/occ.
5. **Construction is usually the bill**: 103 s and 534 MiB to build that index ⇒ ≈7·10⁸
   reported occurrences before it amortises. For most workloads this dominates query
   time, and it is where the engineering effort actually goes (ropebwt3: 20.5 h for
   ~600 Gb).

## What this repository could formalize (and what it could not)

Grounded candidates, in order of tractability:

1. **The counting core of `δ ≤ γ`** — KNP's verbatim proof: *"Every length-k substring
   has an occurrence covering an attractor position, so there can be at most kγ distinct
   substrings of length k, that is, d_k(S)/k ≤ γ for all k ≤ n."* Definitions: string
   attractor, `d_k`, SLP size. Statements: `d_k(S) ≤ k·|Γ|` for any attractor; the same
   for a grammar; hence `δ ≤ γ` once the characterization `δ = max_k d_k/k` is in hand.
2. **`σ ≤ r`, `γ ≥ σ`** — elementary, quoted facts, one-line proofs.
3. **Demaine–López-Ortiz Thm 2.1** — a bit-probe adversary argument, the *space* dual of
   this repository's time bounds: fast search into the text ⇒ text-sized index. This is
   the one lower bound in the area that is both strong and formalizable in spirit.
4. **Not** formalizable here: KK Thm 3.7 (the `r = O(δ log …)` bound, deep), the
   `γ = Ω(δ log(n/δ))` separations (explicit string families), and anything about
   cell-probe trade-offs.

## The three lower bounds that would settle it (from `time-3`)

1. A parameterised cell-probe bound for count/locate in `O(r)` space, e.g. `S·t = Ω(r·m)`
   — would be the first cell-probe bound in a *data-dependent parameter*; hard because
   small `r` is low-entropy and every existing technique is fuelled by incompressibility.
2. `Ω(r)` words for `O(m + occ)` locate — must defeat all index families, not just
   BWT-based ones.
3. A non-systematic lower bound for exact substring search — the Gál–Miltersen gap.
