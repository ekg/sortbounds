# Space–time trade-offs for compressed text indexes

`T[1..n]`, alphabet `[1..σ]`, `r` = BWT runs, `m` = pattern length, `occ` = occurrences,
`w = Θ(log n)`. Space in **words** unless "bits". Labels: **PROVED** = unconditional theorem;
**CONDITIONAL** = from a hardness conjecture; **FOLKLORE** = no citable theorem found;
**OPEN**; **UNVERIFIED** = source not read by me.

## 1. Explicit knobs

| # | Knob | Space cost | Time saved | First paper |
|---|---|---|---|---|
| K1 | SA/PLCP sampling stride `s` | `O(n/s)` words beyond the index, `O((n log n)/s)` bits | locate `O(s)` per occurrence | Kärkkäinen–Ukkonen, sparse suffix trees, ISAAC 1996 (FOLKLORE; via Navarro §5.5.2, formula in GNP §2) |
| K2 | Sampling in the repetitive setting (`rlfm-index`) | `O(r + n/s)` words | locate `O((m + s·occ)(log σ/log log r + (log log n)²))` | Mäkinen et al., JCB 2010 (table in Nishimoto–Tabei) |
| K3 | **r-index parameter `s`** (sampling inside the run structure) | `O(r s)` words | per-occurrence `O(1 + log log_w(n/r)/s)` (`O(1)` at `s = log log_w(n/r)`) | Gagie–Navarro–Prezza (GNP), JACM 2020, Thm 1 |
| K4 | **Subsampling the `r` samples** (`sr-index`) | `O(r)` + `min(r, 2⌈n/(s+1)⌉)·2 log n` bits | *negative* knob: time × `s`; buys space, not time | Cobas–Gagie–Navarro, CPM 2021 / ACM 2024, Thm 4.5 |
| K5 | **Dense `move` structure** (store `φ`/`LF` pairs per run, no predecessor queries) | `≈ 2r log n` bits (`O(r)` words) | `LF`, `φ`, `φ⁻¹` in `O(1)`; locate `O(m log log_w σ + occ)` | Nishimoto–Tabei, ICALP 2021 (OptBWTR) |
| K6 | **Sparse bitvector** alternative (bitvectors + predecessor) | `O(r log(n/r))` bits — `log r` factor *less* than K5 | `O(log log_w(σ + n/r))` per predecessor, not `O(1)` | r-index (GNP 2020); gap quantified by Brown–Langmead 2026 §3.3 |
| K7 | **Blocked / two-level** structures | `O(r)` words per level, `O(r log(n/r))` total | text/SA/ISA/LCP access `O(log(n/r))` instead of loglog | GNP 2020, Thm 2, §6.2–6.4 (levels `sᵢ = n/(r·2^{i−1})`) |
| K8 | Indexing all `log(n/r)`-mers (trie / z-fast trie) | `O(r log(n/r))` words; packed `O(r w log_σ(n/r))` | count `O(m)`, locate `O(m + occ)`; packed `O(m log σ/w + occ)` | GNP 2020, Thms 3–4, 9–10 |
| K9 | σ-dependent tables | `+σ` bits (`C[]`, `Ψ′` intervals); `log_σ` factor when packed | `Ψ′` search / rank in `O(log r_a)` | RLCSA; Brown et al. 2024 give `O(r log(n/r) + r log σ + σ)` bits |
| K10 | LCE structure | `O(n)` bits, σ-independent | `O(1)` LCE | Kempa–Kociumaka, STOC 2019 (`O(n/log n)` words); r-space composition UNVERIFIED |
| K11 | LCP access / sampling | `O(r s)` words sampled, `O(r log(n/r))` full | `LCP[p±i]` in `O(log log_w(n/r)+s′)`; `ℓ` cells in `O(log(n/r)+ℓ)` | GNP 2020, Lemma 5, Thm 7 |

Corrections: (a) `O(r + n/s)` is the *rlfm-index*'s bound: the r-index samples only the `r`
run-end positions, so that knob becomes `min(r, n/s)` (K4). (b) The r-index's own `s` (K3)
costs `r·s` — it *multiplies* `r`.

## 2. The Pareto frontier, `O(r) → O(n)`

The frontier is a **set of points**, not a curve: count/locate are not monotone in space
across families. Rows ordered by space for a given `r`.

| Space | Count | Locate | Ref |
|---|---|---|---|
| `O(r)` words (dense move, K5) | `O(m log log_w σ)` | `O(m log log_w σ + occ)` | N–T 2021, Thm 9 |
| `O(r)` words (r-index, K6) | `O(m log log_w(σ + n/r))` | `+ occ·log log_w(n/r)` | GNP 2020, Thm 1 |
| `O(r s)` words | `O(m log log_w(σ + n/r))` | `occ·(1 + log log_w(n/r)/s)` | GNP 2020, Thm 1 |
| `O(r + min(r, n/s) log n)` bits | — | `O((m + s·occ) log(σ + n/r))` | sr-index, Thm 4.5 |
| `O(r + n/s)` words | as `O(r)` | `O((m + s·occ)(log σ/log log r + (log log n)²))` | rlfm |
| `O(r log(n/r))` words | `O(m)` | `O(m + occ)` | GNP 2020, Thms 3, 9 |
| `O(r w log_σ(n/r))` words (packed) | `O(m log σ/w)` | `O(m log σ/w + occ)` | GNP 2020, Thms 4, 10 |
| `n H_k + o(n log σ)` bits + `n/s` samples | `O(m log log_w σ)` | `O(m + s·occ)` | FM-index, per GNP 2020 §2 |
| `O(δ log(n/δ) log n/log σ)`, `δ ≤ r` | SA/ISA access `O(log^{4+ε} n)` per cell | ⇒ polylog count/locate (**UNVERIFIED** as stated) | Kempa–Kociumaka, STOC 2024 (δ-SA) |

Verbatim: GNP Thm 1 — "we can store a text … in `O(rs)` words … and (after counting) report
their `occ` locations in overall time `O((1+ log log_w(n/r)/s)·occ)`". sr-index Thm 4.5 —
"finds all the `occ` occurrences … in time `O((1/ε)(m + s·occ) log(σ + n/r))`". OptBWTR — "in
`O(r)` words of space and `O(m log log_w σ + occ)` time".

Shape: between `O(r)` and `O(r log(n/r))` everything is loglog apart; reaching `O(m + occ)`
costs a full `log(n/r)` factor of space; above `r log(n/r)`, more space buys only packed and
alphabet factors. **No interpolation between `r` and `n` besides `n/s` sampling and δ/γ is
known.**

## 3. Compression is not free

**PROVED (unconditional, cell-probe).**
- Random access in grammar/LZ/**BWT**-compressed strings: Chen–Verbin–Yu (SODA 2013) — "if the
  space is `poly(n)`, then the query time must be at least `(log L)^{1−ε}/log S` where `S` is
  the space used"; "for … `L = n^{1+ε}` … if the space is `n·polylog(n)`, then the query time
  must be at least `Ω(log n/log log n)`"; "We prove lower bounds also for the case of
  LZ-compression and Burrows-Wheeler (BWT) compression." The cleanest "compression taxes
  queries" theorem, but about `access`, not `count`/`locate`.
- Rank with near-linear space: Belazzougui–Navarro (TALG 2015), Thm 2 — "Any data structure
  that uses `n·w^{O(1)}` space to represent a sequence of length `n` over alphabet `[1,σ]`,
  for any `σ ≤ n·w^{O(1)}`, must use time `Ω(lg σ / lg lg w)` to answer rank queries." `O(r)`
  space is inside `n·w^{O(1)}`, so it bounds every FM-style count step; **transfer to `count`
  proper is OPEN** (counting need not expose rank).
- Bitmap redundancy: Golynski 2007 (quoted by Belazzougui–Navarro) — "a lower bound of
  `Ω(n lg lg n/ lg n)` extra bits for supporting either operation in constant time if `S` is to
  be represented in plain form, and gave matching upper bounds." The canonical `log log n`
  tax: O(1) rank/select is impossible *at* `n` bits.
- Products: Golynski 2009 — "if `t` and `t⁰` are the time complexities for access and select,
  and `ρ` is the bit-redundancy per symbol, then `ρ·t·t⁰ = Ω((lg σ)²/w)`"; Grossi et al. 2010:
  for plain-form encodings, rank within `a` accesses forces `ρ = Ω((lg σ)/a)`.

**CONDITIONAL.**
- De–Kempa 2026: rank / symbol-occurrence on grammar- and LZ78-compressed texts in polylog
  time within `O(|G| log^{O(1)} n)` space "would imply an `O(n² log^{O(1)} n)`-time algorithm
  for Boolean Matrix Multiplication … where the best known algorithms achieve
  `O(n^{2.371339})` time"; range-distinct-count hardness is "under the popular Orthogonal
  Vectors (OV) conjecture".

**Not found:** any lower bound tying `count`/`locate` time to `r`-space (arXiv searches
returned nothing). §2 rests entirely on upper bounds.

## 4. What is *not* known

- **The shape.** Only points are known. Nobody has proved that `O(r)` space forces
  `Ω(log log n)` per occurrence, nor that `O(r log(n/r))` is needed for `O(m + occ)`. The
  hierarchy stood until δ-SA collapsed it (Kempa–Kociumaka: "This collapses the hierarchy of
  compressed data structures into a single point").
- **Reachability of `r` for access.** Navarro's survey: "An intriguing case is `r`, which
  allows for efficient indexing but not access, as far as we know." No `O(r)`-space random
  access structure is known: one can store `O(r)` and *locate* but not extract.
- **Reachability of `γ`.** "`γ` is a lower bound to all the other repetitiveness measures.
  Yet, we do not know if it is reachable."
- **Impossibility for particular (space, time) pairs** in the `r` regime: none known — only
  `access`/`rank` results (§3) and conditional hardness.
- **Packed vs unpacked.** Whether `O(m log σ/w + occ)` needs GNP Thm 4's extra `w` is open.
- **UNVERIFIED:** K1's 1996 statement; whether K10's `O(n)`-bit LCE structure keeps `o(n)`
  space inside an r-index; whether `min(r, n/s)` samples is tight.

## 5. Trade-off knobs worth formalising the accounting of

1. **Sample count × per-occurrence steps** = `Θ(n)` in every family (`n/s ↦ s`, `min(r,n/s) ↦ s`,
   `r·s ↦ loglog/s`): one product invariant, not two parameters.
2. **Bits-per-run, not words-per-run**: K5 vs K6 is `r log n` vs `r log(n/r)` bits — a `log r`
   gap invisible in the O-word notation of GNP Thm 1.
3. **`log log_w(n/r)` vs `log log_w σ`**: OptBWTR removes `n/r` from the loglog; a model that
   conflates them cannot see it.
4. **Two directions of "s"**: multiplicative (`r·s`) vs divisive (`n/s`) — same symbol,
   different accounting.
5. **The `σ` term**: `+σ` bits and `log_σ` factors are free only while `σ ≤ n/log n`.
6. **Level count** in blocked structures: `log(n/r)` levels × `O(r)` words — space is a
   *product*, which is why `O(m+occ)` costs a factor and not a loglog.
7. **Access vs locate vs count** are three cost currencies; `r` space gives locate but not
   access (§4) — account for them separately.

## Sources

Read as full text: arXiv 1705.10382 (GNP, JACM 2020) · 2409.14654, 2103.15329 (sr-index) ·
2006.05104 (Nishimoto–Tabei) · 2408.04537 (RLCSA) · 2602.11029 (move structures) · 2308.03635
(δ-SA) · 1904.04228 (LCE) · 1111.2621 (Belazzougui–Navarro) · 1203.1080 (Chen–Verbin–Yu) ·
2607.07366 (De–Kempa) · 2004.02781 (Navarro CSUR). Second-hand only, hence
FOLKLORE/UNVERIFIED above: Kärkkäinen–Ukkonen 1996, Mäkinen et al. 2010, Golynski 2007/2009,
Grossi et al. 2010.
