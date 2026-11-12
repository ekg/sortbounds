# Query times achievable in `O(r)` space — the state of the art

`T[1..n]`, alphabet `[1..σ]`, `P[1..m]`, `occ` = occurrences of `P` in `T`, `r` = number of
runs in the BWT of `T`, `w = Θ(log n)` = machine word (unit-cost word RAM unless stated).
Space in **words** unless marked "bits". "Optimal" always means optimal *for the stated
space*: `Ω(m)` for count (the pattern must be read) and `Ω(m + occ)` for locate (the
occurrences must be written).

This file is the `O(r)` slice of thread T. The knobs that *buy* time with space, and the
shape of the frontier from `O(r)` to `O(n)`, are in `time-2-tradeoffs.md`; it is not
repeated here. Lower bounds (and the absence of any for `r`-space indexes) are in
`time-3-lower-bounds.md`.

**Reading conventions used below.**

* **VERBATIM** = quoted from the paper's own text, which I read in full (arXiv PDF, text
  extracted with `pdftotext`). Theorem numbering is the arXiv version's, which for GNP
  matches the numbering the sibling files cite.
* **UNVERIFIED** = stated from memory or second-hand, not confirmed against the source.
  What would settle it is said explicitly.
* Bibliographic data (venue, volume, page range) was **not** re-verified against a
  publisher or dblp — both were unreachable from this sandbox (dblp served an
  anti-bot page, Crossref returned empty, OpenAlex is rate-budgeted). Author/year/venue
  as given in the papers' own text or arXiv metadata is reliable; volume/page numbers
  are marked UNVERIFIED where I could not read them off a primary source.

---

## 1. The results, in order

### 1.1 Before the r-index: the RLFM-index (baseline, not `O(r)`)

Mäkinen–Navarro–Sirén–Valenzuela (JCB 2010) gave the first run-length FM-index. It
achieves `O(r)` space **for counting only**; locating needs an ordinary SA sample of
`O(n/s)` words. GNP summarise it as Lemma 1 (VERBATIM):

> **Lemma 1.** The Run-Length FM-index of a text `T [1..n]` whose BWT has `r` runs can
> occupy `O(r)` words and count the number of occurrences of a pattern `P [1..m]` in time
> `O(m log log_w (σ + n/r))`. It also computes `LF` and access to any `BWT [p]` in time
> `O(log log_w (n/r))`.

and GNP state the failure mode plainly (VERBATIM, §2.5):

> …although they can efficiently count within `O(r)` space, they need a much larger
> `O(n/s)` space to support these operations in time proportional to `O(s)`. Despite
> various efforts [65], this has been a bottleneck in theory and in practice since then.

**Do not** attribute `O(r + n/s)` to the r-index. That is the rlfm-index's bound: it is a
*divisive* sample (`n/s`) *added* to `r`. The r-index's own parameter `s` is
*multiplicative* (`r·s`) — see `time-2-tradeoffs.md` §1, corrections (a) and (b), where
this is already recorded.

### 1.2 The r-index: Gagie–Navarro–Prezza (SODA 2018; J. ACM 2020)

Full text read: **arXiv:1705.10382v4**. Everything in this subsection is VERBATIM from it.

Main trade-off theorem:

> **Theorem 1.** Let `s > 0`. We can store a text `T [1..n]`, over alphabet `[1..σ]`, in
> `O(rs)` words, where `r` is the number of runs in the BWT of `T`, such that later, given
> a pattern `P [1..m]`, we can count the occurrences of `P` in `T` in
> `O(m log log_w (σ + n/r))` time and (after counting) report their `occ` locations in
> overall time `O((1 + log log_w (n/r)/s) · occ)`.
>
> In particular, we can locate in `O(m log log_w (σ + n/r) + occ log log_w (n/r))` time and
> `O(r)` space or, alternatively, in `O(m log log_w (σ + n/r) + occ)` time and
> `O(r log log_w (n/r))` space.

That "in particular" is the `O(r)` frontier people quote. The `J. ACM` abstract puts the
two headline points this way (VERBATIM):

> …showing how to extend the Run-Length FM-index so that it can locate the `occ`
> occurrences efficiently within `O(r)` space (in loglogarithmic time each), and reaching
> optimal time `O(m + occ)` within `O(r log(n/r))` space, on a RAM machine of
> `w = Ω(log n)` bits. Within `O(r log(n/r))` space, our index can also count in optimal
> time `O(m)`.

So: **`O(m + occ)` at `O(r)` is *not* a GNP result.** At `O(r)` they get
`occ · log log_w(n/r)`; `occ` is **additive**, and `occ` is **multiplied** by a
`log log_w(n/r)` per-occurrence factor.

#### Where each factor comes from

* **The `2r`-size SA sample.** The toe-hold is built from predecessor structures `R_c`
  storing, per run of each character `c`, *both* endpoints. VERBATIM (proof of Lemma 2):

  > We store a RLFM-index and predecessor structures `R_c` storing the position in `BWT` of
  > the right and left endpoints of each run of copies of `c`. Each element in `R_c` is
  > associated to its corresponding text position, that is, we store pairs `⟨i, SA[i] − 1⟩`
  > sorted by their first component… These structures take a total of `O(r)` words.

  and the size is stated exactly: "Since `R` contains `2r` elements on a universe of size
  `σn`, we can have predecessor searches in time `O(log log_w (nσ/r))` and `O(r)` space."
  So it is `2r` `⟨BWT position, SA value − 1⟩` pairs — `4r` words of payload by my
  arithmetic, plus the predecessor index — still `O(r)` words, and emphatically not `2r`
  bits. (Bannai–Gagie–I §1.3 halve this payload.)

* **The `log log_w(σ + n/r)` factor.** It is the sum of two independent predecessor/rank
  costs, and the `σ` and `n/r` terms are *different objects*. VERBATIM (proof of Lemma 1):

  > We use the RLFM+ [65, Thm. 17], using the structure of Belazzougui and Navarro [10,
  > Thm. 10] for the sequence `L0` (with constant access time) and the predecessor data
  > structure described by Belazzougui and Navarro [10, Thm. 14] to implement `E`… The sum
  > of both operation times is `O(log log_w σ + log log_w (n/r))`, which can be written as
  > `O(log log_w (σ + n/r))`.

  Concretely: `log log_w σ` is a **rank on the run-head string `L0` over alphabet σ**
  (there are at most `min(σ, r)` distinct run symbols, but the universe is the alphabet);
  `log log_w (n/r)` is a **predecessor search on BWT positions**, whose universe is `n` and
  whose stored set has `2r` elements, hence the `n/r` after the reduction. Writing the sum
  as one `log log_w(σ + n/r)` is a notational convenience — a structure that fixes one term
  does not automatically fix the other (this is exactly what OptBWTR exploits, §1.4).

* **`log(n/r)` is the "primary occurrence" depth.** Lemma 6: every text substring has a
  *primary* occurrence containing a sampled character, at most `O(log(n/r))` LF steps away.
  This is the source of every `log(n/r)` and of the `r log(n/r)` block-structure space.

#### Getting to `O(m)` count / `O(m + occ)` locate: two different routes

Route A — **index all the short patterns** (GNP Theorem 3). This is the cheapest space at
which the unconditional optimal bound is available. VERBATIM:

> **Theorem 3.** We can store a text `T [1..n]` in `O(r log(n/r))` words, where `r` is the
> number of runs in the BWT of `T`, such that later, given a pattern `P [1..m]`, we can
> report the `occ` occurrences of `P` in optimal `O(m + occ)` time.

The proof indexes every distinct `(log(n/r))`-mer (there are `O(r log(n/r))` of them by
GNP's Lemma 14), storing at each trie node the triple `⟨occ, i, δ⟩` that lets the whole SA
interval be read off an array `W` in `O(1)` per entry. Note the accounting: the space is a
**product** `r · log(n/r)` — `log(n/r)` levels of `O(r)` — which is why optimal time costs
a factor and not another `log log`. Count is `O(m)` here because `occ = 0` is decidable by
the trie walk; GNP state that separately as Theorem 9 (VERBATIM):

> **Theorem 9.** We can store a text `T [1..n]` in `O(r log(n/r))` words, where `r` is the
> number of runs in the BWT of `T`, such that later, given a pattern `P [1..m]`, we can count
> the occurrences of `P` in optimal `O(m)` time.

Route B — **move structure** (OptBWTR, §1.4): `O(r)` words and *no* `n/r` in the loglog,
at the price of a `log log_w σ`.

The packed analogue (GNP Theorem 4, VERBATIM):

> **Theorem 4.** We can store a text `T [1..n]` over alphabet `[1..σ]` in
> `O(rw log_σ (n/r))` words, where `r` is the number of runs in the BWT of `T`, such that
> later, given a packed pattern `P [1..m]`, we can report the `occ` occurrences of `P` in
> optimal `O(m log(σ)/w + occ)` time.

### 1.3 Refining the r-index: Bannai–Gagie–I (CPM 2018; TCS 2020)

Full text read: **arXiv:1802.05906v6** (the TCS preprint; the CPM 2018 version is titled
"Online LZ77 parsing and matching statistics with RLBWTs" and the paper says so in a
footnote). VERBATIM, the abstract's own summary of what it does:

> In this paper we first strengthen and simplify Policriti and Prezza's Toehold Lemma
> (DCC '16; Algorithmica, 2017), which inspired the r-index and plays an important role in
> its implementation. We then show how to update the r-index efficiently after adding a new
> genome to the database, which is likely to be vital in practice. As a by-product of this
> result, we obtain an online version of Policriti and Prezza's algorithm for constructing
> the LZ77 parse from a run-length compressed Burrows-Wheeler Transform… Finally, we show
> how to augment the r-index such that, given a new genome and fast random access to the
> database, we can quickly compute the matching statistics and maximal exact matches of the
> new genome with respect to the database.

**What exactly improved.** Three separate things, and it matters which is which:

1. **The sample shrinks from `2r` to `r`.** VERBATIM (§2.3):

   > Policriti and Prezza augmented the RLBWT to store the SA entries `SA[i]` and `SA[j]`
   > that are the positions in the text of the first and last characters in each run
   > `BWT[i..j]`. They showed how, with this extra information, a backward search for a
   > pattern can be made to return the location of one of its occurrence (assuming it
   > occurs at all).
   >
   > We can simplify and strengthen Policriti and Prezza's result slightly, **storing only
   > the position of the first character of each run** and finding the starting position of
   > the lexicographically first suffix starting with a given pattern.
   >
   > (boldface mine)

2. **It is a strengthening, not just a saving:** the returned occurrence is now the
   *lexicographically first* one, which is what makes the dynamic update work.

3. **`O(r)`, not `O(rσ)`, for the MEM/matching-statistics augmentation** — the paper says
   the conference version needed `O(rσ)` words and "we have reduced this to `O(r)`".

Their refined toe-hold (VERBATIM):

> **Lemma 2.** We can augment an RLBWT with `O(r)` words, where `r` is the number of runs
> in the BWT, such that after each step in a backward search for a pattern, we can return
> the starting position of the lexicographically first text suffix prefixed by the suffix
> of the pattern we have processed so far.

> **Theorem 8.** We can augment an RLBWT for `T` with `O(r)` words, where `r` is the number
> of runs in the BWT for `T`, such that later, given `S[1..m]` and `O(log log n)`-time
> random access to `T`, we can compute the matching statistics for `S` with respect to `T`
> in `O(m log log n)` time.

**The important caveat for a query-time table.** BGI's contribution is *not* a better
count/locate bound. Their setting is **dynamic**, and every operation is a balanced-tree
operation: VERBATIM (§3), the online r-index maintains "a data structure to compute `LF` in
`O(log r)` time, a data structure to compute `pred_B` and insertion/deletion of new element
to/from `B` in `O(log r)` time (using a standard balanced search tree)". Locating still
steps through SA entries one at a time via `pred_B` (their Lemma 4, which is GNP's Lemma
3), so in their dynamic version per-occurrence cost is `O(log r)`, **worse** than GNP's
`O(log log_w(n/r))` — traded for the ability to update. Their experiments compare
"online" against "offline" r-index and find online ~4× the space and ~10% slower at
locate. **A table that lists BGI as improving locate time would be wrong.** What it
improves is space-per-sample (`2r → r`), the proof, and updatability.

### 1.4 OptBWTR / the move structure: Nishimoto–Tabei (ICALP 2021)

Full text read: **arXiv:2006.05104v3**. This paper *is* "OptBWTR", so the brief's items 3
("Nishimoto–Tabei move structure") and 4 ("OptBWTR") are one result, not two. The paper
calls its gadget a **move data structure**; the later literature (Brown et al. 2024/2026,
Sanaullah et al. 2025) calls it the **move structure**. VERBATIM, the central theorem:

> **Theorem 9.** OptBWTR requires `O(r)` words, and it supports count and locate queries on
> a string `T` in `O(m log log_w σ)` and `O(m log log_w σ + occ)` time, respectively. We can
> construct OptBWTR in `O(n + r log r)` time and `O(r)` words by processing the RLBWT of
> `T`.

**So the answer to the question "is count now `O(m)` and locate `O(m + occ)` in `O(r)`
space?" is: NO, not for general `σ`.** It is `O(m log log_w σ + occ)`, and the paper is
explicit that optimality is conditional on the alphabet. VERBATIM (§1):

> Locate query: OptBWTR can solve a locate query on an input string in `O(r)` words of
> space and `O(m log log_w σ + occ)` time, **which is optimal for strings with
> polylogarithmic alphabets (i.e., `σ = O(polylog n)`)**.
>
> Count query: OptBWTR can return the number of occurrences of a query string on an input
> string in `O(r)` words of space and `O(m log log_w σ)` time, **which is optimal for
> polylogarithmic alphabets**.

(Emphasis added. `O(log log_w σ) = O(1)` once `σ ≤ w^{O(1)}`, e.g. `σ = polylog n`.)

**Where the residual `σ` lives — and it is *not* the same `σ` as GNP's.** OptBWTR removes
`n/r` from the loglog entirely (constant-time `LF` and `φ⁻¹` — that is the whole point of
the move structure) but a `log log_w σ` survives inside its backward-search step, from the
rank structure on the run-head string. VERBATIM (appendix C.1):

> `R_rank` is a rank data structure for solving a rank query on a string `S` in
> `O(log log_w σ)` time and with `O(|S|)` words of space [3].

So `O(r)`-space count is `O(m)` **iff** alphabet rank on a length-`O(r)` string over `[1..σ]`
is `O(1)`. GNP's `log log_w(n/r)` per occurrence is gone; the `σ` term is not.

**What the move structure is.** It replaces predecessor queries on BWT positions by
"move queries" on a partition of `BWT` into *balanced* intervals, with two arrays
`D_pair`, `D_index` of size `O(r)`, so that `LF`, `FL`, `φ`, `φ⁻¹` and the SA successor are
all `O(1)`. VERBATIM (§1): "we present a novel data structure that can compute `LF` and
`φ⁻¹` in constant time and `O(r)` words of space", against the previous
`O(log log_w (n/r))`.

**σ-free / σ-dependent variants: yes, and this is the crux.** The paper's Table 1 is the
cleanest statement of the alternatives at larger space:

| Space (words) | Count | Locate |
|---|---|---|
| `O(r log log_w (σ + n/r))` (r-index) | `O(m)` | `O(m + occ)` |
| `O(rw log_σ(n/r))` (packed r-index, GNP Thms 4 & 10) | `O(⌈m log(σ)/w⌉)` | `O(⌈m log(σ)/w⌉ + occ)` |
| `O(r)` (**OptBWTR**) | `O(m log log_w σ)` | `O(m log log_w σ + occ)` |

**Discrepancy, flagged rather than papered over:** NT's Table 1 renders the packed row's
space as `O(rw log_σ log_w n)`, while GNP's own Theorem 4 and Theorem 10 both say
`O(rw log_σ(n/r))` words (quoted verbatim in §1.2). These are not the same function. I use
GNP's expression, since it is the primary statement; NT's rendering is either a
transcription of a different derivation or a typo. **UNVERIFIED which** — settling it needs
the ICALP proceedings or journal version, or an author's reply.

Read across: **there is no row that is `O(r)` space and `O(m)` count for unrestricted
`σ`.** The `O(m)`-count rows either pay `log log_w(σ + n/r)` space or `rw log_σ(n/r)`
space. Conversely OptBWTR buys `σ`-independence-of-`n/r` at `O(r)` and pays `log log_w σ`.

Its other queries are genuinely optimal and `σ`-free in the interesting cases:
extract `O(1)` per character in `O(r + b)` words for `b` bookmarks (Theorem 10),
decompression `O(n)` in `O(r)` (Theorem 11) — the first linear-time RLBWT decompression in
`O(r)` working space — and prefix search `O(m + occ')` in `O(r' + |D|)` words (Theorem 12).

On the size of the move structure: it is five `O(r)`-word components (`F(I_LF)`, `F(I_ISA)`,
`R(L_first)`, `SA⁺`, `SA⁺_index`), each move structure being two arrays of size `O(r)`; the
text I read states the LF move structure's input-interval count as `k ≤ 2r`. So "`O(r)`
words" is right, "`2r` bits" would be wrong.

### 1.5 After 2021 — what actually moves the `O(r)` frontier

Everything here is from the arXiv abstract unless marked otherwise, so **treat the
times as quoted but the surrounding claims as UNVERIFIED** — I read the abstract and, where
stated, selected sections of the full text of only one of these (item 1).

1. **`OptBWTRL` — adding `LCP`/`PLCP` in `O(1)` at `O(r)` words (Sanaullah–Zhi–Zhang,
   2025, arXiv:2505.15698).** The one post-2021 result I found that **does** tighten a
   query at `O(r)` words. Full text read; VERBATIM from §1:
   > `OptBWTRL`: OptBWTRL is an `O(r)` words space data structure that maintains the
   > capabilities of OptBWTR and adds the ability to compute `φ`, `PLCP`, and long LEMs
   > efficiently.
   >
   > `PLCP`: OptBWTRL enables constant time `PLCP[i]` computation in `O(r)` space. Note that
   > `PLCP[SA[j]] = LCP[j]`, therefore `PLCP` computation in constant time allows `LCP[j]`
   > computation in constant time given `SA[j]`.

   and the query result VERBATIM:
   > We describe an `O(m + occ)` expected time long LEM query for pattern `P` and text `T`
   > given the matching statistics of `P` with respect to `T`. The underlying index
   > (OptBWTRL) uses `O(r)` space.

   Reconcile against GNP's two prior LCP-access points, quoted VERBATIM:
   > **Lemma 5.** Let `s > 0`. We can store a data structure of `O(rs)` words such that, given
   > `SA[p]`, we can compute `LCP[p−i+1]` and `LCP[p+i]`, for `i = 1, …, s0` and any `s0 ≤ s`,
   > in time `O(log log_w(n/r) + s0)`.
   >
   > **Theorem 7.** Let the BWT of a text `T[1..n]` contain `r` runs. Then there exists a data
   > structure using `O(r log(n/r))` words that can retrieve any `ℓ` consecutive values of its
   > longest common prefix array in time `O(log(n/r) + ℓ)`.

   So `O(1)` at `O(r)` words is a real improvement on both cells: the same trick that removed
   `log log_w(n/r)` from locate also removes it from `LCP`. Caveats: the bound is
   **expected**, and this is an *augmented* `O(r)` (larger constant, same asymptotics).

2. **Below `r` words, at the cost of time (Brown–Gagie–Manzini–Navarro–Sciortino 2024,
   arXiv:2408.04537).** VERBATIM:
   > We first review how we can store a run-length compressed suffix array (RLCSA) for a text
   > `T` of length `n` over an alphabet of size `σ` whose `BWT` consists of `r` runs in
   > `O(r log(n/r) + r log σ + σ)` bits such that later, given character `a` and the suffix
   > array interval for `P`, we can find the SA interval for `aP` in `O(log r_a + log log n)`
   > time, where `r_a` is the number of runs of copies of `a` in the BWT. We then show how to
   > modify the RLCSA such that we find the SA interval for `aP` in only `O(log r_a)` time,
   > without increasing its asymptotic space bound. Our key idea is applying a result by
   > Nishimoto and Tabei (ICALP 2021) and then replacing rank queries on sparse bitvectors by
   > a constant number of select queries.

   **This does not move the `O(r)`-word frontier and must not be tabulated as if it did:**
   `O(r log(n/r) + r log σ + σ)` *bits* is far below `r` words (it is `o(r)` words whenever
   `log(n/r) + log σ = o(log n)`), and the price is `O(log r_a)` per backward-search step
   rather than OptBWTR's `O(1)`. It is a **cheaper-space** point, i.e. thread-S/`time-2`
   territory. It is, however, the cleanest published confirmation that the move structure
   is now the standard building block.

3. **Move structure reconstruction and average-case analysis (2026).** Brown–Sanaullah–
   Zhang–Langmead, arXiv:2603.22147: "While the existing best `O(r)`-space construction
   approaches require `O(r log r)`-time, we present an optimal `O(r)`-time and space
   construction algorithm." Brown–Langmead, arXiv:2602.11029, sharpens the practical story and
   contains the one theoretical caveat worth recording: the worst-case `O(1)` move query
   needs the original interval-splitting *balancing*; with plain length capping they get
   optimal *average* query time and "[t]he worst case query time is also improved to
   `O(log(n/r))` without balancing". So "`O(r)` words, `O(1)` per step" is a **worst-case**
   claim that is paid for in balancing and in `O(r log r)`-bit components.

4. **Bi-directional variants (Move-rb, Fischer–Nalbach, 2026, arXiv:2609.30089).** Space is
   `O(r + r⃖)` for both directions (runs of `T` and of `T^R`) and the motivating bottleneck
   is explicitly the alphabet: VERBATIM, existing variants "suffer from two bottlenecks:
   `O(σ)` character-predecessor/-successor queries on the run-length-encoded BWT per
   extension, and predecessor queries on sparse bit vectors". VERBATIM on their fix:
   "Without a direction switch, Move-rb computes an all-`k`-character extension in
   output-optimal `O(k)` time and a single-character extension in the same time", and
   "[a] direction switch incurs only `O(log log_ω(n/r_min))` additional time". This is the
   `log log_w(n/r)` factor reappearing in the *bi-directional* setting — evidence that it is
   tied to switching direction, not to a single-direction scan.

5. **`r*`-indexing (Gagie, 2025, arXiv:2508.12675).** VERBATIM: "Let `T[1..n]` be a text over
   an alphabet of size `σ ∈ polylog(n)`, let `r*` be the sum of the numbers of runs in the
   `BWT`s of `T` and its reverse, and let `z` be the number of phrases in the LZ77 parse of
   `T`. We show how to store `T` in `O(r* log(n/r*) + z log n)` bits such that … we can
   report the locations of the `occ` occurrences of `P` in `T` in `O(m log n + occ log^ε n)`
   time." Both the space measure (`r*`, plus `z`) and the time (`m log n`) are outside the
   `O(r)`-space column; it trades time for a different, and sometimes smaller, measure.

6. **`sr`-index (Cobas–Gagie–Navarro, CPM 2021 / 2024).** `O(min(r, n/s))` space with time
   per occurrence multiplied by `s` — again *below* `r`, so it belongs to
   `time-2-tradeoffs.md` (K4), not here.

### 1.6 Two things the brief asked about that I could not substantiate

* **Non-overlapping indexing in `r`-space — NOT FOUND.** I searched the arXiv API for
  `abs:"non-overlapping indexing" AND abs:"run-length"` (0 hits), `abs:"non-overlapping
  indexing"` (only Cohen–Porat 2009, *Range Non-Overlapping Indexing*, unrelated to `r`),
  and `abs:"non-overlapping occurrences"` (8 hits, none about `r`-bounded space). dblp
  blocked this sandbox and Semantic Scholar rate-limited me. So: **I have no evidence that
  a non-overlapping-indexing structure with `O(r)` space and `o(occ)`-independent reporting
  time exists**, and equally no evidence that it does not.
  *What would settle it:* a dblp author search for Bannai/Gagie/Köppl/Thankachan around
  2022–2025, or one Semantic Scholar query for `non-overlapping indexing` restricted to
  SPIRE/CPM/ISAAC.
* **eBWT indexing — no asymptotic query-time result on this frontier.** The eBWT/XBWT line
  is about *construction* and about *run counts*, not count/locate times. The one indexing
  paper close to the question, Gagie–Gourdel–Manzini, *Compressing and Indexing Aligned
  Readsets* (arXiv:1809.07320), is explicitly experimental and even admits errors: VERBATIM,
  "Although this index can occasionally return false positives, it is usually much more
  compact than the alternatives", with the evidence given as run counts ("eliminating
  separators characters from the EBWT reduces the number of runs by 19%, from 220 million to
  178 million"). Also notable: it defines "`r`" on the *transformed* string, so its bounds
  are not comparable to the `r` of `BWT(T)` without care. There is **no `O(r)`-space
  eBWT count/locate bound** to put in the table.

### 1.7 One nearby 2026 result that looks like it should help — and does not, at `O(r)`

Bals–Charalampopoulos–Lachish–Pissis–Verbeek, *Text Indexing: From Reporting to Counting*
(ESA 2026, arXiv:2607.24043) prove a generic lifting (VERBATIM): "Our framework acts as a
convenient black box, lifting indexes with reporting time `O(|P| + |Occ_T(P)|)` to support
counting queries in time `O(|P|)`". If that applied to the r-index it would give `O(m)`
count at `O(r)` words *unconditionally* — i.e. it would beat OptBWTR. It does not, as far
as I can tell: the mechanism is "store the counts for the at most `n` 'frequent' substrings
of `T` in a preprocessing step", and that table is `Θ(n)` substrings, which is not
`O(r)`-bounded and is not shown compressible in terms of `r`. **UNVERIFIED** — I read only
the abstract. *What would settle it:* whether the frequent-substring table can be stored in
`O(r)` space; if it cannot, this is a `Θ(n)`-space technique and orthogonal to thread T.

---

## 2. The table

Sorted by space. `σ_eff` = `min(σ, r)`. "assumptions" lists what the bound additionally
needs beyond `w = Θ(log n)` unit-cost word RAM.

| structure | space (words / bits) | count | locate | assumptions | citation |
|---|---|---|---|---|---|
| rlfm-index | `O(r + n/s)` words | `O(m(log σ/log log r + (log log n)²))` | same `+ occ`-term, `O(s·occ)` factor: `O((m + s·occ)(log σ/log log r + (log log n)²))` | `s ≥ 1`; **not** `O(r)` | Mäkinen–Navarro–Sirén–Valenzuela, JCB 2010 — **UNVERIFIED**, quoted from NT21 Table 1 |
| **r-index** (GNP Thm 1, `s=1`) | **`O(r)` words** | `O(m log log_w(σ + n/r))` | `O(m log log_w(σ + n/r) + occ·log log_w(n/r))` | unit-cost word RAM, `w = Ω(log n)` bits; effective alphabet assumed (`σ ≤ r ≤ n`) | GNP, SODA 2018 / J. ACM 2020, Thm 1 (arXiv:1705.10382v4) |
| r-index, sampled | `O(rs)` words | `O(m log log_w(σ + n/r))` | `O(m log log_w(σ + n/r) + occ·(1 + log log_w(n/r)/s))` | `s > 0`; `s` is **multiplicative** in `r` | GNP Thm 1 |
| **BGI-refined r-index** | **`O(r)` words** (`r` SA samples, was `2r`) | as r-index | `occ · O(log r)` in their **dynamic** version (balanced-tree `pred_B`); static = GNP | supports prepend-updates; not a time improvement | Bannai–Gagie–I, CPM 2018 / TCS 2020, Lemmas 2–4, §3 (arXiv:1802.05906v6) |
| **OptBWTR** (move structure) | **`O(r)` words** (five `O(r)`-word components; LF move structure has `k ≤ 2r` intervals) | `O(m log log_w σ)` | `O(m log log_w σ + occ)` | optimal **only for `σ = O(polylog n)`**; `LF`,`φ`,`φ⁻¹` in `O(1)`; `O(1)` per step needs interval-splitting balancing | Nishimoto–Tabei, ICALP 2021, Thm 9 (arXiv:2006.05104v3) |
| **OptBWTRL** (OptBWTR + `LCP`) | **`O(r)` words** | `O(m log log_w σ)` | `O(m log log_w σ + occ)` | adds `φ` and `PLCP[i]`/`LCP[j]` in **`O(1)`** at `O(r)`; long-LEM query `O(m + occ)` **expected** | Sanaullah–Zhi–Zhang 2025 (arXiv:2505.15698) — abstract + §1/§4 read |
| r-index + short-pattern trie | `O(r log(n/r))` words | **`O(m)`** (Thm 9) | **`O(m + occ)`** (Thm 3) | needs all `O(r log(n/r))` distinct `log(n/r)`-mers indexed (Lemma 14); `occ` **additive** | GNP Thm 3 (locate), Thm 9 (count), Lemma 14 |
| r-index, packed | `O(rw log_σ(n/r))` words | `O(m log(σ)/w)` (Thm 10) | `O(m log(σ)/w + occ)` (Thm 4) | packed strings; optimal in packed model | GNP Thm 4 (locate), Thm 10 (count) |
| RLCSA (bit-space; **not** the `O(r)`-word column) | `O(r log(n/r) + r log σ + σ)` **bits** | backward step `O(log r_a)` | via ordinary SA sampling; no `r`-bounded locate claim | `r_a` = runs of character `a`; below `r` words, so time is worse | Brown–Gagie–Manzini–Navarro–Sciortino 2024 (arXiv:2408.04537), abstract |

The "current best" depends on the currency, and there are exactly three answers:

* **`O(r)` words, unrestricted `σ` — this is the exact state of the art.**
  count `O(m log log_w σ)`, locate `O(m log log_w σ + occ)`.
  **Nishimoto–Tabei, ICALP 2021, Theorem 9** (quoted verbatim in §1.4).
* **`O(r)` words, `σ = polylog n`:** count `O(m)`, locate `O(m + occ)` — same theorem,
  same paper; the `σ` hypothesis is doing real work. **Nothing I found at `O(r)` words does
  better than this for any `σ`.**
* **Unconditional `O(m)` / `O(m + occ)` at the cheapest space:** `O(r log(n/r))` words —
  **GNP Theorem 3** (and packed `O(m log σ/w + occ)` at `O(rw log_σ(n/r))`, GNP Thm 4).
  OptBWTR did **not** improve on this space; it only removes the `n/r` from the loglog at
  `O(r)`.

---

## 3. Reducible or irreducible? (JUDGEMENT — explicitly not a theorem)

The repository's rules say: label judgement as judgement. Everything in this section is my
reading, not a proved statement, and no lower bound in `time-3-lower-bounds.md` backs any
part of it.

**Believed irreducible (near-certainly not removable).**

1. **`Ω(m)` in count and `Ω(m + occ)` in locate.** Trivial, but worth naming because the
   literature's "optimal" means exactly this and nothing more. Any `O(m)` claim is a claim
   about *overhead being `O(1)` per pattern character*, not about beating `m`.
2. **Some `σ`-dependent factor, for general `σ`, at `O(r)`.** Judgement, but well
   evidenced: three independent designs at three space points (GNP `log log_w(σ + n/r)`,
   OptBWTR `log log_w σ`, packed `log σ/w`) all keep an alphabet term, and OptBWTR is
   *explicit* that it is optimal only for polylog `σ`. The mechanism is structural —
   every design must map a `[1..σ]` symbol to a rank in a structure of `O(r)` words, i.e.
   answer a predecessor question on universe `σ` with `O(r)` space, and
   Belazzougui–Navarro's `Ω(log σ / log log w)` rank bound bites in that regime. I would
   not bet on `O(m)` count in `O(r)` words for `σ = Θ(n)`.
3. **`Ω(occ)` output, additively.** Locate bounds are `+ occ`, never `· occ`, in the
   optimal rows; that is inherent in reporting positions.

**Merely not-yet-removed (I would expect progress, and there is no lower bound).**

4. **`log log_w(n/r)` (GNP), everywhere it appears.** Already removed by OptBWTR for `LF`,
   `φ`, `φ⁻¹` and per-occurrence locate (`occ` becomes additive at the same `O(r)` words),
   and removed again by OptBWTRL for `PLCP`/`LCP` access (§1.5). Three separate removals at
   the same space bound make it as clearly *technique-bound* as anything here gets. The
   *cost* of removing it was `log log_w σ` appearing on the count side and dense `O(r)`-word
   move tables — an exchange rate, not a wall. (It does survive in the bi-directional
   setting as a direction-switch cost, `O(log log_ω(n/r_min))` for Move-rb — where it looks
   attached to the *switch*, not to the search.)
5. **`log(n/r)` space for `O(m)` count (GNP Thm 3).** No lower bound exists; it is a
   product of the primary-occurrence depth, i.e. of one particular technique. Note that
   OptBWTR reaches `O(m log log_w σ)` at `O(r)` — so the *unconditional* `O(m)` at
   `O(r log(n/r))` and the polylog-`σ` `O(m)` at `O(r)` are one `log log` apart, and
   nothing shows which is the true frontier.
6. **`min(r, n/s)` sample counts and the `r log(n/r)` bits-vs-words gap.** Accounting
   artefacts of word-RAM reporting; the sibling `time-2-tradeoffs.md` §1 (K5 vs K6) shows a
   `log r` bit-gap that the `O`-word notation hides.
7. **Whether the `log log_w σ` in OptBWTR can be driven to `O(1)` at `O(r)` words.** This is
   the concrete form of (2), listed separately because it is a specific data-structure
   question and because nothing I read rules it out — my confidence here is *lower* than for
   the general statement in (2). **What would settle it:** either a rank structure on the
   length-`O(r)` run-head string with `O(1)` query time in `o(σ)` words — which would
   contradict the Belazzougui–Navarro-style bound unless it exploits that the string has
   `O(r)` *distinct run heads* and not `σ` — or a cell-probe lower bound for that specific
   problem. My judgement: this is where the next result will land, and it will probably be
   about the *effective* alphabet `σ_eff = min(σ, r)` rather than `σ`.

**One thing that is definitely *not* irreducible and is often misread:** the `O(r)` in
"`O(r)` space" is `O(r)` **words ≈ `r log n` bits**, not `2r` bits. GNP's own sampled
structures are `r lg n`-ish bits; the `2r lg r`-bit variants are RLBWT *representations*
(e.g. the online RLBWT implementation BGI use), not the index.

---

## 4. Open / unverified

* **OptBWTR journal version.** The arXiv v3 (Apr 2021) is the ICALP 2021 text. Whether a
  journal version strengthens `O(m log log_w σ)` to `O(m)` is **UNVERIFIED** — I found no
  such version. *Would settle it:* a journal citation, or a 2022+ paper citing OptBWTR's
  improved bound.
* **The exact per-occurrence cost of BGI's static structure.** BGI never state a combined
  count/locate theorem; they inherit GNP's structures and only give the dynamic
  `O(log r)`-per-operation analysis. Attributing `occ·O(log log_w(n/r))` to "the refined
  r-index" is therefore an inference, not a quotation.
* **Mäkinen et al. 2010's exact time bound** is quoted from NT21's Table 1, not read from
  the JCB paper.
* **Bibliographic volume/pages** for GNP (J. ACM), BGI (TCS), NT (ICALP/LIPIcs) were not
  verified against a publisher. dblp served an anti-bot page, Crossref returned empty
  bodies, Semantic Scholar returned HTTP 429, DuckDuckGo returned a JS wall, and OpenAlex
  is rate-budgeted on a shared IP — so **no** bibliographic service was usable from this
  sandbox. Author lists and years come from arXiv metadata (reliable); venues come from the
  papers' own text (reliable for BGI's CPM 2018 footnote and for NT's confirmation in
  Brown et al. 2024: "applying a result by Nishimoto and Tabei (ICALP 2021)").
* **Every 2024+ claim in §1.5–§1.7 rests on abstracts plus, for item 1 of §1.5 only,
  selected sections (§1, §4) of the full text.** I did not re-derive any of their theorems.
* **Non-overlapping indexing in `r`-space: not found** (§1.6) — this is an absence of
  evidence, not evidence of absence.
* **`r*`-indexing and `r*`:** I did not check whether `r* ≠ O(r)` can happen on texts where
  `r` and `r*` differ by more than a constant; the abstract does not say. It matters if you
  want to state "the `O(r)` frontier" versus "the `O(r*)` frontier".

---

## Sources

Read as **full text** (arXiv PDF → `pdftotext`, theorems quoted verbatim):
`1705.10382v4` (Gagie–Navarro–Prezza, SODA 2018 / J. ACM 2020) ·
`1802.05906v6` (Bannai–Gagie–I, CPM 2018 / TCS 2020) ·
`2006.05104v3` (Nishimoto–Tabei, ICALP 2021, OptBWTR) ·
`2505.15698v1` (Sanaullah–Zhi–Zhang 2025, `OptBWTRL` — abstract + §1/§4).

**Abstracts only** (quoted inline, flagged): `2408.04537v7` (RLCSA, 2024) ·
`2602.11029v4` (Brown–Langmead 2026) · `2603.22147v4` (move structure construction, 2026) ·
`2609.30089v2` (Move-rb, 2026) · `2508.12675v1` (`r*`-indexing, 2025) ·
`2103.15329v1`/`2409.14654v1` (`sr`-index) · `2607.24043v4` (reporting→counting, ESA 2026) ·
`1809.07320v5` (eBWT/readsets, 2018).

Second-hand only, hence flagged above: Mäkinen–Navarro–Sirén–Valenzuela (JCB 2010);
Belazzougui–Navarro (TALG 2015) theorems, as cited by GNP and NT; Policriti–Prezza
(DCC 2016 / Algorithmica 2017), as described by BGI.
