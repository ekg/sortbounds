# Thread T3 — the lower-bound side: what is actually impossible

Labels: **PROVED** (theorem, model named), **CONDITIONAL**, **OPEN**, **FOLKLORE**,
**MY-INFERENCE**. Quotes were read in the cited PDFs.

"Is the `r`-index optimal?" **No theorem addresses it, either way.** §3.

## 1. Unconditional bounds (PROVED)

**The canonical text-indexing bound.** Demaine & López-Ortiz, *A Linear Lower Bound on
Index Size for Text Retrieval* (SODA 2002; J. Algorithms 48(1) 2003), Thm 2.1:

> "If I is an index supporting a search for the substring P in S(|P|, |T|) = O(|P|) bit
> probes to the text T, then |I| = Ω(|T|)."

Bit-probe model; `|I|` in bits; the **text is stored** and only text probes are charged —
"an arbitrary amount of computation may be done on an arbitrary amount of the index".
Abstract: "an index supporting linear-time substring searches requires about as much space
as the original text"; it "applies to inverted word indices".

**Succinct substring search.** Gál & Miltersen, *The Cell Probe Complexity of Succinct Data
Structures* (ICALP 2003), Thm 3:

> "Consider Substring Search with parameters n, m so that 2 log₂ n + 5 ≤ m ≤ 5 log₂ n. For
> any systematic scheme solving it with redundancy r and bit probe complexity t, we have
> `(r + 1)t ≥ (1/800)·n/log n`." [fraction split in the PDF]

"Systematic": storage is `φ(x) = x · φ*(x)` — text kept verbatim plus `r` bits. Boolean
problem, weaker than reporting.

**Access + search, general cell probe.** Golynski (SODA 2009; full version = Waterloo thesis
2008, Ch. 5) claims "the first lower bound for the problem of searching and retrieval of a
substring in text" [abstract]. Thesis, after Cor. 5:

> "we need at least Ω(Υ) cells (i.e., linear in the information-theoretic minimum) of extra
> space to support both access and search queries in constant time for patterns of size
> p = lg L/lg σ in the cell probe model with word size lg L."

`Υ ≈ L lg σ/w` is the information-theoretic minimum, so this bounds *redundancy*, and the
preconditions (`tt′ < ε(p lg σ)²/(128 w lg(2ep))`) exclude `t = Θ(log n)`. Earlier
rank/select indexing bound, as quoted in the thesis: "the index size must be
r = Ω((n lg t)/t)".

**The template for §4.** Pătraşcu, *Unifying the Landscape of Cell-Probe Lower Bounds*
(SICOMP 2011), partial match: "a data structure for the partial match problem with
cell-probe complexity t must use space 2^{Ω(d/t)}, assuming the word size is O(n^{1−ε}/t)"
— "optimal for constant query time, but degrades quickly with t". PROVED and
unconditional (via lopsided set-disjointness). The only such space-vs-`t` theorem I found
is about wildcards, not exact matching.

**Dynamic.** Pătraşcu & Demaine (SICOMP 2006): an "amortized randomized Ω(lg n) lower
bound per operation" for partial sums and dynamic connectivity, which "breaks a
long-standing barrier of Ω(lg n/lg lg n)" — the Fredman–Saks bound. Relevant only for a *dynamic*
`r`-index.

**Compressed random access.** Verbin & Yu (CPM 2013), CFG of size `n` deriving length `L`:
if space is `poly(n)` then "the query time must be at least `(log L)^{1−ε}/log S`"; they
"prove lower bounds also for ... Burrows-Wheeler (BWT) compression", but that part
(§6.2) is an informal appendix claim (`runs(s) = n` ⟹ representation `< n log L` bits)
about *character access*. **UNVERIFIED** as a pattern-matching bound.

**Not found:** any pointer-machine lower bound for LCE or pattern matching; any
unconditional LCE query-time bound. Searches were metadata-only (**UNVERIFIED absence**);
settle it by walking citations from the cell-probe literature.

## 2. Conditional bounds (all CONDITIONAL)

- **SETH, unindexed.** LCS/DTW: "an O(n^{2−ε}) time algorithm for computing the LCS or the
  DTWD of two sequences of length n over a constant size alphabet, refutes ... (SETH)"
  (Abboud–Backurs–Williams, FOCS 2015). Edit distance, `O(n^{2−δ})` ⟹ CNF-SAT in
  `M^{O(1)}2^{(1−ε)N}` (Backurs–Indyk, STOC 2015).
- **OVH, indexed.** "Under OVH, one cannot solve OV in O(|X|^α|Y|^β) with α < 1 or β < 1,
  even after allowing arbitrary polynomial-time preprocessing of X" (Gabory, arXiv
  2607.08566, Lemma 5). Applied: "no polynomial-time index of the graph ... can support
  querying P in time O(|P|+|E|^δ|P|^β), with either δ<1 or β<1" (Equi–Mäkinen–Tomescu,
  TCS 2023), also transferred to *indexed edit distance*; and "no solution for GD-indexing
  with query time O(n^α m^{O(1)} + m) ... under OVH (and hence SETH)" (Gabory, Thm 6, from
  Gibney, SPIRE 2020).
- **k-Clique / OMv, indexed.** "no combinatorial index with polynomial preprocessing time
  can answer queries in O(n^{O(1)} m^{1−ε} + m)" (Gabory, Thm 11); "Assuming the OMv
  conjecture, one cannot preprocess ... and answer active-prefix queries ... in
  O(m^{2−ε}) time" (Gabory, Thm 16).
- **3SUM.** Kopelowitz–Pettie–Porat (SODA 2016): "new reductions from 3SUM to pattern
  matching problems"; also "Any static data structure for SetDisjointness that answers
  queries in constant time must spend Ω(N^{2−o(1)}) time in preprocessing".
- **APSP:** no text-indexing bound found. **UNVERIFIED absence.**

Note the pattern: **every conditional *indexing* bound above concerns a harder object or
query than exact matching on one string** — graphs, degenerate strings, approximation,
active-prefix queries. Exact string indexing has an `O(m + occ)` index and is conditionally
hard only in preprocessing.

## 3. For `r`-space indexes: nothing (OPEN)

**Plainly: no theorem of the form "count/locate in time `t` needs space `s`" is known for
`O(r)`-size indexes** — no impossibility, no separation between `O(r)` and `O(n)`.

The §1 bounds are of two shapes, and neither reaches the `r`-index:

1. **Indexing/systematic**: text stored verbatim, only text probes charged (DLO;
   Gál–Miltersen; Golynski's rank/select). The `r`-index stores **no text**, so it is
   outside the model; and these bounds are on *redundancy over the text's information
   content*, which a `o(n)`-bit structure is not an instance of.
2. **Hard instances are incompressible** — a Kolmogorov-random permutation (DLO),
   Reed–Solomon-like polynomial evaluation (Gál–Miltersen), random points (Pătraşcu). There
   `r = Θ(n)`, so restated in `r` they cannot separate `O(r)` from `Θ(n)`.
   **MY-INFERENCE**; settle it by computing the run count of the DLO witness text.

The only lower bound in the repetitiveness-measure world is about *encoding*: Kociumaka–
Navarro–Prezza (arXiv 1910.02151) prove "there are string families needing
`Ω(δ log(n/δ))` space to be encoded, so this space is optimal for every n and δ". **No
analogue is known for `r`.** Navarro's survey (ACM CSUR 2021) lists its open challenges as
practicality and construction — a space lower bound is not among them. **UNVERIFIED
absence**; settles only through the compressed-indexing community, not metadata search.

## 4. What "space-optimal" would require

Natural statement (**MY-INFERENCE**):

> Cell probe, word size `w = Θ(log n)`, space `S` words, query = count (or report the
> `j`-th). For every `n` and `r` there is a text of length `n` whose BWT has `r` runs such
> that any structure answering in time `m + occ` uses `S = Ω(r)` words.

Obstacles:

- **Counting starves.** A bound needs answers that are hard to predict; small `r` means a
  highly periodic text, so answers are nearly forced by a short description — exactly where
  communication/Kraft arguments give nothing.
- **Parameterised bounds barely exist.** Cell-probe bounds are stated in the data's size,
  not in a combinatorial parameter of it. A bound in `r` would be the first of its kind.
- **The cost is text reconstruction.** The `r`-index spends LF-steps over a compressed
  BWT — neither probes to a stored text nor comparisons, so neither the indexing model nor
  a decision tree measures it.
- **The frontier moves** under Toehold/move-structure improvements; a matching bound must
  survive each. Trivial only: `t ≥ m`, `t ≥ occ`, `S ≥ log₂(#texts with r runs)` — all met.

## 5. Why the decision-tree bounds do not apply

The repository's frame is `#outcomes ≤ b ^ #steps` (`Core.Branching`); here it is vacuous,
for two independent reasons.

**Wrong outcome set.** For a count query the outcome is a number in `[0, n]`, so the frame
gives `t ≥ log_b(n+1)`. Its power came from `N = n!` orderings; an index need not
distinguish orderings, only answer *matching* questions about a **fixed, preprocessed**
input.

**Wrong charged resource.** Cell probe: "the running time is defined to be equal to the
number of memory probes; any computation inside the CPU is free" (Pătraşcu). DLO allow
"an arbitrary amount of computation ... on an arbitrary amount of the index". Comparison
counting bounds steps *through the data*; here the index is read freely and only probes to
the text are bounded. The meaningful inequality is `space × probes` — **succinctness** — a
different inequality from `#outcomes ≤ b^steps`.

What transfers: the discipline (name the model and the parameter; say what "optimal"
quantifies over), and the counting fact that reporting `occ` occurrences costs `Ω(occ)` —
why no `Ω(m log n)` statement for locate is even true.

## The three lower bounds that would settle it

1. **A parameterised cell-probe bound for count/locate in `O(r)` space**, e.g.
   `S·t = Ω(r·m)`. *Why hard:* needs hard instances with `r ≪ n`, but small `r` is a
   low-entropy object, and every technique in §1 is fuelled by incompressibility. It would
   be the first cell-probe bound in a data-dependent parameter.
2. **`Ω(r)` words for `O(m + occ)` locate.** *Why hard:* must defeat all index families,
   not just BWT-based ones, and show run structure is essentially the only compressibility
   that supports locate; nothing phrased over a parameter of the text exists to build on.
3. **A non-systematic lower bound for exact substring search.** Gál & Miltersen name the
   gap: "We don't know how to prove similar lower bounds for natural storage and retrieval
   problems such as Substring Search." *Why hard:* their proofs run through an
   error-correcting-code property; substring search hides no such code, because occurrences
   overlap and the text is self-referential. This is the obstruction blocking (1) too.
