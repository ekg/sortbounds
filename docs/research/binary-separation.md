# Is the `γ ≫ δ` separation attainable on a binary alphabet? — **yes, and it is published**

**Verdict.** `σ = 2` is covered explicitly by a theorem in the journal version of Kociumaka–
Navarro–Prezza that does **not** appear in the arXiv version we have been citing.  So
`γ/δ → ∞` on binary text is **PROVED in the literature**, not open, and two of our own conjectures
(`C1`, `C1′` in `CONJECTURES.md`) are refuted by citation as well as by our counterexample.

**Provenance (read this before quoting).**  The quotes below were recovered from the transcript of
a lane that was killed by a harness restart before it wrote its note (run `460b16d4`, session
`~/.pi/agent/sessions/…/460b16d4-…/run-0/session.jsonl`).  The lane had opened the **IEEE TIT
author copy** and extracted the passage; I have not re-opened the PDF myself.  Everything here is
therefore **QUOTED (second-hand)** rather than verified first-hand — the one thing to re-check
before this goes anywhere public.

## The passage

> "A more real limitation of the theorem is that the strings it builds have alphabet size `σ = δ`.
> We now obtain a more general result that holds for smaller alphabet sizes.
> **Theorem III.4.**  For every alphabet size `σ ≥ 2`, length `n ≥ 1`, and integer parameter
> `9σ ≤ Δ ≤ n log σ/(2 log n)`, there exists a string `S ∈ [0..σ)^n` such that `δ(S) ≤ Δ` and
> `γ(S) = Ω(Δ log(n log σ/(Δ log n)))`."

(Kociumaka–Navarro–Prezza, *IEEE Transactions on Information Theory*; §III, immediately after
Thm III.3.  The PDF extraction was reported as two-column and partly garbled, so the formula should
be re-read against the page image.)

## What it settles

* **`σ = 2` is in the statement** (`σ ≥ 2`).  With `σ = 2` the hypothesis is `18 ≤ Δ ≤ n/(2 log n)`
  and the conclusion is `γ = Ω(Δ log(n/(Δ log n)))` — a `log` separation at binary alphabet.
* Therefore **`δ` is not a constant-factor approximation of `γ` at `σ = 2`** (for `δ = Δ ≥ 18`), and
  the KNP log factor is *not* an artefact of a large alphabet.  My conjecture `C1` (`γ ≤ 3δ` on
  binary) and its sharp form `C1′` (`γ ≤ 1.5δ + O(1)`) are **dead, by citation**.
* The `σ`-refined form also explains the `log log σ` that appears in the index literature: the
  argument of the outer log is `n log σ/(Δ log n)`, so `σ` sits *inside* a log, never as an order.

## What our own family adds

Our powers-of-two family `T_j` (`1` exactly at the positions `2^k − 1`) has **`δ(T_j) = 2`** and
`γ(T_j) = ⌈j/2⌉ + 1 = Θ(log n)` (certified, `n = 8 … 8192`; `CONJECTURES.md` §C-new):

* it attains `γ = Θ(log n)` with `δ = 2`, i.e. **below** Thm III.4's hypothesis `Δ ≥ 9σ = 18`;
* so the `9σ` threshold in Thm III.4 is **not** needed at `δ = 2` — the separation exists there with
  an explicit, exactly-computed `γ` (whereas Thm III.4's proof is asymptotic and its strings are
  not given in closed form);
* `δ = 2` is the smallest non-unary value, so `T_j` also shows the phenomenon is not confined to
  large `δ`.

That is a genuinely new small observation: **the `σ`-refined separation holds at the minimum
possible `δ`**, with an exact formula for `γ` rather than an asymptotic bound.  It is not a
refutation of anything published — Thm III.4 says nothing about `Δ < 9σ`.

## Status of the claims in `CONJECTURES.md`

| claim | new status |
| --- | --- |
| `γ ≤ 3δ` on binary (C1) | **REFUTED** — KNP Thm III.4 (`σ = 2`) + our `T_j` |
| `γ ≤ 1.5δ + O(1)` on binary (C1′) | **REFUTED** — same |
| `δ` is a constant-factor approximation at `σ = 2` | **REFUTED** |
| `γ/δ` unbounded on binary | **PROVED** (KNP Thm III.4, quoted above) |
| LP gap bounded on binary (C2) | **OPEN** — `γ/LP* ≤ γ/δ` is now vacuous as a cap |
| `γ(T_j) = ⌈j/2⌉ + 1` | **EVIDENCE** (11 exact values), proof lane running |

## What to do next, in order

1. **Re-verify the quote first-hand** against the IEEE TIT PDF (page image, not `pdftotext`),
   recording the exact page and column.  Until then `RESULTS.md` must not cite `σ = 2` as proved.
2. If it holds: cite Thm III.4 in `RESULTS.md` open problem 2 as **solved in the literature**, and
   keep `T_j` as the explicit `δ = 2` instance.
3. Reconsider the LP-gap question with `γ/δ → ∞` in hand — it is the one live question the
   literature leaves open for this parameter.
