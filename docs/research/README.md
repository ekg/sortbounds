# Research threads: compressed text indexing

Two independent questions, deliberately separated because they are different *kinds*
of question:

## Thread S — space (`space.md`)

Is `r` (BWT runs) the right measure, and how small can a pattern-matching index be?
This is a question about a **measured hierarchy** (`δ ≤ γ ≤ r`, `z`, `g`, `e`) and
about whether any *index* attains the smallest measure.  The mathematical content is
combinatorial and, for the inequalities, possibly formalizable.

Key sub-questions: the proved relations and their separations; whether `O(r)` space
is optimal (is there *any* lower bound?); whether an `O(γ)`- or `O(δ)`-space index with
fast queries exists; where the `σ` term lives (additive in space, or inside
`log log_w(σ + n/r)`).

## Thread T — time (`time-*.md`)

Given a space budget, how fast can queries be, and what is the trade-off frontier?

* `time-1-query-times.md` — the exact state of the art in `O(r)` space (`r-index`,
  Toehold refinement, move structures, OptBWTR, post-2021 results).
* `time-2-tradeoffs.md` — the knobs that buy time with space (sampling rates, dense vs
  sparse `move`, storing `φ`), and the shape of the Pareto frontier between `O(r)` and
  `O(n)`.
* `time-3-lower-bounds.md` — what is actually **impossible** (unconditional and
  conditional), and why no lower bound is known for `r`-space indexes.
* `time-4-grammar-attractor.md` — the small-space end: query times at `O(γ)` and
  `O(δ)` space, i.e. the price of saving space.
* `time-5-practice.md` — where the time actually goes (Move-r, MONI, construction cost,
  constants that the asymptotics hide).

## Status

| file | thread | state |
| --- | --- | --- |
| `space.md` | S | done — hierarchy, separations, δ-optimal space, σ term, lower bounds |
| `time-1-query-times.md` | T | done — exact `O(r)` bounds (OptBWTR Thm 9), and it *falsified* an `O(m)`-count claim |
| `time-2-tradeoffs.md` | T | done — 11 knobs, frontier table, and it *corrected* `O(r+n/s)` (rlfm, not r-index) and the role of `s` |
| `time-3-lower-bounds.md` | T | done — Demaine–López-Ortiz, Gál–Miltersen gap, no `r`-space bound |
| `time-4-grammar-attractor.md` | T | done — `O(γ log(n/γ))` and δ-optimal times, plus matching δ-space lower bounds for SA/LF/Φ |
| `time-5-practice.md` | T | done — measured numbers (13.1 MiB / 629 MB DNA; construction dominates) |
| `SYNTHESIS.md` | both | the answer, with corrections to what the supervisor had asserted |

Five of the six briefs corrected either a claim of mine or a claim of a sibling. That is
the point of the arrangement: the briefs are evidence, the synthesis is judgement.

## Why this belongs next to a sorting-lower-bounds repository

The `sortbounds` development is about **time** lower bounds in a decision model
(bits per probe).  Compressed indexing asks **space** questions about set/matching
queries, where the natural lower bounds are cell-probe or conditional — so the existing
machinery gives *nothing* here directly.  What transfers is the discipline: name the
model, name the parameter (`r`, `γ`, `δ`, `σ`), and say what "optimal" quantifies over.
The one genuinely formalizable overlap is the measure hierarchy in thread S, which is
elementary combinatorics over explicit definitions (attractor, SLP, BWT runs).
