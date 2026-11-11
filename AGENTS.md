# AGENTS.md — working agreement for this repository

Read this before doing anything here. It overrides default caution about
stopping early.

## Autonomy

**Do not wait for the operator to say "continue".** `docs/PROGRESS.md` lists the
queue. Take the next item, start it, and keep going. Report progress in short
bursts; then pick up the next item. If you finish the queue, extend it with the
highest-value true statement you can find and say why — do not idle.

Ask only when a decision is irreversible and outside the repository (publishing
claims about other people's work, deleting history, spending money).

## Long-running work

* **Never use a 30-minute cap.** Subagent launches must pass an explicit
  `timeoutMs`: `14400000` (4 h) for implementation lanes and
  `21000000` (5 h 50 m) for anything that rebuilds or searches. Multi-hour work
  is normal here; a lane that runs for two hours and lands one theorem is a
  success.
* Run lanes **in the background** (`async`, or a `workflows/*.js` script via
  `runs.lanes`) so the operator can interject. Never block the session on a
  long child.
* A timed-out lane is a failure of the harness, not of the work: inspect the
  partial files before retrying, and finish the last open goal yourself if it is
  small.

## Fan-out shape

One directory per lane, one namespace per lane, one writer per directory
(`docs/STRUCTURE.md`). Lanes may run for hours; they must not touch
`SortBounds/Core`, `SortBounds/Comparison`, `SortBounds/Instances`, the umbrella
`SortBounds.lean`, `docs/PROGRESS.md`, or each other.

* Only the integrator runs `lake build` and `git`. Lane workers use
  `lake env lean <file>` (no oleans written, no build races).
* Every lane gets a **fresh-context reviewer** as its second stage. Reviewers
  exist because they have caught real errors the kernel cannot: a false prose
  claim about `Ω(n² log n)` and a vacuity gap in a model's semantics.
* `make check` must stay green: the compiler's own `declaration uses 'sorry'`
  warning plus a source grep for `axiom`/`native_decide`. No `sorry`, no
  `admit`, no `axiom`.

## Truth discipline

The kernel checks proofs, not claims. For every result, ask:

1. **Is the statement the thing we mean?** (Depth vs. input-attained cost;
   `S n` = min depth vs. min worst-case `cost`; "comparison-free" as `rfl` vs.
   genuine independence of the oracle.)
2. **Is it vacuous?** Exhibit a witness for every hypothesis that matters.
3. **Does the prose claim more than the theorem says?** Quote the theorem when
   writing the prose.
4. **Is it already done elsewhere?** Check `docs/PRIOR-ART.md` before starting a
   lane; two ideas already died that way (0-1 principle, verified SA-IS).

## Where things live

`docs/PROGRESS.md` (dashboard, single editor) · `docs/STRUCTURE.md` (layout and
parallel-work rules) · `docs/PRIOR-ART.md` (who else has done what) ·
`SortBounds/Projects/<Lane>/README.md` (the lane's contract).
