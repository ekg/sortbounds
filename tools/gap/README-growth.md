# Lane: gap-growth — is the attractor LP gap bounded?

**State of knowledge.** `../docs/research/lp-gap.md`: the exact maximum of `γ/LP*` over **all**
binary strings is `1` (n≤6), `6/5` (n=7), `9/7` (n=8..11), `4/3` (n=12), `15/11` (n=13),
`4/3` (n=14..16) — exhaustive, exact rationals.  `15/11` is now a kernel-checked theorem on its
instance (`SortBounds/Projects/AttractorLP/`).  Whether the maximum is bounded is **open**, and it
is the pivot of the programme: bounded ⇒ an `O(1)`-ratio algorithm must exist via rounding;
unbounded ⇒ the LP route is dead and `log`-factor behaviour is inherent for LP methods.

**Your job: extend the measurement past n = 16 with certificates, and characterise the growth.**

## Deliverables (in this order)

1. **Exhaustive `n = 17`** if it finishes in budget with the existing exact simplex and node
   universe.  Report the maximum gap, its witnesses, and the wall time.  If it does not finish,
   say so with the measured per-instance cost — negative results with numbers are deliverables.
2. **Targeted search `n = 17..40`** (the exhaustive maximum is a special case; a search is what
   extends the range): start from the four `n = 13` witnesses, extend by one symbol at a time
   (`000`/`111`/`0`/`1` appended, and prefix insertion), keep any instance whose gap exceeds
   `15/11` exactly (rationals, never floats).  Also run: random strings with low `δ` (repetitive
   shapes: `1^a 0^b 1^c 0^d …`, powers, Fibonacci/Thue–Morse prefixes, `S S`, `S S^R`,
   `S 0^m S`), because the `n = 13` witness's fractional structure is "short repeated factors".
3. **The growth verdict.**  Is the observed max consistent with a limit, with `log n`, or with
   `n^{1/4}`?  Give the curve and a **falsifiable** statement ("if bounded by `B`, then no instance
   with gap `> B` exists for `n ≤ N`, and I searched X instances").
4. **A certificate for every claimed gap.**  Any instance reported with gap `g > 1` must carry
   (i) `γ` exact and its witness attractor, (ii) `x` primal feasible with `Σx = LP*`, (iii) `y`
   dual feasible with `Σy = LP*`, both as **rational vectors printed in full**.  This is what makes
   the finding formalizable, which is the point.

## Constraints

* stdlib only; `timeout` on every run; assert progress in every loop (no silent hangs).
* exact `Fraction` arithmetic for every reported number; floats only in a clearly-labelled
  descriptive column.  Reuse `simplex.py`, `instance.py`, `gap.py` — do not re-implement the LP.
* Re-verify each reported witness independently of the solver (feasibility by direct summation),
  and print the check.  A gap claim without a re-verified certificate is to be discarded.
* Do not claim a maximum you did not exhaust.  "Searched, not exhausted" must be stated for
  everything above `n = 16`.

## Report

`../docs/research/lp-gap-growth.md`: the curve (with `n`, exhaustive/searched, max gap, witness
text), the certificates for any improved instance, the verdict, and a short "what would settle it"
section.  Update `../docs/research/lp-gap.md` with a pointer.  Do not modify `grep.py`/
`simplex.py` semantics; add new files.

## Log

* (empty)
