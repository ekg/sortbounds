# Lane: gamma-delta-growth — can `γ − δ` grow on *binary* text?

**Why this is now the central question.**  `docs/research/RESULTS.md`, open problem 2.  Two facts
pin it:

* `δ ≤ γ` (theorem, `Repetitiveness.deltaQ_le_minAttractorSize`) and `γ = O(δ log(n/δ))` in general
  (KNP23 via `z`).  KNP Thm III.3 gives `γ = Ω(δ log(n/δ))` for every `n` and `δ` — but over a
  **general** alphabet; the counting argument is not obviously binary.
* Every exhaustive measurement on **binary** text has `γ − ⌈δ⌉ ≤ 2` for `n ≤ 18`, and `3` at
  `n = 32` (`Packing.s32_gamma`/`s32_delta`, kernel-checked).

If `γ − δ` stays bounded on binary, then `δ` — computable in `O(n)` — is a constant-factor
approximation of `γ` at `σ = 2`, and (with `LP* ≥ δ`, `gamma_div_primal_le`) the LP gap is bounded
too.  If it grows, both die.  **Nothing in the literature settles this and we have the tooling to
attack it.**

## Deliverable

A certified curve: for `n = 20 … 64` (or as far as the budget allows), the **maximum**
`γ(S) − ⌈δ(S)⌉` over binary strings, with

* `δ(S)` exact (`instance.Instance.delta`),
* `γ(S)` as a **closed bracket** `[lb, ub]` (`anytime.search`; `lb` from `δ` + packing, `ub` from a
  verified attractor) — report the gap only when `lb == ub`, otherwise report the interval,
* the text, so every row is reproducible.

and a **verdict**: does the maximum grow with `n`, stay flat, or is the search simply not finding
things (state which, with evidence).

## Search strategies to cover (in order)

1. **Random binary strings** filtered to small `δ` (rejection sampling: keep strings with
   `δ ≤ 3`), `n = 20..64`.  Cheap, and it probes the bulk.
2. **Structured inflation**: strings built to make *few* positions cover *many* factors — nested
   `u v u`, `u u^R`, separators (`u 0^m v`), low-period blocks with aperiodic insertions,
   prefixes of the Fibonacci and Thue–Morse words, and `S S` / `S S^R` of random `S`.
3. **Local search on γ itself**: start from the best instance found, mutate (swap a symbol,
   move a block), accept if `(γ_ub − ⌈δ⌉)` improves; keep every improvement.  γ's upper bound comes
   from `anytime.search`, the lower bound from packing — **never report `γ` from an open bracket.**

## Constraints

* stdlib only; `timeout` on every run; assert progress in every loop (a lane once lost 30 minutes
  to `sleep` polling — do not poll, write results incrementally to a JSON file after every `n`).
* `δ` and every bracket exact (`Fraction`); floats only in a clearly-labelled descriptive column.
* Reuse `tools/attractor` (`instance.py`, `anytime.py`); do not re-implement γ.
* Machine is loaded (14+ jobs from another lane); use **at most 6 workers**.

## Report

`docs/research/gamma-delta-growth.md`: the curve, the best instances with full data, the verdict,
and an explicit "what would settle it" section.  Also state clearly whether the observed maximum is
consistent with `γ − δ = O(1)` on binary, with `Θ(log n)`, or with "search too weak to tell".

## Log

* (empty)
