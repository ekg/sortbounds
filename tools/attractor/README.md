# attractor — an anytime search for small string attractors

`r` is solved and `χ` (suffixient sets) is what `pangenome/sxgc` already exploits.
The measure that would *improve a grammar* is `γ`, the smallest string attractor
(an attractor of size `c` yields an RLSLP of size `O(c log(n/c))`). `γ` is NP-hard,
so the only honest interface is:

    report a certified bracket  [LB, UB]  and improve both ends with more budget.

## The exact reduction (no loss)

Minimum attractor **is** minimum set cover:

* universe  = distinct nonempty factors of `S`;
* for each position `p`, the set `cover(p)` = factors having an occurrence crossing `p`;
* `Γ` is an attractor ⟺ `⋃_{p∈Γ} cover(p)` = universe.

Consequences used by the tool: greedy gives `O(log U)`; any `Γ` is verifiable in one
pass (`check` from `tools/repmeter`); and the LP/dual and packing bounds are lower
bounds on `γ`.

## Two certified ends

* **UB** — an explicit set of positions, verified by an *independent* checker
  (every distinct factor has an occurrence crossing `Γ`). Monotone: the tool only
  accepts a new `Γ` that is strictly smaller.
* **LB** — the maximum of:
  1. `δ` = `max_k d_k/k` (KNP: `δ ≤ γ`), computed exactly from SA/LCP;
  2. a **packing bound**: factors `f_1..f_k` such that no position covers two of them
    ⇒ `γ ≥ k`. Certified by exhibiting the factors and the incompatibility.
  3. (optional) a validated LP-dual bound if you implement one — must come with a
     checkable dual solution, never a solver's word.

## Any-time schedule (each step only ever improves)

1. **Greedy**: repeatedly take the position covering the most uncovered factors.
2. **Irredundant prune**: drop any position whose removal keeps the cover.
3. **Local search**: try `1↔1` swaps (move a position, re-cover, prune) and
   `2↔1` replacements; accept only strict improvements.
4. **Exact tail**: iterative deepening over `k = LB, LB+1, …` deciding "is there an
   attractor of size ≤ k" by DFS/SAT with the packing and `δ` pruning. This is only
   run while `k ≤ |Γ|` and the budget allows.
5. Every accepted `Γ` is printed with a timestamp, its size, and the current bracket.

## Contract

```python
# instance.py
class Instance:
    def __init__(self, text): ...          # from SA+LCP; elements are SA-intervals
    def uncovered(self, gamma) -> int      # how many distinct factors are uncovered
    def verify(self, gamma) -> bool        # INDEPENDENT definition-level check
    def delta(self) -> Fraction            # exact substring complexity
    def packing_bound(self) -> tuple[int, list]   # (k, witness factors)

# anytime.py
def search(inst, budget_s=60.0, seed=0) -> Iterator[dict]
    # yields {"t":…, "gamma":[…], "ub":…, "lb":…} on every improvement, and at the end
```
**Acceptance tests** (must be in `check.py`, must exit non-zero on failure):
1. For every binary string of length ≤ 12: `verify` accepts the greedy result, and for
   `n ≤ 12` the *exact* `γ` (exhaustive) is bracketed by `[lb, ub]`.
2. On `"mississippi"` the exact `γ = 4` and the tool's search reaches 4 within budget.
3. On the Thue–Morse family the packing bound must exceed `δ` at some `n` (that is the
   whole point of a second lower bound) — if it never does, say so honestly instead of
   faking it.
4. `search` never yields a *larger* `Γ` than a previous yield (monotonicity), and never
   yields an unverified one.

## Rules

stdlib only; `timeout` every run; assert progress in every loop (a loop that does not
strictly improve must terminate).  No number printed without either a proof-shaped
certificate (`δ`, packing) or an explicit "not computed".  This directory is Python
tooling; the Lean side is `SortBounds/Projects/Repetitiveness`.
