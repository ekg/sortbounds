# repmeter — what index does this text deserve?

A stdlib-only Python tool that measures the quantities which decide compressed-index
choice, and prints a **certified bracket** on the one you cannot compute.

No dependencies: `python3 tools/repmeter/measure.py --text "mississippi"` works anywhere
Python 3 runs.

## What it computes

| quantity | how | cost | exact? |
| --- | --- | --- | --- |
| `n`, `σ` | trivially | `O(n)` | yes |
| `r` | BWT runs, from a prefix-doubling suffix array | `O(n log² n)` | yes |
| `δ = max_k d_k/k` | `d_k = #{i : lcp[i] < k ≤ n − sa[i]}` (interval ownership), difference array | `O(n)` after SA+LCP | yes (as an exact fraction) |
| `\|Γ\|` | greedy attractor (cover the most uncovered factors) | `O(n·\|Γ\|)` | yes, but **not optimal** |
| `γ` | exhaustive subset search | exponential | only for `n ≤ 14` |
| bracket | `δ ≤ γ ≤ \|Γ\|` | — | yes (both ends proved) |

The point of the bracket: `γ` (the smallest attractor) is **NP-hard** to find, but `δ` is
computable in linear time and any verified attractor gives an upper bound, so
`[δ, |Γ|]` is a *proved* interval on `γ` — which is what an attractor-based index's space
depends on. `KNP Thm III.3` shows the interval can be a log factor wide, so it is reported
as a bracket, not as an answer.

## Commands

```sh
python3 tools/repmeter/measure.py --text "mississippi"          # one literal
python3 tools/repmeter/measure.py genome.fa                     # a file
python3 tools/repmeter/measure.py --gen fibonacci:20            # or thue-morse:K, random-binary:N:SEED
python3 tools/repmeter/measure.py --text "ababa" --json         # machine-readable
python3 tools/repmeter/check.py                                 # self-tests (must exit 0)
```

`--verbose` also dumps `d_k`, the BWT and `Γ`. `--crosscheck` runs the slow `O(n²)`/`O(n³)`
reference implementations. The greedy is budgeted (`--greedy-budget-seconds`, default 60;
`--max-greedy-n`; `--max-greedy-rounds`): when it exceeds the budget the tool prints
`Γ: not computed (budget)` and **withholds the bracket** rather than guessing.

## Measured (exact, this machine)

| input | `n` | `σ` | `r` | `δ` | `γ` | bracket |
| --- | --- | --- | --- | --- | --- | --- |
| `mississippi` | 11 | 4 | 9 | 4 | **4** (exhaustive) | `[4, 7]` |
| Fibonacci `F₂₀` | 6765 | 2 | **4** | 2 | — | `[2, 5]` |
| Thue–Morse `2¹⁶` | 65536 | 2 | 46 | 40960/12289 ≈ 3.3331 | — | `[3.33, 4]` |
| random binary | 4096 | 2 | 2061 | 3607/14 ≈ 257.6429 | — | `[257.64, 479]` |

Read it as the theory predicts: Fibonacci words are *extremely* compressible (`r = 4` at
`n = 6765`!), Thue–Morse likewise (`r = 46` at 65 k), while random binary text has
`r ≈ n/2` and `δ ≈ n/16` — no compressibility, and no index will help. On `mississippi`
the greedy gives `|Γ| = 7` against the true `γ = 4`, which is the bracket doing its job
and admitting it is loose.

Implied index sizes (words, from `docs/research/SYNTHESIS.md`): an `O(r)`-space r-index is
`r` words — 4 for `F₂₀`; a δ-optimal structure is
`O(δ log(n log σ/(δ log n)))` words; on random text either is `Θ(n)` and you should not
bother.

## Self-tests

`check.py` cross-checks `δ` and `r` against **independent brute-force implementations**
(distinct factors by explicit `set`, BWT by sorting all rotations) on all binary strings of
length ≤ 12, checks the greedy attractor with a **separate** verifier that re-implements
the attractor definition (not the greedy's bookkeeping), and asserts that a budgeted run
reports "not computed" instead of hanging. Last run:

```
196487 checks, 0 mismatches, 9.1s
OK
```

## What this does not do

* **No `γ` beyond `n ≤ 14`** — it is NP-hard (ESA'18: finding the smallest `k`-attractor is
  NP-hard; NP-complete for `k ≥ 3`). No approximation is used here, so `|Γ|` is *an* upper
  bound, not an approximation with a ratio.
* **No `g`** (smallest grammar) and no `z` (LZ77) — also NP-hard / not implemented.
* **No index.** This measures; it does not search. Any index built from these numbers is
  future work — the r-index family is the target, and the frontier table in
  `docs/research/SYNTHESIS.md` says what space/time to expect.
* **The suffix array is prefix doubling**, not SA-IS: fine at 10⁵–10⁶, not at 10⁹. The
  predicted sizes are asymptotic *word counts*, not measured bytes.
* `σ` is byte-based for files, so a UTF-8 text reports bytes, not code points.
