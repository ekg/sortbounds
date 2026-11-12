# Lane: Algorithms — make the object executable, then build the first real algorithm

**The gap.** `Projects/Repetitiveness` proves facts *about* `δ` and attractors, but
nothing in that lane can be run: `distinctFactors`, `substringComplexity` and
`minAttractorSize` all carry `noncomputable`, so `#eval δ "mississippi"` is impossible.
(Evidence they are *needlessly* noncomputable: `example : distinctFactors ['a','b','a'] 2 =
{['a','b'],['b','a']} := by decide` elaborates, i.e. the kernel evaluates them.)
Theory without an executable is a description of an algorithm, not an algorithm.

**So: two jobs.**

## Job 1 — executable measures (M0)

```lean
/-- `δ` computed directly from the definition, without `Classical`. -/
def deltaCompute (s : List α) : ℕ
theorem deltaCompute_eq (s : List α) : deltaCompute s = delta s

/-- The greedy attractor as a program, and its size. -/
def greedyAttractorCompute (s : List α) : Finset (Fin s.length)   -- if the existing one is noncomputable
theorem greedyAttractorCompute_eq (s) : greedyAttractorCompute s = greedyAttractor s
```
plus `#eval`-checked demos on `"mississippi"`, `"ababa"`, a Fibonacci word, and a
`decide`-checked agreement with brute force on all strings over `{a,b}` of length ≤ 6.

## Job 2 — the first real algorithm: suffix array, then BWT, then `r` (M1)

`r` (BWT runs) is the measure that decides index choice in practice, and computing it needs
a suffix array.  Do the **correct, slow** version first — it is ~30 lines given the library:

```lean
/-- Suffixes in lexicographic order, as positions. -/
def suffixArray (s : List α) : List ℕ
theorem suffixArray_perm (s) : (suffixArray s).Perm (List.range s.length)
theorem suffixArray_sorted (s) : (suffixArray s).Pairwise (fun i j => compare (suffix s i)
    (suffix s j) = Ordering.lt)   -- or the `IsSorted` form you can actually prove

def bwt (s : List α) : List α        -- last column, from the SA
theorem bwt_length (s) : (bwt s).length = s.length
def numRuns (s : List α) : ℕ         -- equal-letter run count of `bwt s`
```
Reuse `SortBounds.Projects.SAIS.{suffix, lcp}` and `List.mergeSort` — a comparison sort by
suffix order is `O(n² log n)` character work and that is *fine*: **this lane is about being
executable and correct, not fast.**  Say so in the docstring, and give the fast version
(SA-IS / prefix doubling) as the roadmap, not as a claim.

## Job 3 (only if 1–2 land) — the pipeline, end to end

```lean
/-- One entry point: measures of a text, all computed, with the certified bracket. -/
def measure (s : List α) : ℕ × ℕ × ℕ       -- (δ, |Γ_greedy|, r)
theorem measure_spec (s) : (measure s).1 = delta s ∧ (measure s).2.1 = (greedyAttractor s).card
                             ∧ (measure s).2.2 = numRuns s
```
so the repository can `#eval measure "…"` and print the three numbers the research briefs
say decide which index family suits a corpus.

## Rules

Own only `SortBounds/Projects/Algorithms/`.  `lake env lean`, no `lake build`, no git,
oleans in `/tmp`.  No `sorry`/`axiom`/`native_decide` (note: `native_decide` is forbidden
*even though* it would make the `#eval` demos fast — use `decide`/`#eval`, and keep the
examples small).  Do **not** claim a complexity you have not stated; if a function is
quadratic, say so in its docstring.  Do not weaken an existing declaration; add.

## Prior art

Suffix-array construction is SA-IS (Nong–Zhang–Chan 2009) / DC3 (Kärkkäinen–Sanders 2003);
Isabelle's AFP has verified SA-IS **correctness** (`SuffixArray`, 2024) — so SA-IS in Lean
would be a port, not a discovery, and this lane deliberately starts with the simple version.
`r` and the BWT-run measure: Gagie–Navarro–Prezza 2020.

## Log

* (empty)
