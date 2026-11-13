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

### 2025-11-13 — Jobs 1–3 landed (Compute.lean, SuffixArray.lean, Measure.lean, Texts.lean)

All four files elaborate cleanly (the plain `lake env lean` command works for `Texts.lean`; the other
three import their lane siblings, so they were validated with the `/tmp` recipe under "Validating"
below — no oleans were written into the repository).

**Job 1 — executable measures (`Compute.lean`).**

* `distinctFactorsCompute (s : List α) (k : ℕ) : Finset (List α)` with
  `distinctFactorsCompute_eq (s) (k) : distinctFactorsCompute s k = distinctFactors s k` — `rfl`
  (the `noncomputable` marker on `distinctFactors` was decoration; the same body elaborates and
  computes).
* `deltaCompute (s : List α) : ℕ` with `deltaCompute_eq (s) : deltaCompute s = delta s`.
* **No greedy twin was needed**: `Repetitiveness.greedyAttractor` is a plain `def`
  (`#eval (greedyAttractor ababa).card` prints `2`), so the contract's `greedyAttractorCompute` would
  have been an `rfl` alias.  Added instead `greedyAttractorSize (s) : ℕ := (greedyAttractor s).card`
  (the number the pipeline reports) and the computable sandwich
  `deltaCompute_le_greedyAttractorSize (s) : deltaCompute s ≤ greedyAttractorSize s ∧
  greedyAttractorSize s ≤ s.length`.
* **Brute-force check.**  `wordsOfLength (A) (k)` with `mem_wordsOfLength : w ∈ wordsOfLength A k ↔
  w.length = k ∧ ∀ a ∈ w, a ∈ A`; `bruteFactorCount (A) (s) (k)` (enumerate words, keep the ones
  occurring in `s` as a `List.IsInfix`, count as a set) with
  `bruteFactorCount_eq (A) (s) (k) (hA : ∀ a ∈ s, a ∈ A) : bruteFactorCount A s k =
  (distinctFactorsCompute s k).card` and the same against the definition
  (`bruteFactorCount_eq_distinctFactors`); `bruteDelta (A) (s)` (list-based `max`, independent of
  `Finset`); `mem_binaryWordsUpTo6` (the enumeration of all binary words of length ≤ 6 is
  *complete*); `bruteDelta_check_binaryUpTo6 : binaryWordsUpTo6.all (fun s => bruteDelta
  binaryAlphabet s == deltaCompute s) = true` by `decide`; hence
  `bruteDelta_eq_deltaCompute_of_length_le_six`.
* Numbers: `δ("mississippi") = 4`, `δ("ababa") = 2`, `δ(fibWord 6) = 2`, `|Γ_greedy
  ("mississippi") = 10` — the first, third and fourth by `decide` in the kernel
  (`deltaCompute_mississippi`, `deltaCompute_fibWord_six`, `greedyAttractorSize_mississippi`).

**Job 2 — suffix array, BWT, `r` (`SuffixArray.lean`).**

* `suffixLE (s) (i j) : Bool := decide (suffix s i ≤ suffix s j)` and
  `suffixArray (s) : List ℕ := (List.range s.length).mergeSort (suffixLE s)`
  (`O(n² log n)` character work — stated in the file header, not claimed better).
* `suffixArray_perm (s) : (suffixArray s).Perm (List.range s.length)`;
  `suffixArray_sorted (s) : (suffixArray s).Pairwise (fun i j => suffix s i < suffix s j)` (the
  strict `≤` form is `suffixArray_pairwise`); `suffix_injOn` (distinct positions have distinct
  suffixes, so there are **no ties** to break — the reason the strict statement loses nothing).
* `suffixArray_unique`: a permutation of `List.range s.length` that is pairwise increasing in suffix
  order *is* `suffixArray s`.  This is what makes concrete suffix arrays provable in the kernel:
  `List.mergeSort` is well-founded recursion, so `decide` cannot reduce `suffixArray`.
* `bwt (s) : List α` with `bwt_length (s) : (bwt s).length = s.length`, in the **wrap-around**
  convention (`s[n-1]` plays the sentinel's role, so the last column has the text's length, not
  `n+1`); `numRuns (s) : ℕ` with `numRuns_le_length` and `numRuns_pos`.
* Concrete values, *proved*: `suffixArray_mississippi`, `bwt_mississippi` (`pssmipissii`),
  `numRuns_mississippi : numRuns mississippi = 8`.  (The textbook BWT of `mississippi$` is
  `ipssm$pissii` with `9` runs; the difference is the sentinel row, and the file header says so.)
* Not attempted: `compare … = Ordering.lt` in the sorted statement.  `List α` has two `Ord`
  instances (core's `List.instOrd` and `List.instLinearOrder.toOrd`) and only the second has the
  bridge `compare_lt_iff_lt`; the statement is `suffix s i < suffix s j`, i.e. `Lex (· < ·)`.

**Job 3 — the pipeline (`Measure.lean`).**

* `measure (s) : ℕ × ℕ × ℕ := (deltaCompute s, greedyAttractorSize s, numRuns s)` with
  `measure_spec (s) : (measure s).1 = delta s ∧ (measure s).2.1 = (greedyAttractor s).card ∧
  (measure s).2.2 = numRuns s`, plus `measure_delta_le` and `measure_nil`.
* `measure_mississippi : measure mississippi = (4, 10, 8)`,
  `measure_ababa : measure ababa = (2, 2, 2)` — both proved.

**Validating (for the integrator).**  The lane's files import each other, so `lake env lean
SortBounds/Projects/Algorithms/Measure.lean` alone cannot resolve `Compute`/`SuffixArray`/`Texts`
until those are built.  `Texts.lean` (the only file with no lane imports) *does* validate with the
plain command.  For the others, oleans can be kept outside the repository like this — verified to
work from an empty `/tmp/algo-copy`:

```sh
SRC=/home/bot/sortbounds; BLD=$SRC/.lake/build/lib/lean; DST=/tmp/algo-copy
MB=$SRC/.lake/packages/mathlib/.lake/build/lib/lean
mkdir -p $DST/SortBounds/Projects/Algorithms $DST/SortBounds/Projects
ln -sfn $BLD/SortBounds/Projects/Repetitiveness $DST/SortBounds/Projects/Repetitiveness
ln -sfn $BLD/SortBounds/Projects/SAIS $DST/SortBounds/Projects/SAIS
for e in "$BLD"/*; do b=$(basename "$e"); [ "$b" = SortBounds ] || ln -sfn "$e" "$DST/$b"; done
for e in "$MB"/*;  do ln -sfn "$e" "$DST/$(basename "$e")"; done
cd $SRC
LEAN=$(lake env which lean)      # resolve BEFORE leaving the repo: /tmp has no lean-toolchain
                                 # and `lake env` there silently picks the default toolchain
                                 # (4.35.0, not 4.35.0-rc2) ⇒ "Init.olean incompatible header"
export LEAN_PATH="$DST:$(lake env printenv LEAN_PATH)"
for f in Texts Compute SuffixArray Measure; do
  cp $SRC/SortBounds/Projects/Algorithms/$f.lean $DST/SortBounds/Projects/Algorithms/
  ( cd $DST && "$LEAN" -o SortBounds/Projects/Algorithms/$f.olean \
      SortBounds/Projects/Algorithms/$f.lean ) && echo "OK $f"
done
```

(`/tmp/algo-copy` has to shadow every namespace prefix the lane imports, because Lean resolves a
module through the first `LEAN_PATH` root that contains its top-level directory.)  `lake build` by
the integrator, after adding the four imports below, is the real check.

**Integrator TODO.**  Add to `SortBounds.lean`, after the Repetitiveness imports:

```lean
import SortBounds.Projects.Algorithms.Texts
import SortBounds.Projects.Algorithms.Compute
import SortBounds.Projects.Algorithms.SuffixArray
import SortBounds.Projects.Algorithms.Measure
```

and add a `## Algorithms` row to `docs/PROGRESS.md`.  Nothing in this lane touches the umbrella, the
core directories, or any other lane.

**Not done / next.**  (i) `bwt_perm`: `bwt s` is a permutation of `s` (needs the modular-bijection
count, `(range n).map (fun j => (j + n - 1) % n) = s.rotateRight 1`); (ii) `bruteDelta` proved equal
to `δ` for *all* texts (today: the count `bruteFactorCount_eq` is general, the `max`-over-`k` step is
only `decide`d for binary words of length ≤ 6); (iii) an `O(n)`/SA-IS suffix array, which would also
make every concrete `#eval` here a `decide`.
