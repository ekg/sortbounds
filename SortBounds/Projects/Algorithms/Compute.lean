/-
SortBounds/Projects/Algorithms/Compute.lean

**Job 1 of this lane: the measures as programs.**

`Projects/Repetitiveness` proves facts *about* `d_k`, `δ` and the greedy attractor, but its
`distinctFactors` and `substringComplexity` carry a `noncomputable` marker, so
`#eval (distinctFactors s 2).card` and `#eval delta s` are rejected by the compiler
(`failed to compile definition … because it depends on 'distinctFactors', which is
'noncomputable'`).  The kernel *can* evaluate them — `example : (distinctFactors ababa 2).card
= 2 := by decide` elaborates — so the marker is an annotation, not a mathematical fact, and
this file gives the executable twin:

* `distinctFactorsCompute`, with `distinctFactorsCompute_eq s k : distinctFactorsCompute s k =
  distinctFactors s k`;
* `deltaCompute`, with `deltaCompute_eq s : deltaCompute s = delta s`.

The greedy construction needs **no** twin: `Repetitiveness.greedyAttractor` is a plain `def`
(no `noncomputable` marker), and `#eval (greedyAttractor ababa).card` prints `2`.  What is
added here is its *size* under a name, `greedyAttractorSize`, and the computable sandwich
`deltaCompute s ≤ greedyAttractorSize s`.

**How the twin is checked.**  Equality with the definition is one thing; that the definition
computes the intended number is another.  So `bruteFactorCount` recomputes `d_k` along a route that
shares no code with `distinctFactors` — it enumerates *all* words of length `k` over a given
alphabet (`wordsOfLength`) and keeps the ones that occur in `s` as an infix (`List.IsInfix`), with
no window constructed — and `bruteFactorCount_eq` proves that this count *is* `d_k` for any
alphabet covering the letters of `s`.  On top of that, `bruteDelta_eq_deltaCompute` shows that the
whole brute-force `δ` agrees with `deltaCompute` on **every** binary word of length at most `6`,
which is not a spot check on a hard-coded list: `mem_binaryWordsUpTo6` proves the enumeration
`binaryWordsUpTo6` contains *every* word over `{a,b}` of length `≤ 6` and nothing else, and
`bruteDelta_check_binaryUpTo6` (a kernel `decide` over that enumeration) is the agreement.
-/
import Mathlib
import SortBounds.Projects.Repetitiveness.Basic
import SortBounds.Projects.Repetitiveness.Attractor
import SortBounds.Projects.Repetitiveness.Measures
import SortBounds.Projects.Repetitiveness.Greedy
import SortBounds.Projects.Algorithms.Texts

namespace SortBounds.Projects.Algorithms

open SortBounds.Projects.Repetitiveness

variable {α : Type*} [DecidableEq α]

/-! ### `d_k` and `δ` as programs -/

/-- **`d_k` as a program**: the number of distinct length-`k` factors of `s`, computed by the
same expression as `Repetitiveness.distinctFactors` but without the `noncomputable` marker, so
that it can be `#eval`ed.  Cost: `n + 1` windows of length `k` are built and inserted into a
`Finset`, i.e. `O(n k log n)` character work and `O(n k)` space in the worst case — this is
the definition, not KNP's linear-time algorithm. -/
def distinctFactorsCompute (s : List α) (k : ℕ) : Finset (List α) :=
  ((Finset.range (s.length + 1)).filter (fun i => i + k ≤ s.length)).image
    (fun i => (s.drop i).take k)

/-- The twin is the same set as the `noncomputable` definition: same starts (`i + k ≤
s.length`), same window (`(s.drop i).take k`). -/
theorem distinctFactorsCompute_eq (s : List α) (k : ℕ) :
    distinctFactorsCompute s k = distinctFactors s k := rfl

/-- Membership in the computable `d_k`, in the form the brute-force check uses. -/
theorem mem_distinctFactorsCompute {s : List α} {k : ℕ} {f : List α} :
    f ∈ distinctFactorsCompute s k ↔ ∃ i, i + k ≤ s.length ∧ (s.drop i).take k = f := by
  rw [distinctFactorsCompute_eq]
  exact mem_distinctFactors

/-- **KNP's `δ` as a program**: `max { d_k / k : 1 ≤ k ≤ n }` (`delta` in `Measures.lean`), with
the computable `d_k`.  Cost: one `distinctFactorsCompute` per `k ≤ n`, i.e. `Σ_{k ≤ n} O(n k log n)
= O(n³ log n)` character work — cubic, and the *definition*: KNP's linear-time algorithm is not
implemented here. -/
def deltaCompute (s : List α) : ℕ :=
  (Finset.Icc 1 s.length).sup (fun k => (distinctFactorsCompute s k).card / k)

/-- **`deltaCompute` computes `δ`.** -/
theorem deltaCompute_eq (s : List α) : deltaCompute s = delta s := by
  show deltaCompute s = substringComplexity s
  simp only [deltaCompute, substringComplexity, distinctFactorsCompute_eq]

/-- The computable `δ` is at most the length, inherited from `delta_le_length`. -/
theorem deltaCompute_le_length (s : List α) : deltaCompute s ≤ s.length := by
  rw [deltaCompute_eq]
  exact delta_le_length s

/-! ### The greedy attractor's size -/

/-- **`|Γ_greedy|`**: the size of the computable attractor of `Greedy.lean`, i.e. the certified
upper bound on `γ`.  `greedyAttractor` already *is* a program (`#eval (greedyAttractor ababa).card`
prints `2`), so this is not a twin — it is the one number the measure pipeline reports, under
a name. -/
def greedyAttractorSize (s : List α) : ℕ := (greedyAttractor s).card

theorem greedyAttractorSize_eq (s : List α) :
    greedyAttractorSize s = (greedyAttractor s).card := rfl

/-- **The computable sandwich `δ ≤ |Γ_greedy| ≤ n`**: both ends of the certified interval are
now runnable.  The middle number `γ` is the one that is NP-hard to compute
(`Measures.lean`:114) and is *not* evaluated here. -/
theorem deltaCompute_le_greedyAttractorSize (s : List α) :
    deltaCompute s ≤ greedyAttractorSize s ∧ greedyAttractorSize s ≤ s.length := by
  refine ⟨?_, greedyAttractor_card_le_length s⟩
  rw [deltaCompute_eq, greedyAttractorSize_eq]
  exact delta_le_greedyAttractor_card s

/-! ### An independent brute-force check of `δ`

The definitions above say what `δ` *is*; the theorems below check that it is the intended number,
by recomputing it along an unrelated route.  `d_k` is counted by enumerating every word of length
`k` over a given alphabet and asking which of them occur in the text as an infix; no window is
built and `distinctFactors` is not used (only the deduplication of the filtered list is a
`List.toFinset`). -/

/-- All words of length `k` over the alphabet `A` (each letter of `A` at each position). -/
def wordsOfLength (A : List α) : ℕ → List (List α)
  | 0 => [[]]
  | k + 1 => (wordsOfLength A k).flatMap fun w => A.map fun a => a :: w

omit [DecidableEq α] in
/-- `wordsOfLength A k` is exactly the set of length-`k` words over `A` — the lemma that makes
the brute force below a *complete* check rather than a spot check. -/
theorem mem_wordsOfLength {A : List α} {k : ℕ} {w : List α} :
    w ∈ wordsOfLength A k ↔ w.length = k ∧ ∀ a ∈ w, a ∈ A := by
  induction k generalizing w with
  | zero =>
    simp only [wordsOfLength, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl
      exact ⟨rfl, by simp⟩
    · rintro ⟨h0, -⟩
      exact h0
  | succ k ih =>
    simp only [wordsOfLength, List.mem_flatMap, List.mem_map, ih]
    constructor
    · rintro ⟨v, ⟨hlen, hv⟩, a, ha, rfl⟩
      refine ⟨by simp [hlen], ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hv b hb
    · rintro ⟨hlen, hall⟩
      cases w with
      | nil => simp at hlen
      | cons a v =>
        exact ⟨v, ⟨by simpa using hlen, fun b hb => hall b (by simp [hb])⟩, a,
          hall a (by simp), rfl⟩

/-- Is `f` a factor of `s`?  Decided by `List.IsInfix` on the whole word — no window is built,
so this shares no code with `distinctFactors`. -/
def isFactorOf (f s : List α) : Bool := decide (List.IsInfix f s)

/-- The number of distinct length-`k` factors of `s`, by brute force over the alphabet `A`:
enumerate every word of length `k` over `A`, keep the ones that occur in `s` as an infix, and count
them — as a set (`List.toFinset`), so that repetitions in `A` cannot inflate the count.  Correct as
a count of `d_k` when every letter of `s` lies in `A` (`bruteFactorCount_eq`). -/
def bruteFactorCount (A : List α) (s : List α) (k : ℕ) : ℕ :=
  ((wordsOfLength A k).filter (fun w => isFactorOf w s)).toFinset.card

omit [DecidableEq α] in
/-- A word that is an infix of `s` is the length-`k` window `(s.drop i).take k` at some start `i`.
This is the bridge from "occurs in `s`" to "is a factor at position `i`". -/
theorem exists_window_of_isInfix {w s : List α} (h : List.IsInfix w s) (k : ℕ)
    (hk : w.length = k) : ∃ i, i + k ≤ s.length ∧ (s.drop i).take k = w := by
  obtain ⟨a, b, rfl⟩ := h
  refine ⟨a.length, by simp; omega, ?_⟩
  rw [List.append_assoc, List.drop_left, ← hk, List.take_left]

omit [DecidableEq α] in
/-- Every window `(s.drop i).take k` — truncated or not — is an infix of `s`. -/
theorem isInfix_window {s : List α} (i k : ℕ) : List.IsInfix ((s.drop i).take k) s := by
  refine ⟨s.take i, (s.drop i).drop k, ?_⟩
  rw [List.append_assoc, List.take_append_drop k (s.drop i), List.take_append_drop i s]

/-- **The brute force counts `d_k`**: for an alphabet `A` that covers the letters of `s`,
enumerating the words of length `k` over `A` and keeping those that occur in `s` gives exactly the
length-`k` factors of `s`, so it counts `d_k`.  The hypothesis is not vacuous — it holds for `{a,b}`
on every binary word, which is the check below. -/
theorem bruteFactorCount_eq (A : List α) (s : List α) (k : ℕ) (hA : ∀ a ∈ s, a ∈ A) :
    bruteFactorCount A s k = (distinctFactorsCompute s k).card := by
  rw [bruteFactorCount]
  congr 1
  ext f
  simp only [List.mem_toFinset, List.mem_filter, mem_wordsOfLength, mem_distinctFactorsCompute,
    isFactorOf, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hlen, -⟩, hinfix⟩
    exact exists_window_of_isInfix hinfix k hlen
  · rintro ⟨i, hik, rfl⟩
    exact ⟨⟨by rw [List.length_take, List.length_drop]; omega,
      fun a ha => hA a (List.mem_of_mem_drop (List.mem_of_mem_take ha))⟩,
      isInfix_window i k⟩

/-- Brute-force substring complexity: the maximum of `d_k / k` over `1 ≤ k ≤ n`, computed from
`bruteFactorCount` (with `0` at `k = 0`, which cannot affect a maximum of nonnegative values). -/
def bruteDelta (A : List α) (s : List α) : ℕ :=
  ((List.range (s.length + 1)).map fun k =>
    if k = 0 then 0 else bruteFactorCount A s k / k).foldr max 0

/-- The brute-force count equals the definition's `d_k` — the same statement with
`Repetitiveness.distinctFactors` on the right, through `distinctFactorsCompute_eq`. -/
theorem bruteFactorCount_eq_distinctFactors (A : List α) (s : List α) (k : ℕ)
    (hA : ∀ a ∈ s, a ∈ A) : bruteFactorCount A s k = (distinctFactors s k).card := by
  rw [bruteFactorCount_eq A s k hA, distinctFactorsCompute_eq]

/-! ### The check on all binary words of length at most six -/

/-- The alphabet of the check. -/
def binaryAlphabet : List Char := ['a', 'b']

/-- Every word over `{a,b}` of length at most `6`. -/
def binaryWordsUpTo6 : List (List Char) :=
  (List.range 7).flatMap fun k => wordsOfLength binaryAlphabet k

/-- The enumeration is **complete**: `binaryWordsUpTo6` contains every word over `{a,b}` of
length at most six, and nothing else. -/
theorem mem_binaryWordsUpTo6 {s : List Char} :
    s ∈ binaryWordsUpTo6 ↔ s.length ≤ 6 ∧ ∀ c ∈ s, c = 'a' ∨ c = 'b' := by
  classical
  simp only [binaryWordsUpTo6, List.mem_flatMap, List.mem_range, mem_wordsOfLength,
    binaryAlphabet, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨k, hk, hlen, hall⟩
    exact ⟨by omega, hall⟩
  · rintro ⟨hlen, hall⟩
    exact ⟨s.length, by omega, rfl, hall⟩

/-- **The two computations agree — as a computation.**  `bruteDelta` (enumerate all length-`k`
words over `{a,b}`, keep the ones occurring in `s` as an infix, maximise `count / k`) and
`deltaCompute` (the definition's `Finset` of windows, maximised) return the same number on every
word of `binaryWordsUpTo6`.  Evaluated by the kernel, which is the only form the repository allows
(`make check` rejects deciding with the native code generator). -/
theorem bruteDelta_check_binaryUpTo6 :
    binaryWordsUpTo6.all (fun s => bruteDelta binaryAlphabet s == deltaCompute s) = true := by
  decide

/-- **Agreement with brute force on every binary word of length at most `6`.** -/
theorem bruteDelta_eq_deltaCompute {s : List Char} (hs : s ∈ binaryWordsUpTo6) :
    bruteDelta binaryAlphabet s = deltaCompute s := by
  have h := List.all_eq_true.mp bruteDelta_check_binaryUpTo6 s hs
  simpa using h

/-- The same, in the form that mentions neither the enumeration nor `List.all`: for every word
over `{a,b}` of length at most six, the independent brute-force `δ` and the definition's `δ`
agree.  (`mem_binaryWordsUpTo6` turns the hypotheses into membership in the enumeration.) -/
theorem bruteDelta_eq_deltaCompute_of_length_le_six {s : List Char} (hlen : s.length ≤ 6)
    (hab : ∀ c ∈ s, c = 'a' ∨ c = 'b') :
    bruteDelta binaryAlphabet s = deltaCompute s :=
  bruteDelta_eq_deltaCompute (mem_binaryWordsUpTo6.mpr ⟨hlen, hab⟩)

/-! ### Running the measures

`#eval` on the lane's texts.  These are the numbers the research briefs ask for, computed by the
definition: `δ` exactly. -/

#eval (distinctFactorsCompute mississippi 3).card
#eval deltaCompute mississippi
#eval deltaCompute ababa
#eval deltaCompute (fibWord 6)
#eval greedyAttractorSize mississippi
#eval greedyAttractorSize ababa

/-- `δ = 2` on `"ababa"`, by computation, and equal to the proved value `ababa_delta`. -/
theorem deltaCompute_ababa : deltaCompute ababa = 2 := by
  rw [deltaCompute_eq, ababa_delta]

set_option maxRecDepth 100000 in
/-- `δ = 4` on `"mississippi"`. -/
theorem deltaCompute_mississippi : deltaCompute mississippi = 4 := by decide

set_option maxRecDepth 100000 in
/-- `δ = 2` on the length-13 Fibonacci word: a repetitive text is a small-`δ` text. -/
theorem deltaCompute_fibWord_six : deltaCompute (fibWord 6) = 2 := by decide

set_option maxRecDepth 100000 in
/-- The greedy attractor keeps `10` of the `11` positions of `"mississippi"`: on a text this
repetitive the maximal-irredundant-cover scan is close to `univ`, which is why `|Γ_greedy|` is a
certified *upper* bound and not a good estimate of `γ`. -/
theorem greedyAttractorSize_mississippi : greedyAttractorSize mississippi = 10 := by decide

/-- Nothing is degenerate: on `"mississippi"` the computable sandwich reads `4 ≤ 10`. -/
example : deltaCompute mississippi ≤ greedyAttractorSize mississippi :=
  (deltaCompute_le_greedyAttractorSize mississippi).1

end SortBounds.Projects.Algorithms
