/-
SortBounds/Projects/Algorithms/Texts.lean

**The two texts this lane runs on**, written once so that the demos in `Compute.lean`,
`SuffixArray.lean` and `Measure.lean` are about the same words.

`"mississippi"` is the standard small example whose BWT (`ipssm$pissii`) is in every
introduction; `fibWord n` is the Fibonacci word prefix, the standard *repetitive* text on which
`δ` stays tiny while a maximal-irredundant-cover attractor is not.

Lean does not elaborate string literals as `List Char` in this toolchain, so the texts are
spelled as lists.
-/
import Mathlib

namespace SortBounds.Projects.Algorithms

/-- `"mississippi"` as a list of characters. -/
def mississippi : List Char := ['m', 'i', 's', 's', 'i', 's', 's', 'i', 'p', 'p', 'i']

theorem mississippi_length : mississippi.length = 11 := rfl

/-- The Fibonacci word prefix: `fibWord 0 = b`, `fibWord 1 = a`, `fibWord (n+2) = fibWord (n+1) ++
fibWord n`.  Lengths are `1, 1, 2, 3, 5, 8, 13, …` (Fuss–Fibonacci), so `fibWord 6` has length
`13`. -/
def fibWord : ℕ → List Char
  | 0 => ['b']
  | 1 => ['a']
  | n + 2 => fibWord (n + 1) ++ fibWord n

theorem fibWord_six_length : (fibWord 6).length = 13 := rfl

end SortBounds.Projects.Algorithms
