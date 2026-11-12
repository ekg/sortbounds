# Lane: Repetitiveness — the counting core of `δ ≤ γ`

**Why this lane.** `docs/research/SYNTHESIS.md` answers "is the r-index optimal?":
time-wise it is up to a `log log` factor, but **space-wise `r` is the wrong measure** —
`r/δ = Θ(log n log log n)` is achievable (Kempa–Kociumaka, FOCS'20, Thm 4.3), and `δ`
(string attractor size) is the floor up to polylog (`Ω(δ log(n/δ) log n)` bits,
Kociumaka–Navarro–Prezza, IEEE TIT 2023, Thm IV.5).  The *elementary* part of that
hierarchy is worth machine-checking, and nobody appears to have formalized string
attractors at all.

**The quoted proof we are formalizing** (KNP, Lemma II.4, verbatim in
`docs/research/space.md`):

> "Every length-k substring has an occurrence covering an attractor position, so there
> can be at most kγ distinct substrings of length k, that is, d_k(S)/k ≤ γ for all
> k ≤ n."

So the mathematical core is a **counting argument**: a set of `Γ` positions "hits" every
substring, so a length-`k` window can cover at most `k` of them, whence at most `k·|Γ|`
distinct length-`k` substrings.

## Contract (exact target signatures)

```lean
namespace SortBounds.Projects.Repetitiveness

variable {α : Type*} [DecidableEq α]

/-- The number of distinct length-`k` factors of `s` (as a `Finset` of lists). -/
noncomputable def distinctFactors (s : List α) (k : ℕ) : Finset (List α)

/-- `Γ` is a **string attractor** for `s`: every nonempty factor occurs at some position
whose interval meets `Γ`.  (Positions are `Fin s.length`.) -/
def IsAttractor (s : List α) (Γ : Finset (Fin s.length)) : Prop

/-- **The counting lemma.**  A length-`k` factor occurrence covering an attractor
position is determined by that position and the offset, so there are at most `k · |Γ|`
of them. -/
theorem distinctFactors_card_le_mul_attractor {s : List α} {Γ : Finset (Fin s.length)}
    (hΓ : IsAttractor s Γ) (k : ℕ) : (distinctFactors s k).card ≤ k * Γ.card

/-- An SLP (straight-line program): `g` rules, each expanding to the concatenation of two
earlier symbols or a terminal.  `slpSize` is the number of rules. -/
structure SLP (α : Type*) where
  size : ℕ
  …

/-- **Every factor of length `k` is a sub-factor of a rule's expansion or straddles one
concatenation**, so a grammar of `g` rules has at most `k·g` distinct length-`k`
factors. -/
theorem distinctFactors_card_le_mul_slp {s : List α} (G : SLP α) (hG : G.expands s) (k : ℕ) :
    (distinctFactors s k).card ≤ k * G.size

/-- **`δ ≤ γ`** in the maximization form used by KNP: for every `k`, `d_k/k ≤ γ`, and `δ`
is the maximum of `d_k/k`. -/
theorem dk_div_le_slp {s : List α} (G : SLP α) (hG : G.expands s) (k : ℕ) :
    (distinctFactors s k).card ≤ k * G.size

end SortBounds.Projects.Repetitiveness
```

## Milestones

* **M0** `distinctFactors`, `IsAttractor`, and the counting lemma
  `distinctFactors_card_le_mul_attractor`.  The map is
  `(position p, offset j) ↦ factor starting at p−j`, and the key step is that every
  factor occurrence can be chosen to cover an attractor position.  Elementary, but the
  index arithmetic (`Fin` vs `ℕ`, `List.drop/take`) needs care.
* **M1** `SLP`, `expands`, and `distinctFactors_card_le_mul_slp`.  Choose the simplest
  faithful SLP model (a list of rules over `Fin size` with an acyclicity condition);
  the counting step is "a factor of length `k` is either a factor of some rule's
  expansion or contains a concatenation boundary of one".
* **M2 (stretch)** the characterization `min attractor size = max_k d_k(S)/k`, which
  with M1 gives `δ ≤ γ`.  The `≤` direction is M0; the `≥` direction is KNP's
  construction and is genuinely harder — do not attempt it unless M0/M1 are green with
  time to spare; if you do, report exactly which step resists.

**Not in scope:** `r` (BWT runs), Kempa–Kociumaka Thm 3.7 (deep), the
`γ = Ω(δ log(n/δ))` separations (need explicit string families).

## Rules

Own only `SortBounds/Projects/Repetitiveness/`.  `lake env lean`, no `lake build`, no
git, oleans in `/tmp`, no python for validation.  No `sorry`/`axiom`/`native_decide`.
**Do not invent a definition that makes the theorem vacuous** (e.g. an `IsAttractor` that
is unsatisfiable, or a `distinctFactors` that counts occurrences rather than distinct
values) — a reviewer will check exactly that, and the point of the lane is that the
counting is real.  Exhibit at least one nontrivial instance (e.g. `"ababa"` with an
attractor of size 2) as a sanity check.

## Prior art

*(to be filled after a literature check: is there any formalization of string
attractors, `d_k`, or `δ ≤ γ` in Lean/Coq/Isabelle?)*

## Log

* **M0 landed** (`Basic.lean`, `Attractor.lean`).
  * `distinctFactors (s) (k) : Finset (List α)` — distinct length-`k` factors (only starts
    with `i + k ≤ s.length`, so `d_0 = {[]}`, `d_k = ∅` for `k > n`; `mem_distinctFactors`).
  * `IsAttractor (s) (Γ : Finset (Fin s.length)) : Prop` — every nonempty factor `s[i..j)`
    has an occurrence `s[i'..j')` with some `p ∈ Γ` satisfying `i' ≤ p < j'`.  Non-vacuity
    and non-triviality are exhibited: `isAttractor_univ`, `ababa_isAttractor` (`{0,1}` for
    `"ababa"`), `not_isAttractor_singleton` (`{0}` is *not* one), `isAttractor_iff_check`
    (the condition is a finite check), plus a unary word with a size-`1` attractor.
  * `distinctFactors_card_le_mul_attractor (hΓ) (k) (hk : 1 ≤ k)`.
    **Side condition added: `1 ≤ k`** — the `k = 0` case is false (`d_0 = 1 > 0·|Γ|`); no
    upper bound `k ≤ s.length` is needed.  Same for M1.
  * Corollaries: `dk_div_le_attractor`, `substringComplexity` (KNP's `δ`),
    `substringComplexity_le_card_attractor`, `attractors`, `minAttractorSize`,
    `substringComplexity_le_minAttractorSize` (**`δ ≤` the *minimum attractor size*** —
    note this is a different fact from `δ ≤ γ`, the grammar size), and the concrete
    `ababa_substringComplexity` / `ababa_minAttractorSize` (`δ = γ = 2` for `"ababa"`).
* **M1 landed** (`Grammar.lean`, `Count.lean`).
  * `SLP` = rules `0..size-1`, each a terminal or `inr (A, B)` with `A, B < i` (acyclicity
    as a topological order); `SLP.expand` (well-founded recursion),
    `SLP.expands G s := ∃ root, G.expand root = s`, `SLP.slpWindow`.
  * `SLP.exists_straddle` — a window of length `k ≥ 2` of an expansion straddles some
    concatenation point, at an offset `d ∈ [1, k-1]`.
  * `distinctFactors_card_le_mul_slp (G) (hG) (k) (hk : 1 ≤ k)`; `k = 1` is separate
    (`distinctFactors_one_card_le_slp`).  Plus `dk_div_le_slp`, `substringComplexity_le_slp`
    (`δ ≤ g`) and a concrete grammar `ababaSLP` (`size = 5`) with `ababaSLP.expands ababa`.
  * `dk_div_le_slp` is stated in the **division** form `d_k / k ≤ g` (the contract listed
    it as a verbatim duplicate of the multiplication form; the multiplication form is the
    theorem above it).
* **M2 is not attempted.**  The contract's characterization
  `min attractor size = max_k d_k/k` has two halves.  The `≤` half is M0 and is landed
  (`substringComplexity ≤ minAttractorSize`); the `≥` half — "some attractor is no larger
  than `δ`" — is **not proved here**.
  *Correction to an earlier draft of this Log:* the `≥` half is **not** refuted by KNP
  Thm III.3.  That theorem separates `γ` (grammar size) from `δ` — `γ = Ω(δ log(n/δ))` —
  and says nothing about the size of the *smallest attractor*, which is a different
  quantity.  Whether `min attractor size = δ` holds in general (and for which strings it
  fails) is a separate question that needs a source; the integrator has recorded it as an
  open item rather than a refutation.  What *is* established here: the equality holds for
  `"ababa"` (`δ = minAttractorSize = 2`), and `δ ≤ minAttractorSize` always.
