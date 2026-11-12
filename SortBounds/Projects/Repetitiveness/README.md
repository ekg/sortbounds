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
    (hΓ : IsAttractor s Γ) (k : ℕ) (hk : 1 ≤ k) : (distinctFactors s k).card ≤ k * Γ.card

/-- An SLP (straight-line program): `g` rules, each expanding to the concatenation of two
earlier symbols or a terminal.  `slpSize` is the number of rules. -/
structure SLP (α : Type*) where
  size : ℕ
  …

/-- **Every factor of length `k` is a sub-factor of a rule's expansion or straddles one
concatenation**, so a grammar of `g` rules has at most `k·g` distinct length-`k`
factors. -/
theorem distinctFactors_card_le_mul_slp {s : List α} (G : SLP α) (hG : G.expands s) (k : ℕ)
    (hk : 1 ≤ k) : (distinctFactors s k).card ≤ k * G.size

/-- **`δ ≤ g`** in the division form KNP use: for every `k ≥ 1`, `d_k/k ≤ g`.  (KNP's
Lemma II.4 is the *attractor* version, `dk_div_le_attractor`; `g` here is the smallest
SLP size, a different measure from `γ`.) -/
theorem dk_div_le_slp {s : List α} (G : SLP α) (hG : G.expands s) {k : ℕ} (hk : 1 ≤ k) :
    (distinctFactors s k).card / k ≤ G.size

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

## M3 target: the certification system (opened 2026-11-12)

**The design constraint.**  Finding a smallest attractor is **NP-hard**: the quoted
statement is "finding the smallest k-attractor is NP-hard" (ESA 2018, *String Attractors:
Verification and Optimization*), with NP-completeness for general alphabets and `k ≥ 3` and
APX-completeness for constant `k ≥ 3` (quoted in the search record for this lane,
**UNVERIFIED** against the PDF), and a polynomial approximation via set cover — the figure
`O(log k)` is quoted second-hand and **UNVERIFIED** (set cover over `n` positions would
suggest `O(log n)`; reconcile against ESA'18 before citing it).  By contrast **verifying** a
candidate is `O(n)` in that literature, and **`δ = max_k d_k/k` is computable exactly in
`O(n)`** (KNP's algorithm; implemented publicly as `regindex/substring-complexity`).
None of those cost claims is formalized here: the `Bool` verifier in `Certify.lean` is
polynomial but *not* linear, and `delta` is `noncomputable`.

So the system cannot *find* the optimum.  It can do this, which is what an index actually
needs:

```lean
/-- A certified attractor: a position set together with a proof that it is one. -/
structure AttractorCertificate (s : List α) where
  pos : Finset (Fin s.length)
  isAtt : IsAttractor s pos

/-- **The certified upper bound on `δ`**: any valid attractor bounds `δ` from above. -/
theorem AttractorCertificate.delta_le (c : AttractorCertificate s) :
    substringComplexity s ≤ c.pos.card

/-- The verifier, as a computable `Bool` program (polynomial, *not* linear: it scans all
`(i,k)` factor occurrences against all `n` positions). -/
def checkAttractor (s : List α) (Γ : Finset (Fin s.length)) : Bool
theorem checkAttractor_eq_true_iff {s} {Γ} : checkAttractor s Γ = true ↔ IsAttractor s Γ

/-- A **computable** attractor construction (not optimal — that is NP-hard): the greedy
cover of all factors, returning positions.  Its correctness, not its size, is the theorem. -/
def greedyAttractor (s : List α) : Finset (Fin s.length)
theorem greedyAttractor_isAttractor (s : List α) : IsAttractor s (greedyAttractor s)

/-- **The certified bracket on `γ`**: `δ ≤ |Γ_greedy|` and `γ ≤ |Γ_greedy|`, so
`[δ, |Γ_greedy|]` brackets the smallest attractor.  **No approximation ratio is proved** —
the greedy is not an approximation algorithm here; `"aab"` shows `|Γ| = 3` against
`δ = γ = 2`. -/
theorem delta_le_greedyAttractor_card (s : List α) :
    substringComplexity s ≤ (greedyAttractor s).card
```

And a `Measures.lean` that names the measures once — `gamma := minAttractorSize`,
`delta := substringComplexity` — with `delta_le_gamma` (proved) as the anchor, so the rest
of the repository and the research briefs use one vocabulary.

**What this system is for.**  An index's space guarantee comes from *some* measure; if you
can certify an attractor of size `c` and compute `δ`, you have a *proved* interval
`[δ, c]` on the smallest attractor, hence on the space any attractor-based index needs —
without solving an NP-hard problem.  The `γ = Ω(δ log(n/δ))` separation (KNP Thm III.3)
says the interval can genuinely be wide, which is the honest limitation of the approach.

## Prior art

* Kempa & Prezza, *At the Roots of Dictionary Compression: String Attractors* (STOC
  2018): the attractor notion and `γ` = size of the smallest attractor.
* Kociumaka, Navarro & Prezza, *Toward a Definitive Compressibility Measure for
  Repetitive Sequences* (IEEE TIT 2023 / LATIN 2020): `δ = max_k d_k/k`, `δ ≤ γ`, the
  separation `γ = Ω(δ log(n/δ))`, and the encoding lower bound — all quoted in
  `docs/research/space.md`.
* **Formalization prior art: none found** (searched 2026-11-12 for Lean/Coq/Isabelle
  treatments of string attractors, `d_k`, or `δ ≤ γ`); this lane appears to be the first
  machine-checked version of KNP's counting lemma.  Treat that claim as *unverified
  absence*, not a theorem.

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
    `substringComplexity_le_minAttractorSize` (**`δ ≤ γ`** — `γ` is the size of the
    smallest attractor, per Kempa–Prezza's notation), and the concrete
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
* **M2: the proposed characterization is false, and the refutation is quotable.**  The
  contract's `min attractor size = max_k d_k/k` has two halves.  The `≤` half is M0 and is
  landed (`substringComplexity ≤ minAttractorSize`, i.e. `δ ≤ γ`).  The `≥` half — "some
  attractor is no larger than `δ`" — is **refuted** by KNP Lemma III.2 / Thm III.3: for
  `S_n = b a^{2^j−1} b …` (i.e. `b` at powers of two) one has `δ(S_n) ≤ 2` while
  `γ(S_n) ≥ ½⌊log n⌋`, so the smallest attractor exceeds the substring complexity by a
  log factor (`docs/research/space.md` §1 and :153-157).  The equality holds only for
  particular strings — `"ababa"` (`δ = γ = 2`) is one, shown above.
  *(An earlier integrator edit wrongly claimed this half was unproved-and-possibly-true,
  by misreading `γ` as the grammar size; `γ` is the attractor size, `g` the grammar.)*
