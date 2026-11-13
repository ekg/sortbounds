# Hardness of the minimum attractor: the exact statements, and the `σ = 2` gap

Question A1: what is *proved* about the complexity of the minimum string attractor, and does any of
it survive restriction to a binary alphabet (`σ = 2`)?

**Verdicts.** PROVED = read verbatim in a primary source (quoted); MY-INFERENCE = derived from
cited statements; MY-COMPUTATION = computed here; UNVERIFIED = source not read; OPEN = no source
found.

**Sources.** **KP18** Kempa–Prezza, STOC 2018, doi:10.1145/3188745.3188814, arXiv:1710.10964
(quotes from **v4**; numbering differs across versions — KPRR18 cites the NP-completeness as
"Thm. 8"). **KPRR18** Kempa–Policriti–Prezza–Rotenberg, ESA 2018, LIPIcs 112,
doi:10.4230/LIPIcs.ESA.2018.52, arXiv:1803.01695. **FW24** Fuchs–Whittington, STACS 2024,
doi:10.4230/LIPIcs.STACS.2024.41, arXiv:2304.06523. **MRRRS19** arXiv:1907.04660 (venue
unverified). **P21** Prezza, arXiv:2004.02781 (survey). **CFGGS21** Casel et al., Theory Comput.
Syst. 65(2):344–409, 2021, doi:10.1007/s00224-020-10013-w.

## 1. The proved statements, verbatim

**(a) fixed `k ≥ 3`: NP-complete.** KP18 **Thm 4.2**: "For `k ≥ 3`, `k`-ATTRACTOR is NP-complete."
Here a `k`-attractor covers all factors of length **at most** `k` (KP18 Def. 4.1: "every substring
`T[i..j]` such that `i ≤ j < i + k`"); the reduction is from `k`-SET COVER for constant `k ≥ 3`.

**(b) the full attractor `k = n`: NP-complete.** KP18, intro:
> "Using a reduction from k-set-cover, we show that the k-attractor problem is NP-complete for
> `k ≥ 3`. In particular, this proves the NP-completeness of the original string attractor problem
> (i.e., the case `k = n`)."

The lift from constant `k` to `k = n` is a **monotonicity gadget** on the same string `T_C`:
`γ*_k(T_C) = γ*_{k'}(T_C)` for every `k < k' ≤ |T_C|`, so hardness at `k = 3` transfers to `k = n`.
KP18 footnote 3 admits non-constant `k = f(n)` when `f(n) → ∞` and `f` is non-decreasing, which
`k = n` satisfies.

**(c) APX-completeness for constant `k`.** KP18 **Thm 4.3**: "For any constant `k ≥ 3`,
MINIMUM-`k`-ATTRACTOR is APX-complete." Membership rests on the alphabet-free
`γ*_k(T) ≤ σ_k(T²) ≤ 2k·γ*_k(T)`; hardness on a reduction from minimum `k`-vertex-cover. It is
about one fixed `k`, not `k = n`.

**(d) inapproximability, every `k ≥ 3`.** KP18 **Cor. 4.4**:
> "For every constant `ǫ > 0` and every (not necessarily constant) `k ≥ 3`, it is NP-hard to
> approximate MINIMUM-`k`-ATTRACTOR within factor `11809/11808 − ǫ`."

The brief writes "~`1 + 1/11809`"; the paper's ratio is `11809/11808 = 1 + 1/11808`
(MY-COMPUTATION: `2k³+4k²−3k+1 = 82` at `k=3`, and `144·82 = 11808`, from Berman–Karpinski's
`145/144` for 3-vertex-cover). As non-constant `k`, including `k = n`, is admissible, this covers
the **full** attractor: no PTAS (MY-INFERENCE — the corollary does not spell out `k = n`).

**(e) `k = 2` — the 2018 open case, closed in 2024.** KPRR18: "Note that such a result is not known
for k-attractors (the case `k = 2` being the only one still open)." FW24 **Thm 9**: "The 2-attractor
problem is NP-complete"; FW24 **Thm 11**: "For every `k ≥ 2` and `0 < ε < 1`, it is NP-hard to
approximate the k-attractor problem to within an approximation ratio smaller than
`(10669 − ε)/10668`." Note `10669/10668 ≈ 1.0000937 > 11809/11808 ≈ 1.0000847` (MY-COMPUTATION),
so FW24 strictly improves the threshold and extends it to `k = 2`. **Repo flag:**
`docs/research/attractor-approx.md` §1.2 and §2(c) still present "`k=2` … still open" as current;
stale as of STACS 2024.

**(f) do not confuse the variants.** `k`-**sharp**-attractor (factors of length *exactly* `k`) is
NP-complete for constant `k ≥ 3` (KPRR18 Thm 34) but **in P for `k = 2`** (Thm 35, edge cover) —
FW24 exists because the sharp-2 case being easy says nothing about the 2-attractor. Chaining the
five statements: only (b) and (d) cover `k = n`; (c) is per constant `k`; (e) is `k = 2`.

## 2. The alphabet in each reduction — the crux

**KP18 (both (a) and (b)).** The alphabet is defined inside the proof, Eq. (4):
> `Σ = ∪_{i=1..u}{x_i} ∪ ∪_{i=1..u}∪_{j=1..k}{x_i^{(j)}} ∪ ∪_{i=1..m}∪_{j=1..n_i+1}{$_{i,j}}
> ∪ ∪_{i=1..u}∪_{j=2..k}{$'_{i,j},$''_{i,j}} ∪ ∪_{i=1..m}∪_{j=2..n_i}{$'''_{i,j},$^{(4)}_{i,j}} ∪ {#}`

where `u = |U|`, `m = |C|`, `n_i = |C_i|`, `t = Σ n_i`. Every family is indexed by `u`, `k` or
`n_i`, so `σ ≥ uk` and `σ ≥ u`; counting the display gives `σ = Θ(uk + t)`
(MY-INFERENCE: `u + uk + (t+m) + 2u(k−1) + 2(t−m) + 1`) against `|T_C| = O(uk² + tk)`. Hard
instances need `u → ∞`, hence `σ → ∞`: **there is no fixed-`σ` version of this proof.** The gadget
depends on it: element `t` gets `k` *distinct* symbols `x_t^{(1)}…x_t^{(k)}`, each block of `S_i`
holds a factor that occurs "only in `S_i` and nowhere else", and the count turns on exactly one
position of slack between `2n_i + 1` and `2n_i + 2` markings inside `S_i`.

**FW24 (`k = 2`).** Their own words: "It is vital that each vertex has a unique label so that each
vertex uniquely corresponds to a 2-substring. For that reason, we need to introduce more symbols and
pay attention that they are all covered." Concretely, Thm 9 uses "an alphabet
`Σ = C ∪ L ∪ L̄ ∪ X = {C_1,…,C_m} ∪ {L_1,L_2,L_3} ∪ {L̄_1,L̄_2,L̄_3} ∪ {X_1,…,X_n}`", i.e.
`σ = m + n + 6 = Θ(n)`; and reducing from a *set* of strings to one string costs, by their Lemma 3,
"`m−1` new symbols `#_1,…,#_{m−1} ∉ Σ`" — `2n+5` more fresh letters. So the 2-attractor hardness
is **also** large-alphabet.

**KPRR18**, same fact stated twice: "The problem remains NP-hard even under the restriction that
only substrings of length at most `k` are captured by `Γ`, for any `k ≥ 3` **and on large
alphabets**"; and for their sharp-`k` reduction, "Note also that our reduction requires large
alphabet." MRRRS19's abstract and P21 then repeat it unqualified — true when `Σ` is part of the
input, not a claim about fixed `σ`.

**Why no constant-`σ`/constant-`k` hardness can exist.** KPRR18 **Thm 29**: "A minimum `k`-attractor
can be found in `O(n) + exp(O(σ^k log σ^k))` time"; **Cor. 7**: "For constant `k`, a minimum
`k`-attractor can be found in optimal `O(n)` time when `σ^{k+ε} ∈ O(log n)`, for any constant
`ε > 0`." At `σ = 2` both exponential terms are constants, so all of §1's hardness lives in the
`σ`-growing regime.

## 3. What is actually known for `σ = 2`

* **`k = 1`**: `γ_1 = σ` (KP18 Ex. 3.3: "any attractor `Γ` must satisfy `|Γ| ≥ σ`"), so `γ_1 = 2`.
* **every fixed `k`**: exact minimum `k`-attractor in `O(n)` (KPRR18 Cor. 7; also Thm 29 with
  `σ = 2`). **MY-INFERENCE, loud version: on binary strings the 2-attractor problem — the one FW24
  proves NP-complete — is solvable in `O(n)`.** No contradiction: FW24's instances have
  `σ = Θ(n)`. So the known hardness is purely an alphabet phenomenon.
* **`k` growing, `σ = 2`**: still in P while `σ^k log σ^k ∈ O(log n)` (Cor. 6), i.e.
  `2^k·k·ln2 ≤ c·log n`, roughly `k ≲ log₂log n − log₂log₂log n` (MY-COMPUTATION: largest admissible
  `k` is `3` at `log₂n = 40`, `4` at `log₂n = 100`). Past that, `σ = 2` buys nothing: the KPRR18
  Lemma 13 class bound `min{n, σ^{2k−1} + 2k − 2}` equals `n` once `k ≈ ½log n`.
* **`k = n` at `σ = 2`**: **no source.** Nothing proves hardness for `σ = 2`; nothing gives a
  polynomial algorithm for the full attractor on binary strings. Searched: arXiv listings for
  "string attractor(s)", citation graphs of KP18/KPRR18, and the open-problem sections of KPRR18,
  FW24, P21, MRRRS19, KNP23 (arXiv:1910.02151), BBGKM26 (arXiv:2602.16152) — none discusses the
  alphabet restriction (UNVERIFIED ABSENCE; a field-wide full-text search would raise confidence).
* **Structural (not complexity) facts**: standard Sturmian words (incl. Fibonacci) have `γ = 2`
  (MRRRS19 Thm 5), Thue–Morse words `γ = 4` (Kutsukake et al., arXiv:2005.09524 Thm 3,
  `n ≥ 4`). MRRRS19 leaves open only the *characterisation*: "An open question is to characterize
  all the binary words with string attractor of size 2."

## 4. Verdict, and what a binary reduction has to overcome

**"Minimum attractor is NP-hard for `σ = 2`" is OPEN** — not proved, not refuted by any algorithm
found. No polynomial algorithm is known either, even though every *fixed-`k`* case is linear-time.

1. **Unique labels must become unique factors.** All three reductions force positions by making a
   factor occur *once*; over `{a,b}` a distinct label costs `Θ(log n)` characters, so `Θ(n)` labels
   need `Θ(n log n)` positions — affordable, but see 2.
2. **The `±1` coverage ledger.** KP18's gap is one position inside each `S_i` (`2n_i+1` vs
   `2n_i+2`); FW24's is `5n+6` against `5n+6+u`. Codeword encoding creates a new factor per prefix,
   suffix and boundary, each with its own cover count, which does not stay inside a constant
   additive gap without a bespoke "covered for free" argument like KP18's for `P_i`, `R_i`. That,
   not alphabet size itself, is the real work.
3. **The lift to `k = n`.** Hardness at `k = 2` or `3` is not enough: one needs a binary analogue of
   the monotonicity gadget, checked by verifying that all long factors inside each gadget are covered
   in *both* local optima.
4. **No shortcut from other measures.** `γ ≤ g` (KP18 Thm 3.5) and `γ ≤ z` are upper bounds; SLP
   hardness does not transfer downwards. Analogue: fixed-alphabet hardness *is* known for the
   smallest *grammar* problem, but only at `σ ≥ 17` (CFGGS21: it "remains NP-complete … even if the
   alphabet is fixed and has size of at least 17"). Binary is not reached even there.
5. **A poly algorithm is equally plausible.** With `σ = 2` and `k` fixed the problem is in `O(n)`, so
   the frontier must be at some `k` growing with `n`; crux: can KPRR18 Lemma 13's `σ^{2k−1}`
   class-collapse be replaced by something polynomial at `σ = 2`, `k = n`?

## 5. What would settle it

1. **Test FW24's colorful-edge-cover machinery at `Σ = {a,b}`**: replace one colour per symbol by
   one vertex per codeword occurrence (`ℓ = O(log n)`) and check whether Lemma 10's count survives.
   One binary-encoded clause gadget with exact `γ` by brute force decides feasibility.
2. **Exhaustive experiment**: exact `γ` for all `2^n` binary strings, `n ≤ 20` (minimal coverages +
   branch-and-bound hitting set; anchors `γ(t_n)=4`, `γ(F_m)=2`) is not a proof, but a family with a
   closed-form `γ` is where a binary gadget would come from.
3. **Parameterized axis**: FPT or W[1]-hard in `k` for `σ = 2`? Cor. 6 gives only `k = O(log log n)`.
4. **Ask KPRR18/FW24** whether fixed-`σ` hardness is known to them; a private "no" is worth
   recording.
5. **Never publish "NP-hard for binary alphabets."** The defensible sentence: "NP-hard in general
   (KP18; FW24), by reductions whose alphabets grow with `n` (KP18 Eq. 4: `σ = Θ(uk+t)`; FW24:
   `σ = Θ(n)`); the complexity for fixed `σ`, in particular `σ = 2` with `k = n`, is open, while every
   fixed `k` is solvable in linear time (KPRR18 Cor. 7)."
