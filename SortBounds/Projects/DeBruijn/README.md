# Lane: DeBruijn — a machine-checked separation `γ ≥ 2^k/k`

**Status: M0–M3 LANDED** in `DeBruijn.lean` (`lake env lean` silent, no `sorry`/`axiom`).  All
four contract theorems are proved with the contract's signatures; no statement had to be
weakened.  See the Log at the bottom for what was harder than advertised.

**Why.** `docs/research/gamma-vs-gamma2.md` proves: for a binary de Bruijn word `B_k` of order
`k`, `γ(B_k) ≥ 2^k/k` while `γ₂(B_k) ≤ 4`; hence `γ/γ₂` is unbounded and the "`γ₂` is within a
constant of `γ`" route to an algorithm is dead. The proof is: `d_i = 2^i` for `i ≤ k` ⇒
`δ = 2^k/k` ⇒ `γ ≥ δ`. All three steps are formalizable, and `δ ≤ γ` is already machine-checked
(`Repetitiveness.deltaQ_le_minAttractorSize`).

This lane makes the *inequality* a theorem. It deliberately does **not** construct de Bruijn
sequences (that is a separate, well-known combinatorial existence result — cite it as a
hypothesis and discharge it for small `k` by `decide`).

## Contract (exact target signatures)

```lean
namespace SortBounds.Projects.DeBruijn

open SortBounds

/-- Every binary word of length `k` occurs as a factor of `s`. -/
def CoversAllWords (s : List Bool) (k : ℕ) : Prop

/-- A de Bruijn word of order `k`: length `2^k + k - 1` and every `k`-gram occurs. -/
def IsDeBruijn (s : List Bool) (k : ℕ) : Prop

/-- **The counting core**: if every binary word of length `i ≤ k` occurs, then `s` has
exactly `2^i` distinct factors of length `i`. -/
theorem card_distinctFactors_of_coversAllWords {s : List Bool} {i : ℕ}
    (h : CoversAllWords s i) : (distinctFactors s i).card = 2 ^ i

/-- **`δ = 2^k/k`** for a de Bruijn word of order `k ≥ 2`. -/
theorem deltaQ_isDeBruijn {s : List Bool} {k : ℕ} (hk : 2 ≤ k) (h : IsDeBruijn s k) :
    deltaQ s = (2 ^ k : ℚ) / k

/-- **The separation**: `γ ≥ 2^k/k` for a binary de Bruijn word. -/
theorem gamma_ge_of_isDeBruijn {s : List Bool} {k : ℕ} (hk : 2 ≤ k) (h : IsDeBruijn s k) :
    (2 ^ k : ℚ) / k ≤ (minAttractorSize s : ℚ)

/-- Non-vacuity: `IsDeBruijn` is satisfiable for the smallest two orders. -/
theorem isDeBruijn_two : IsDeBruijn (['0','0','1','1','0'].map (· = '1')) 2
theorem isDeBruijn_three : IsDeBruijn (<de Bruijn word of order 3 over Bool>) 3

end SortBounds.Projects.DeBruijn
```

## Milestones

* **M0** `CoversAllWords`, `IsDeBruijn`, `card_distinctFactors_of_coversAllWords`
  (`distinctFactors s i` is the image of `Fin i → Bool` under `List.ofFn`; use
  `Finset.card_image_of_injective` and `Fintype.card_fun`; `List.ofFn_injective` is in
  Mathlib).
* **M1** `deltaQ_isDeBruijn`: `deltaQ` is the `sup'` over `1 ≤ i ≤ n` of `d_i/i`; with
  `d_i = 2^i` it is `max_i 2^i/i`, attained at `i = k` because `2^i/i` is nondecreasing for
  `i ≥ 1`. (Careful: `deltaQ` uses `ℚ` division and `Finset.sup'`; you may need the `Icc`
  membership and `sup'_le`/`le_sup'`.  If the `sup'` rewriting is painful, prove the two
  inequalities separately: `∀ i ∈ Icc 1 n, 2^i/i ≤ 2^k/k` and `2^k/k` is attained at `k`.)
* **M2** `gamma_ge_of_isDeBruijn` — one line from M1 and
  `Repetitiveness.deltaQ_le_minAttractorSize`.
* **M3** the two `decide` instances (order 2: `00110`; order 3: `0001011100`), each by
  `decide` over all `2^k` words of length `k`. This is what makes the theorem non-vacuous.

## Rules

Own only `SortBounds/Projects/DeBruijn/`.  `lake env lean`, no `lake build`, no git, oleans in
`/tmp`.  No `sorry`/`admit`/`axiom`/`native_decide`.  Do **not** claim existence of de Bruijn
words for all `k` in Lean — it is a hypothesis of the main theorems and the two instances are
witnesses.  If a statement is false as written (e.g. a length condition), state the true one and
report.

## Prior art

De Bruijn sequences: de Bruijn 1946; the greedy/FKM construction; van Aardenne-Ehrenfest &
de Bruijn 1951.  `γ ≥ δ` is KNP23 Lemma II.4 (machine-checked here).  The separation
`γ/γ₂ → ∞` is, as far as our surveys go, unstated in the literature.

## Log

* **M0–M3 landed** (`DeBruijn.lean`).  What is here, beyond the four contract theorems:
  * `CoversAllWords` quantifies over **all** `List Bool` of length `k` (the honest reading of
    "every binary word of length `k` occurs"), so it is not itself `decide`-able — no
    `Decidable` instance for `∀ w : List Bool, …`.  The lane therefore proves
    `coversAllWords_iff_fin` (`Fin k → Bool`, via `exists_ofFn_eq`: every list of length `k`
    is `List.ofFn` of a tuple) and the M3 instances `decide` **that**.  Cost: one bridge
    lemma.  Worth knowing if another lane wants the same definition.
  * `deltaQ`'s `sup'` needed *more* than "`i ↦ 2^i/i` is nondecreasing": the supremum runs
    over `Icc 1 s.length = Icc 1 (2^k + k - 1)`, so for `k < i` the value `d_i = 2^i` is not
    available and `d_i` is of order `2^k`, not `2^{2^k}`.  There the bound is the **position
    count** `d_i ≤ s.length - i + 1 = 2^k + k - i` (`card_distinctFactors_le`), which is
    below `2^k/k` for `i > k` because the inequality reduces to `(k - i)(2^k + k) ≤ 0`
    (`ratio_le_of_lt`).  So the README's "prove the two inequalities separately" advice was
    half the work; the `i > k` case was the surprise, and it is genuinely necessary —
    `d_i/i` for `i > k` is *not* covered by monotonicity of `2^i/i`.
  * the two headline theorems are `deltaQ`-statements, so `δ` (not the floored
    `substringComplexity`) is what is pinned; the witnesses show why: `δ(0001011100) = 8/3`.
    `decide` cannot evaluate `deltaQ` at all (the kernel gets stuck on `Finset.sup'`), so the
    two witness values in the file are derived from `deltaQ_isDeBruijn`, not computed.
  * **Not proved, on purpose:** `γ₂(B_k) ≤ 4`.  `γ₂` (bounded-length attractors) is not
    defined in this repository, so the quotient conclusion `γ/γ₂ → ∞` stays prose in
    `docs/research/gamma-vs-gamma2.md`; `gamma_ge_of_isDeBruijn` is this lane's half.  The
    file says so in a closing section.
  * Non-vacuity: `isDeBruijn_two` (`00110`), `isDeBruijn_three` (`0001011100`), and two
    negative examples showing each hypothesis of `IsDeBruijn` bites (`0010` misses the `2`-gram
    `11`; `0011` has the wrong length).
* `DeBruijn.lean` is **not** imported by the umbrella `SortBounds.lean` (the integrator's
  call, per `docs/STRUCTURE.md`); `lake env lean SortBounds/Projects/DeBruijn/DeBruijn.lean`
  is the check.
