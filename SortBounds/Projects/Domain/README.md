# Lane: Domain — does structure buy speed, or is `n log n` inescapable?

**Question.** The comparison bound is `log₂(n!)`. But the number of *bits of
information* needed is `log₂(U)`, where `U` is the size of the key domain, not
`log₂(n!)`. Whenever `U` is much smaller than `n!`, a procedure that can *read the
key* rather than compare it needs far fewer steps.  This lane makes that
quantitative and shows the bound is **tight**: `log_b U` probes are necessary, and
radix sort uses exactly `⌈log_b U⌉`.

This is the formal answer to "are we proving there is no escape?". No: we prove
exactly how much an escape costs — `log_b U` steps of `b`-way access — and that
radix attains it. For `U = n^{O(1)}` and `b = n` that is `O(1)` passes, versus
`Ω(n log n)` comparisons.

## Contract (exact target signatures)

```lean
namespace SortBounds.Projects.Domain

/-- Keys as `d` digits in base `b`. -/
def Key (d b : ℕ) := Fin d → Fin b
theorem card_Key (d b : ℕ) : Fintype.card (Key d b) = b ^ d

/-- A `b`-way `p`-probe transcript: which digit was read, and what it was. -/
def Probe (d b p : ℕ) := Fin p → Fin d × Fin b

/-- **`b`-ary probes cannot distinguish more than `b ^ p` keys.**  (Instantiate
`Core.card_le_pow_of_prefixFree` with the transcript map.) -/
theorem card_le_pow_probes (d b p : ℕ) (S : Finset (Key d b))
    (hfiber : ∀ k₁ ∈ S, ∀ k₂ ∈ S, (∀ q, Probe.digit … = …) → k₁ = k₂) :
    S.card ≤ b ^ p

/-- **The bound is attained**: radix sort on `d` base-`b` digits uses exactly `d`
passes and sorts every list of keys (`Instances.Radix`). -/
theorem radix_sorts_Key (d b : ℕ) (l : List (Key d b)) : … (radixSort d b id l) …

/-- **No `b`-ary procedure sorts `b ^ d` keys in `p < d` probes.** -/
theorem passes_lower {d b p : ℕ} (hp : p < d) : ¬ (∃ proc, SortsAllKeys proc p)

/-- **The word-RAM corollary**: with `w`-bit words (`b = 2 ^ w`) and `U = 2 ^ nw`,
sorting needs `≥ n` word reads, and radix with `w`-bit digits uses `n`. -/
theorem wordram_probes (n w : ℕ) (hw : 0 < w) : …

end SortBounds.Projects.Domain
```

## Milestones

* **M0** `Key`, `card_Key`, `Probe`, and the counting lemma instantiated from
  `Core.Branching` (`card_le_pow_probes`).  No new combinatorics.
* **M1** `passes_lower` — a clean statement that a `p`-probe `b`-ary procedure
  cannot sort a domain of `b ^ d` keys when `p < d`, with the model spelled out
  (what is a "procedure" here? a function from probe transcripts to an ordering,
  or a decision tree over digit reads — pick the simplest faithful model and say
  why it is faithful).
* **M2** the tightness: `radixSort` on `Key d b` uses `d` passes (reuse
  `Instances.Radix.radixCost_eq_passes` and its correctness), so passes `= d`
  exactly.
* **M3** the contrast statement: for `U = b ^ d` with `b = n`, comparison sorting
  needs `Ω(n log n)` while digit sorting uses `d = log_b U` passes; state it with
  explicit numbers (e.g. `U = n ^ 2 ⇒ 2` passes).

## Rules

Own only `SortBounds/Projects/Domain/`.  Reuse `Core/Branching` and
`Instances/Radix`; do not edit them.  `lake env lean`, no `lake build`, no git,
oleans in `/tmp`, no python for validation.  No `sorry`/`axiom`/`native_decide`.
The one thing to be careful about is the **model**: say exactly what a probe is and
why a comparison sort is *not* a `b`-ary probe procedure (it must not be — otherwise
you would prove the comparison bound false).  If a statement turns out to be false
or vacuous, say so and state the true one.

## Prior art

Radix sort's `O(d(n+k))`: CLRS §8.3.  Fusion trees `O(n log n / log log n)` and
van Emde Boas `O(n log log U)`: Fredman–Willard 1993, van Emde Boas 1975 — all
wider probes, i.e. larger `b`.  Han–Thorup `O(n√log log n)`.  None formalised.

## Log

### Round 1 (files `Model.lean`, `Lower.lean`, `Radix.lean`, `Contrast.lean`)

M0–M3 landed. Everything is `lake env lean`-clean (one file at a time would need
oleans; validated as one concatenation in `/tmp`), no `sorry`/`axiom`/`native_decide`,
and `#print axioms` gives `propext, Classical.choice, Quot.sound` for every headline
theorem.

**The model, in one paragraph.** A *probe plan* `KeyProc d b p` is `next : (q) → q < p →
(Fin q → Fin b) → Fin d` (the digit to read at step `q`, chosen from the values read so
far — so plans are adaptive) together with `code : (Fin p → Fin b) → ℕ` (a digest computed
from the values read). `P.codeOf k` is the digest of key `k`; `P.valsAt k` its observation;
`P.trace k` the full transcript (`Probe d b p`). `SortsAllKeys P` says the digest refines
the radix order on keys and separates distinct keys (the two clauses are derived from
"sorts every list" in the definition's comment). A comparison sort is *not* an instance:
it reads order relations between positions and separates the `n!` arrangements, not the
`b ^ d` keys — the separation is stated as a remark at the head of `Model.lean`.

**Landed (exact signatures).**

```lean
abbrev Key (d b : ℕ) := Fin d → Fin b
theorem card_Key (d b : ℕ) : Fintype.card (Key d b) = b ^ d
def Probe (d b p : ℕ) := Fin p → Fin d × Fin b
theorem card_le_pow_probes (d b p : ℕ) (t : Key d b → Probe d b p) (S : Finset (Key d b))
    (hfiber : ∀ k₁ ∈ S, ∀ k₂ ∈ S, (∀ q, (t k₁ q).2 = (t k₂ q).2) → k₁ = k₂) :
    S.card ≤ b ^ p                          -- Kraft, specialised (Core.Branching)
theorem no_injective_code_of_lt {d b p : ℕ} (hb : 2 ≤ b) (hp : p < d) (P : KeyProc d b p) :
    ¬ Function.Injective P.codeOf
theorem passes_lower {d b p : ℕ} (hb : 2 ≤ b) (hp : p < d) :
    ¬ ∃ P : KeyProc d b p, SortsAllKeys P
theorem probes_lower {d b p : ℕ} (hb : 2 ≤ b) {P : KeyProc d b p} (h : SortsAllKeys P) : d ≤ p
theorem probes_lower_logb {d b p : ℕ} (hb : 2 ≤ b) {P : KeyProc d b p} (h : SortsAllKeys P) :
    Real.logb b (Fintype.card (Key d b)) ≤ (p : ℝ)
theorem exists_code_collision {d b p : ℕ} (S : Finset (Key d b)) (P : KeyProc d b p)
    (h : b ^ p < S.card) : ∃ k ∈ S, ∃ k' ∈ S, k ≠ k' ∧ P.codeOf k = P.codeOf k'
theorem obs_congr {d b p : ℕ} (P : KeyProc d b p) (k k' : Key d b) (J : Finset (Fin d))
    (hread : ∀ (q : ℕ) (hq : q < p), P.next q hq (fun s => P.obs k s.val _) ∈ J)
    (heq : ∀ j ∈ J, k' j = k j) : P.valsAt k' = P.valsAt k
theorem exists_obs_eq_of_lt {d b p : ℕ} (hb : 2 ≤ b) (hp : p < d) (P : KeyProc d b p)
    (k : Key d b) : ∃ k' : Key d b, k' ≠ k ∧ P.valsAt k' = P.valsAt k
theorem unit_key_collision {d p : ℕ} (hp : p < d) (P : KeyProc d 2 p) :
    ∃ j : Fin d, P.valsAt (Function.update (fun _ => 0) j ⟨1, by omega⟩) = P.valsAt (fun _ => 0)
-- attainment
theorem radixProc_sortsAllKeys {d b : ℕ} : SortsAllKeys (radixProc d b)
theorem probes_tight (d b : ℕ) (hb : 2 ≤ b) :
    (∀ (p : ℕ) (P : KeyProc d b p), SortsAllKeys P → d ≤ p) ∧ (∃ P : KeyProc d b d, SortsAllKeys P)
theorem radix_sorts_Key (d b : ℕ) (l : List (Key d b)) :
    (radixSort d b (fun k => k) l).Perm l ∧ (radixSort d b (fun k => k) l).Pairwise (KeyLe d b)
theorem radix_sorts_Key_strict (d b : ℕ) {l : List (Key d b)} (hnd : l.Nodup) :
    (radixSort d b (fun k => k) l).Pairwise (KeyLt d b)
theorem radix_passes (d n b : ℕ) :
    ((List.range d).map (fun _ => passCost n b)).length = d ∧
      radixCost d n b = d * (n + b) ∧ radixComparisons d n b = 0
-- the contrast, with numbers
theorem two_digit_probes (n : ℕ) (hn : 2 ≤ n) :
    (∀ (p : ℕ) (P : KeyProc 2 n p), p < 2 → ¬ SortsAllKeys P) ∧
      (∃ P : KeyProc 2 n 2, SortsAllKeys P) ∧ Fintype.card (Key 2 n) = n ^ 2 ∧
      Real.logb n (Fintype.card (Key 2 n)) = 2
theorem radix_cost_le_comparison_cost (N : ℕ) (hN : 65536 ≤ N) {t : Tree N}
    (ht : Correct (α := ℕ) t) :
    ∃ x : Fin N → ℕ, Function.Injective x ∧ (radixCost 2 N N : ℝ) ≤ (cost t x : ℝ)
theorem wordram_probes (n w : ℕ) (hw : 0 < w) :
    (∀ (p : ℕ) (P : KeyProc n (2 ^ w) p), p < n → ¬ SortsAllKeys P) ∧
      (∃ P : KeyProc n (2 ^ w) n, SortsAllKeys P) ∧
      Real.logb ((2 : ℝ) ^ w) (Fintype.card (Key n (2 ^ w))) = (n : ℝ)
```

**Three deviations from the contract, all reported rather than silent.**

1. `def Key` is `abbrev Key`.  With a `def`, typeclass search does not look through it,
   so `Fintype (Key d b)`/`DecidableEq (Key d b)` are not found and `card_Key` does not
   even elaborate.  `abbrev` makes it a transparent type synonym; the type is still
   `Fin d → Fin b`, nothing is weakened.
2. `passes_lower` needs `2 ≤ b`.  As stated in the contract (`hp : p < d` only) it is
   **false**: for `b ≤ 1` the key domain is a subsingleton, every list is already sorted,
   and a `0`-probe plan sorts (`passes_lower_needs_two` proves both a `b = 1` and a `b = 0`
   instance, with `p = 0 < d`).  `2 ≤ b` is the exact hypothesis.
3. `card_le_pow_probes` takes the transcript map `t : Key d b → Probe d b p` as an
   argument (the contract's `…` placeholders).  Only the *values* of a transcript are
   counted: the positions are the plan's own choices, so `#(Probe d b p) = (b * d) ^ p`
   would count the algorithm's decisions as information.  The exponent is `p`.

**Where `⌈log_b U⌉` stops being the answer** (`unit_key_collision`, found while trying to
prove the general-`U` converse).  Tightness in `probes_tight` is tightness for the *whole*
domain `U = b ^ d`, and it cannot be upgraded to an arbitrary `U`-element set of keys: in
`Key d 2` the `d + 1` keys `{0, e_1, …, e_d}` have `⌈log_2(d+1)⌉ ≪ d`, yet no `p < d`
probes separate them — whatever `p` positions a plan reads on the zero key, some unit key
`e_j` sits on an unread position and is indistinguishable from zero (`unit_key_collision`,
from `obs_congr`).  The information-theoretic `log_b U` is the right answer for "the whole
`b`-ary digit domain", not for "any `U` keys": a probe must *read all the digits* of a key
to be sure of it, and no clever code can be chosen by the plan instead.

**Not proved, and why.**  The general-`U` converse (false in this model, see above).
Nothing about the *optimality of radix sort's* `d(n + b)` constant; nothing about `p ≥ d`
probes for a plan that is only required to sort inputs with *distinct* keys (that is a
weaker requirement, `SortsAllKeys` is the model of "sorts every list"); no *average-case*
version for probes (the counting engine `Core.Entropy` is available but not wired up — the
worst case is what the contract asked for); no formal comparison model inside this lane
(the separation is prose + the reuse of
`Comparison.LowerBound.exists_input_cost_ge_quarter` in `radix_cost_le_comparison_cost`).

**Integrator TODOs.**  Add `SortBounds/Projects/Domain/{Model,Lower,Radix,Contrast}` to the
umbrella `SortBounds.lean`; add the headline theorems (`probes_tight`, `passes_lower`,
`card_le_pow_probes`, `radix_sorts_Key`, `wordram_probes`, `radix_cost_le_comparison_cost`)
to `scripts/axioms.lean`; update the dashboard row for this lane.
