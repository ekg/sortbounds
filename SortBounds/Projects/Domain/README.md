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

* (empty)
