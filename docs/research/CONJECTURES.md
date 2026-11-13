# Conjecture register

Every conjecture this programme has produced, with the evidence for it, the single most decisive
experiment, and its current status.  A conjecture leaves this list only by being proved (→
`RESULTS.md`) or refuted (→ the refuting instance, certified).

Labels: **OPEN** (no attempt), **EVIDENCE** (data, no proof), **REFUTED** (witness cited),
**NARROWED** (surviving special case after a refutation).

---

## C1 — `γ ≤ 3·δ` on binary text

*Equivalently: `δ` is a 3-approximation of `γ` at `σ = 2`.  `δ` is computable in `O(n)`; `γ` is
NP-hard.*

| | |
| --- | --- |
| **evidence** | `γ/δ ≤ 2.33` over 49 certified rows, `n = 20 … 384`, all brackets closed; `3.0` in the `δ = 2` slice (`n = 96, 160`); exhaustive `n = 20, 21, 22` (`2^20, 2^21, 2^22` strings) give `γ − ⌈δ⌉ ≤ 3` and `γ ≤ 5` with `δ = 2` |
| **why plausible** | KNP's `γ = O(δ log(n/δ))` is proved through `z` (LZ77), and a `log` is lost at the macro-scheme step; the binary case may simply never realise that loss |
| **decisive experiment** | a certified instance with `γ/δ > 3` — one row would kill it.  Cheapest hunting ground: `δ = 2`, `n = 256 … 4096`, where the ratio is already `3.0` |
| **status** | **EVIDENCE** |
| **consequence if true** | with T5 (`γ/LP* ≤ γ/δ`) the attractor LP gap is `≤ 3` on binary; an `O(n)`-time 3-approximation for `γ` at `σ = 2` would exist |
| **consequence if false** | the KNP log factor is attained at `σ = 2`, and `δ` gives nothing beyond polylog |

## C1′ — the sharp form: `γ ≤ (3/2)·δ + O(1)` on binary

*Post-hoc fit to the 14 certified rows of `gamma-delta-growth.md` (`n = 20 … 384`,
`δ = 2.8 … 24.6`), not independent evidence — recorded because it unifies C1 and C3.*

| δ | 2.8 | 3.0 | 3.9 | 5.0 | 6.9 | 10 | 16 | 19.8 | 24.6 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `γ/δ` | 3.00 | 2.33 | 2.31 | 2.00 | 1.74–1.88 | 1.70 | 1.50 | 1.52 | 1.42 |

The ratio **decreases monotonically in `δ`** (with one tie), the classic signature of
`γ = c·δ + O(1)` rather than `γ = c·δ` exactly: least squares gives `γ ≈ 1.35·δ + 2.8` with maximum
residual `1.81` over all 14 rows.

| | |
| --- | --- |
| **why it matters** | `LP* ≥ δ` is a theorem (T5), so `γ ≤ (3/2)δ + O(1)` **implies the LP gap is `≤ 3/2` asymptotically** — which is exactly the band the LP measurements occupy (`15/11 = 1.364`, `7/5 = 1.4`).  C3 (the `γ=3, δ=2` family tending to `3/2`) would then be the same phenomenon seen from the LP side |
| **decisive experiment** | the `δ = 2` slice at `n = 256 … 4096`: it is the *worst* case for the ratio (`3.0`), so it decides between "additive constant" (`γ` stays `≤ 6`) and "slow growth" |
| **status** | **EVIDENCE**, and post-hoc (a fit to points that were collected for other reasons) |

## C2 — the attractor LP gap is bounded by a constant on binary text

| | |
| --- | --- |
| **evidence** | measured max `7/5 = 1.4` at `n = 31`; `γ/δ ≤ 2.33`; `LP* ≥ δ` (theorem) |
| **relation** | implied by C1 + T5, so C2 is *strictly weaker* than C1 |
| **decisive experiment** | same as C1; or an instance with `γ/LP* > 2.33` while `γ/δ` stays smaller |
| **status** | **EVIDENCE** |

## C3 — the LP gap in the `γ = 3`, `δ = 2` family tends to `3/2`

*Observation that generated it: with `γ = 3` fixed and `δ = 2`, `LP*` drifts down toward the `δ`
floor: `9/4` (n=12) → `11/5` (n=13) → `13/6` (n=21, 27).*

| | |
| --- | --- |
| **evidence** | three lengths, monotone drift; `LP* ≥ δ = 2` is a theorem, so the ratio is `≤ 3/2` in this family by construction |
| **decisive experiment** | minimise `LP*` over `γ = 3`, `δ = 2` instances at `n = 30 … 60`: does it reach `2`, stall at `2 + c`, or is `γ = 3` unattainable at larger `n`? |
| **status** | **EVIDENCE** (weak — three points) |

## C4 — `γ_k` of a de Bruijn word is independent of the order once `m ≥ k`

*Computed: `γ₂(B_m) = 2` for every `m`; `γ₃(B_m) = 3`; `γ₄(B₅) = 5`.*

| | |
| --- | --- |
| **evidence** | `k = 2, 3` for all `m ≤ 7`; `k = 4` at `m = 5` only |
| **decisive experiment** | `γ₄(B₆)` — solver did not finish in 200 s, so this needs a better algorithm than definition-level search |
| **status** | **EVIDENCE** (thin) |
| **note** | if true it would say `γ_k(B_m) = γ_k(B_k)`, making the hierarchy a function of `k` alone on de Bruijn words |

## C5 — `γ = max packing` on binary text of the sizes we can certify

| | |
| --- | --- |
| **evidence** | every record instance in `gamma-delta-growth.md` has `lb = ub` with `lb_source = packing`, and `check.py` re-verified 49/49 packings |
| **counter-evidence** | **not** true in general: `lp-gap.md`'s table has 16 rows where the bracket did not close with the packing bound (`lb_source` breakdown: delta 11, packing 38, delta+packing 61, exact tail 7) |
| **status** | **REFUTED** as a general claim; open as a binary-small-`n` claim |
| **why it matters** | if the packing bound were within a constant of `γ` on binary, C1 would follow from a purely combinatorial statement about intersecting hypergraphs |

---

## Refuted, kept for the record

| conjecture | refuted by |
| --- | --- |
| `γ ≤ ⌈δ⌉ + 2` | `Packing.s32_*`: `γ = 6`, `δ = 3` at `n = 32` (kernel-checked) — and `+3` is being refuted at `n = 48` |
| `γ ≤ γ₂ + c` for a constant `c` | `AttractorK.gamma_ratio_ge_isDeBruijn`: `γ/γ_k → ∞` for every fixed `k` (kernel-checked) |
| `γ = ⌈δ⌉` in general | Thue–Morse prefixes 25–59, TM `n = 4, 5` (`gamma-equals-delta.md`) |
| `γ = ⌈2^k/k⌉` on de Bruijn words | `γ₄(B₅) = 5 > 4` (computed) |
| `γ` is a function of the `d`-profile | 41 of 123 profile classes split (exhaustive, binary `n ≤ 12`) |
| `15/11` is the maximum LP gap | `7/5` at `n = 31` (certified) |
| `b a^{2^j−1} b` separates `γ` from `δ` | `γ = δ = 2` at every length (computed) — my own error |
| a binary VERTEX COVER gadget reduces to `γ` | three explicit constructions, all inverted (`sigma2-gadget.md`) |

---

## The one thing to run next

**C1's decisive experiment**, `δ = 2` at `n = 256 … 4096`.  Every other live item is either a
research proof (C1, C2) or a small optimisation (C3, C4).  A single certified instance with
`γ/δ > 3` would refute C1 and settle C2 negatively in one stroke; a credible absence of one at
`n = 4096` would make C1 the central conjecture of the programme.
