# One inequality, many models

This repository's reusable content is the *frame*, not the `Ω(n log n)` theorem.
This document states the frame once and then lists the models it has been
instantiated in, what the bound becomes in each, and how each model escapes it.
Every claim below names the Lean declaration that backs it.

## The frame

An algorithm that decides among `N` outcomes by steps with at most `b` possible
results needs at least `log_b N` steps, provided distinct outcomes leave
distinct transcripts:

```
#outcomes ≤ b ^ #steps                      -- SortBounds.Core.Branching.card_le_pow_of_prefixFree
log_b #outcomes ≤ #steps                    -- SortBounds.Core.Branching.logb_le_of_le_pow
```

It is Kraft's inequality: a prefix-free set of words over a `b`-letter alphabet
has `∑ b ^ (-length) ≤ 1` (Mathlib: `InformationTheory.IsPrefixFree.
finsetSum_one_div_card_pow_length_le_one`). If instead of a worst case you want an
*expectation*, the same weights give it: `∑ b ^ (-cost) ≤ 1` implies the mean cost
is at least `log_b` of the number of outcomes — in the binary comparison case that
is `SortBounds.Comparison.Aggregate.sum_pow_cost_le_one` and
`SortBounds.Comparison.Average.avg_cost_ge_log2_factorial`.

**The whole content is: how many bits does one step buy you?** Everything else is
bookkeeping. So when someone claims to beat `n log n`, the only question that
matters is *what are they allowed to look at per step, and how many outcomes does
that have?*

## The models

| Model | `b` | step cost | bound becomes | escapes by |
| --- | --- | --- | --- | --- |
| comparison sort (decision tree) | 2 | one comparison | `≥ log₂ n!` comparisons — `Comparison.Tree.factorial_le_two_pow_depth`, `exists_input_cost_ge_quarter` | nothing, within the model |
| sorting network (oblivious) | 2 | one comparator | `≥ log₂ n!` **comparators** — `Instances.Network.factorial_le_two_pow_length_of_sortsAll` | depth, not work: AKS has `O(log n)` depth *and* `Θ(n log n)` comparators |
| counting / radix sort | `b` buckets | one pass over `n+b` items | `d·(n+b)` operations, **zero** comparisons — `Instances.Radix.radixCost_eq_passes` | reads keys instead of comparing; for `U = n^{O(1)}` this is linear |
| word-RAM, `w`-bit probe | `2^w` | one word read | `log_{2^w} N` probes | wider probes: vEB `O(n log log U)`, fusion trees `O(n log n / log log n)`, Han–Thorup `O(n√log log n)` |
| algebraic decision tree | 3 (`<`,`=`,`>`) | one polynomial test | `log₃` of the cells | Ben-Or's topological bound still gives `Ω(n log n)` for distinctness — `Projects/BenOr` (model + statement only) |
| suffix sorting with LCP | 2 | `1 + characters past the known LCP` | `Θ(n log n)` *inspections*, not `Θ(n²)` — `Projects/SAIS.cmpFrom_inspectCount_le`, the `aⁿ` contrast | SA-IS/DC3 sort integer *ranks*, i.e. they take the radix door |
| `X + Y` sums | 2 | one sum comparison | the generic `N = n²` bound — `Projects/XY.factorial_mul_card_le_two_pow_depth` | additive structure: Fredman's `O(n²)` comparison scheme (open how to make it an algorithm) |

The last row is the honest warning attached to the frame: the generic bound applies
to a procedure that sees `N` unordered values, and `X+Y` is *not* such a procedure.
Additive structure restricts which orderings occur, so `Ω(n² log n)` is false there
and the counting argument says nothing. That is why `Projects/XY` states its M0
theorem as "the generic `N`-item bound, re-indexed" and nothing more.

## What the bound does *not* say

* **Preprocessing is free in none of our theorems, and unlimited in the real
  world.** With a table of size `U` you can sort `n` items in `O(n)` (counting
  sort); the frame says nothing because the table is not part of the procedure.
* **Randomisation.** A randomised algorithm is a distribution over deterministic
  ones; fixing the coins gives a `Tree`, so the deterministic bound applies to
  each instantiation, hence to the expectation. (Argued, not formalised.)
* **Adaptivity and partial information.** If the input is promised to be nearly
  sorted, the right `N` is not `n!` but the number of *consistent* orderings —
  the poset/entropy version of the frame (Saks–Werman, Kahn–Kim). Our theorems
  all take `N = n!`, i.e. the promise-free case.
* **Parallelism.** The bound is on *steps*, so something that fits many steps into
  one time unit beats it in time, not in work. This is the sorting-network row.

## Where the open problems actually live

All of these are in the same family as the frame (decision trees and their
transcripts), and all are open; none is a formalisation gap:

* **exact `S(n)`** — known for `n ≤ 22`; open for `n ≥ 23`, and the second-order
  term `S(n) = ⌈lg n!⌉ + o(n)` is itself a research question. `Projects/SN` has
  `n ≤ 5` machine-checked, in both the depth and the comparison-count readings.
* **merge-insertion's exact count and attainment** — `Projects/FordJohnson` has the
  algorithm, the closed form for `n ≤ 22` and the table `F(4..11)`; *attainment*
  (an input that actually costs `F(n)`) is being attempted in a lane.
* **sorting `X+Y`** (Berlekamp/Fredman; TOPP #41) and **3SUM** (TOPP #11, conjectured
  no subquadratic algorithm) — the structure-changes-the-answer frontier.
* **Bose–Nelson**: optimal sorting-network size is known only up to 12 wires
  (`s(11)=35`, `s(12)=39`); optimal depth further, but bounded.
* **evasiveness** (Aanderaa–Karp–Rosenberg): every nontrivial monotone graph
  property is evasive — proved for prime powers by group actions on decision
  trees, open in general. Same object as `Tree`, different label set.
* **the lower-bound barrier**: outside order-type and topological arguments
  (Ben-Or) there are essentially no superlinear unconditional lower bounds. That
  is the honest answer to "is there no escape" — it is a frontier, not a theorem.

## How to instantiate the frame in a new model

1. Fix the transcript: what does one step of the algorithm record?
2. Prove the transcript map is injective on the inputs you must distinguish, and
   that transcripts are prefix-free (equivalently: the decision structure is a
   tree/DAG with leaves).
3. Get `#inputs ≤ b ^ max cost` from `Core.Branching`.
4. Say *precisely* which inputs the procedure must distinguish — this is where
   `X+Y` and partial-information problems differ from sorting, and where most
   false claims originate.

`Comparison/Aggregate.card_le_pow_of_cost_le` is step 3 done directly on a tree by
induction; `Instances.Network.reachPerms` is the same count via "at most `2^k`
products of swap/no-swap choices". Both are the frame; neither is special.
