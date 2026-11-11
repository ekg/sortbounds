# Repository structure and the rules that keep parallel work sane

## The decision

**One Lake project, directory per sub-project, namespace per sub-project.**
Rationale: every sub-project needs Mathlib (7.6 GB of oleans). Separate Lake
packages would duplicate that per project; one project shares it, shares the
toolchain pin, and still gives clean namespacing and build slicing.

```
sortbounds/
├── lakefile.toml                 one project, pinned Mathlib rev
├── SortBounds.lean               umbrella import (what currently builds)
├── SortBounds/
│   ├── Core/                     reusable, Mathlib-only, no sorting in sight
│   │   └── Branching.lean        bits-per-probe: #outcomes ≤ b ^ #steps
│   ├── Comparison/               the comparison model + Ω(n log n) instance
│   │   └── Basic Tree Aggregate WorstCase Stirling LowerBound Average
│   │       General Examples
│   ├── Instances/                other models, to show the boundary
│   │   └── Radix.lean MergeSort.lean
│   └── Projects/                 research lanes, one directory each
│       ├── FordJohnson/          verified merge-insertion + exact count
│       ├── SN/                   certified exact minimum comparison counts S(n)
│       ├── XY/                   sorting X+Y (Fredman/Berlekamp)
│       ├── BenOr/                algebraic decision trees
│       └── SAIS/                 suffix arrays: cost model (queued)
├── docs/
│   ├── PROGRESS.md               the dashboard — status of every lane
│   ├── STRUCTURE.md              this file
│   └── PRIOR-ART.md              who else has done what
└── scripts/axioms.lean           trust artifact: #print axioms
```

Module names follow the path: `SortBounds/Projects/SN/Table.lean` is
`SortBounds.Projects.SN.Table`, in `namespace SortBounds.Projects.SN`.

## Why directories-per-project, not per-package

* A lane is a *directory*, so `git mv` can promote it to its own repository if
  it outgrows this one. Nothing else in the tree needs to change.
* A lane is a *namespace*, so lemma names cannot collide across lanes.
* A lane is a *build slice*: `lake build SortBounds.Projects.SN` builds only that
  lane (plus its imports). Add a `[[lean_lib]]` entry when a lane stabilises.

## Rules for parallel work (learned the hard way)

1. **One writer per directory.** Lanes never touch each other's files, and never
   touch `SortBounds/Core`, `SortBounds/Comparison`, `SortBounds/Instances`,
   or the umbrella `SortBounds.lean`.
2. **Only the integrator runs `lake build`; only the integrator runs `git`.**
   Lane workers validate with `lake env lean SortBounds/Projects/<Lane>/<File>.lean`,
   which elaborates without writing oleans and therefore cannot race.
3. **Interface before fanout.** A lane's `README.md` states the exact target
   signatures (copy-pasteable Lean). A worker may strengthen a target, never
   weaken or rename it silently — report instead.
4. **`PROGRESS.md` has one editor.** Lane workers update their own README's
   `## Log`, never the dashboard. The integrator merges status up.
5. **No `sorry`, ever.** A lane that cannot finish a milestone stops, reports
   what blocked it, and leaves the weaker *true* statement proved instead.
6. **Milestones are cumulative and checkable.** `M0` must compile before `M1`
   starts; a lane that reaches M1 but not M2 is a success, not a failure.

## What belongs where

| Kind of thing | Where |
| --- | --- |
| A lemma usable by any model (counting, logs, bits) | `SortBounds/Core/` |
| A model + its lower bound | `SortBounds/<Model>/` |
| A concrete algorithm demonstrating a model boundary | `SortBounds/Instances/` |
| A research question with a target theorem | `SortBounds/Projects/<Name>/` |
| Status, ownership, blockers | `docs/PROGRESS.md` |
| Claims about other people's work | `docs/PRIOR-ART.md` |
