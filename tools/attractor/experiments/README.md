# experiments — measuring the gap `γ − ⌈δ⌉` across string families

One question: on which strings is `γ = ⌈δ⌉` (so that the NP-hard `γ` would be computable in
`O(n)`), and where it is not, how fast does the gap grow with `n`?  The answer, the tables and
every qualification are in **`docs/research/gamma-delta-table.md`**; this directory is what
produces and re-verifies them.

Nothing here re-implements a measurement: `δ` comes from `tools/attractor/instance.py`
(repmeter's `delta_exact`) and the bracket `[lb, ub]` on `γ` from `tools/attractor/anytime.py`
(`search`, or its own primitives re-scheduled when `search` crashes — see the note's §9).

| file | what it is |
| --- | --- |
| `run_families.py` | the sweep: 117 texts in 13 family groups, each row an exact `δ` and a certified bracket; writes `results.json` and the five `*.md` table blocks |
| `check.py` | independent re-verification: rebuilds every text from its spec, recomputes `δ` exactly, re-checks every `ub` with the definition-level verifier, re-derives every `lb` from its certificate (packing re-certified, completed DFS re-run), and requires the note's tables to be the generated ones verbatim |
| `run.sh` | `sh run.sh` = sweep + checks under `timeout` (~2.5 min); `--no-doc` tolerates a stale note, `--quick` skips the DFS re-proofs |
| `results.json` | every row with its text spec, `δ` as a fraction, `lb`, `ub`, the attractor, the packing family, and the provenance of each bound |
| `verdicts.md` `table.md` `trends.md` `rates.md` `summary.md` | the generated table blocks, quoted verbatim in the note |

```sh
sh run.sh                    # full: sweep (~2 min) then check (~30 s), non-zero on failure
python3 run_families.py --only "thue,square" --base-budget 3   # a slice, for a smoke test
python3 check.py --quick     # the checks minus the DFS re-proofs
```

Rules this directory inherits from the parent tools: stdlib only, `timeout` on every run, an
assertion of progress in every loop, and no number printed without a certificate — a case that
does not finish in its budget is printed as `not computed` with the reason, never estimated.
`*.md` in this directory is generated: regenerate it with `run_families.py`, do not edit it.
