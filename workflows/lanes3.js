// Round 3: two lanes, multi-hour. Every stage carries an explicit deadline.
const ROOT = "/home/bot/sortbounds";
const H5 = 5 * 60 * 60 * 1000;
const H1 = 1 * 60 * 60 * 1000;

const common = (lane) => [
  `Repository: ${ROOT} (Lean 4.35.0-rc2, Mathlib pinned, built). READ AGENTS.md FIRST.`,
  `You own EXACTLY ONE directory: SortBounds/Projects/${lane}/.`,
  `Do NOT edit anything outside it (not lakefile.toml, not SortBounds.lean, not docs/PROGRESS.md,`,
  `not Core/Comparison/Instances, not other lanes). Do NOT run git. Do NOT run "lake build".`,
  `Validate with: cd ${ROOT} && lake env lean SortBounds/Projects/${lane}/<File>.lean`,
  `If your own lane's oleans are missing, concatenate your files into one /tmp file and elaborate that.`,
  `Python is allowed ONLY to SEARCH for a certificate (e.g. a decision tree) and print it as a Lean`,
  `literal; the certificate itself must be checked by the Lean kernel. No python for anything else,`,
  `and never let a python run be your validation of the result.`,
  `READ FIRST: AGENTS.md, docs/STRUCTURE.md, SortBounds/Projects/${lane}/README.md, and the lane's files.`,
  `Namespace: SortBounds.Projects.${lane}. HARD RULES: no sorry, no admit, no axiom, no native_decide.`,
  `Never weaken or rename a contract signature; report instead. You have HOURS: do not stop at the`,
  `first difficulty, and keep every landed file compiling.`,
  `Report: files, exact signatures proved (verbatim), what is not proved and why, integrator TODOs.`,
].join("\n");

const review = (lane) => [
  `Read-only review of a Lean 4 lane in ${ROOT}. Do not edit, do not run git.`,
  `You MAY run: cd ${ROOT} && lake env lean SortBounds/Projects/${lane}/<File>.lean`,
  `Start from SortBounds/Projects/${lane}/README.md (contract) and AGENTS.md. Cite file:line.`,
  `1. Contract: every signature the README lists as landed exists exactly? Any weakened/renamed?`,
  `2. Meaningfulness: vacuous, rfl-by-construction, unsatisfiable hypotheses, or a "certificate"`,
  `   that is not actually checked by the kernel (e.g. a tree whose correctness is asserted)?`,
  `3. Trust: sorry/admit/axiom/native_decide/foreign imports? Is any python output load-bearing?`,
  `4. Prose: quote sentences claiming more than the theorems state.`,
  `5. Next step: the single concrete lemma that best advances the next milestone.`,
  `Output: numbered PASS/CONCERN/FAIL, then fixes ordered by severity.`,
].join("\n");

const board = await runs.lanes([
  {
    key: "sn-six",
    stages: [
      {
        key: "impl",
        label: "SN: explicit optimal trees for n = 6, 7 (S 6 = 10, S 7 = 13)",
        agent: "worker",
        timeoutMs: H5,
        task: common("SN") + "\n\n" + [
          `TASK: extend the M2 results from n = 5 to n = 6 and n = 7.`,
          `Land, in new files (e.g. Six.lean, Seven.lean):`,
          `  theorem S_six : S 6 = 10`,
          `  theorem S_seven : S 7 = 13`,
          `Lower bounds are free: S_lower gives ⌈log2 6!⌉ = ⌈log2 720⌉ = 10 and`,
          `⌈log2 5040⌉ = 13 (both `+ "`by decide`" + ` on Nat.clog). Upper bounds need explicit`,
          `decision trees of depth 10 (720 leaves) and 13 (5040 leaves) whose leaves are the`,
          `720 / 5040 permutations — the known-optimal comparison sorts of 6 and 7 elements.`,
          `Reuse Verify.lean: netTree (turn a comparator list into a Tree), and`,
          `correct_of_forall_run_xOfPerm (correctness checked on the n! canonical inputs by`,
          `decide — this is the kernel check that makes the tree trustworthy).`,
          `A practical route: a sorting NETWORK for 6 elements of size 12 exists (Batcher) but`,
          `S(6) = 10 (< network size 9? check), so you need an ADAPTIVE tree: build it from the`,
          `Ford-Johnson schedule (pair, sort winners, insert losers in Jacobsthal order) or take`,
          `the known 10-comparison decision tree from Knuth TAOCP 5.3.1 Fig. 12-ish; either way`,
          `encode it as nested `+ "`Tree.node`" + ` applications and let `+ "`decide`" + ` verify it.`,
          `Writing a small search (python) that emits the tree literal is allowed; the Lean`,
          `kernel must check the emitted tree via correct_of_forall_run_xOfPerm.`,
          `Land Six.lean first; Seven.lean only if Six is green. Do not touch existing files`,
          `except appending to README's `+ "`## Log`" + `.`,
        ].join("\n"),
      },
      { key: "review", label: "Review SN six/seven lane", agent: "reviewer", timeoutMs: H1, task: review("SN") },
    ],
  },
  {
    key: "fj-attain",
    stages: [
      {
        key: "impl",
        label: "FordJohnson: attainment of the insertion and merge-insertion counts",
        agent: "worker",
        timeoutMs: H5,
        task: common("FordJohnson") + "\n\n" + [
          `TASK: the lane proves only `+ "`≤`" + ` bounds; this lane turns them into equalities where`,
          `true, starting from the reviewer's suggested lemma. New file Attain.lean:`,
          `  theorem insertCount_attains (k : ℕ) :`,
          `      ∃ x : ℕ, ∃ l : List ℕ, l.length = k ∧ (insertCount x l).1 = Nat.clog 2 (k + 1)`,
          `  theorem loserCost_attains (m : ℕ) (hm : 1 ≤ m) :`,
          `      ∃ l : List ℕ, l.length = m ∧ (insertAll m ...).1 = loserCost m   (shape your call)`,
          `  theorem fjCountJ_attains (n : ℕ) (hn : 2 ≤ n) :`,
          `      ∃ l : List ℕ, l.length = n ∧ (fjSortJ l).1 = fjCountJ n`,
          `The last one is the real prize: it would let the lane say the bound is EXACT. If it is`,
          `false for some n (check small cases by computation first — e.g. n = 2..7 by deciding`,
          `the maximum of `+ "`(fjSortJ l).1`" + ` over a search of inputs), STOP and report with the`,
          `counterexample and the best true statement (e.g. `+ "`≥ fjCountJ n - c`" + ` for explicit c,`,
          `or attainment for the insertion phase only).`,
          `Existing tools: Insertion.lean (insertCount, clog_half_add_one, clog_split_add_one),`,
          `Count.lean, Jacobsthal.lean (jacInsertCost, fjCountJ), JacobsthalInsertion.lean`,
          `(fjSortJ, insertBatch_count). Append to README's `+ "`## Log`" + ` only.`,
        ].join("\n"),
      },
      { key: "review", label: "Review FordJohnson attainment lane", agent: "reviewer", timeoutMs: H1, task: review("FordJohnson") },
    ],
  },
]);

return board.map((lane) => ({
  key: lane.key,
  state: lane.state,
  failedStage: lane.failedStage,
  stages: lane.stages.map((s) => ({ key: s.key, state: s.state, ok: s.ok, runId: s.runId, verdict: s.verdict })),
}));
