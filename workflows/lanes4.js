// Round 4: review the landed SortTree lane, and open the FJA-tree lane (8h).
const ROOT = "/home/bot/sortbounds";
const H8 = 8 * 60 * 60 * 1000;
const H2 = 2 * 60 * 60 * 1000;
const H1 = 1 * 60 * 60 * 1000;

const review = (lane, files) => [
  `Read-only review of a Lean 4 lane in ${ROOT}. Do not edit files, do not run git.`,
  `You MAY run: cd ${ROOT} && lake env lean ${files}`,
  `Lane: SortBounds/Projects/${lane}/. Start from its README (contract) and AGENTS.md.`,
  `Cite file:line for every finding.`,
  `1. Contract: does every signature the README lists as landed exist exactly (name, binders, statement)?`,
  `2. Meaningfulness / vacuity: is any theorem rfl-by-construction, are the hypotheses of the`,
  `   headline results satisfiable, and is the depth bound really about the constructed tree`,
  `   (not silently about a different object)?`,
  `3. Trust: sorry/admit/axiom/native_decide/foreign imports anywhere in the lane?`,
  `4. Prose: quote any docstring or README sentence claiming more than the theorems state.`,
  `5. Next step: the single concrete lemma that best advances the next milestone.`,
  `Output: numbered PASS/CONCERN/FAIL verdicts, then concrete fixes ordered by severity.`,
].join("\n");

const board = await runs.lanes([
  {
    key: "sorttree-review",
    stages: [
      {
        key: "review",
        label: "Review the landed SortTree lane (S_sandwich)",
        agent: "reviewer",
        timeoutMs: H1,
        task: review("SortTree", "SortBounds/Projects/SortTree/Main.lean"),
      },
    ],
  },
  {
    key: "fj-tree",
    stages: [
      {
        key: "impl",
        label: "FjTree: decision tree of merge-insertion, optimality for n <= 11",
        agent: "worker",
        timeoutMs: H8,
        task: [
          `Repository: ${ROOT} (Lean 4.35.0-rc2, Mathlib pinned, built). READ AGENTS.md FIRST,`,
          `then SortBounds/Projects/FjTree/README.md — that is your contract, with exact target`,
          `signatures and the milestone ladder (M0..M3).`,
          `You own EXACTLY ONE directory: SortBounds/Projects/FjTree/.`,
          `Do NOT edit anything outside it (not lakefile.toml, not SortBounds.lean, not docs/PROGRESS.md,`,
          `not Core/Comparison/Instances, not other lanes — other lanes have live writers right now).`,
          `Do NOT run git. Do NOT run "lake build". Validate with:`,
          `  cd ${ROOT} && lake env lean SortBounds/Projects/FjTree/<File>.lean`,
          `If your own lane's oleans are missing, concatenate your files into one /tmp file and elaborate that.`,
          `Python may only emit a certificate that the Lean kernel then checks; it is never validation.`,
          ``,
          `READ: SortBounds/Comparison/Bridge.lean (liftTree, liftTree_correct, liftTree_depth_le),`,
          `SortBounds/Projects/SortTree/Main.lean (insertTree, insertPerm_sorts, insertTree_depth_le,`,
          `rankOf; also sortTree as a worked example of iterating substitution),`,
          `SortBounds/Projects/FordJohnson/{Jacobsthal,JacobsthalInsertion}.lean (jac, jacInsertCost,`,
          `fjCountJ, fjCountJ_eq_clog_factorial, and how the schedule's windows are counted),`,
          `SortBounds/Projects/SN/Basic.lean (S, S_le_iff, S_lower).`,
          ``,
          `GOAL: build the decision tree of merge-insertion and derive`,
          `  S_le_fjCountJ : SN.S n <= fjCountJ n`,
          `  S_eq_clog : 4 <= n -> n <= 11 -> SN.S n = Nat.clog 2 (Nat.factorial n)`,
          `The whole lane is the tree: once `+ "`fjTree_depth_le`" + ` exists, the last two are one-liners.`,
          `Land M0 (insertion-only tree through the substitution API) first; it validates the machinery.`,
          `Then M1 (pairing + recursive winners) and M2 (loser insertion in Jacobsthal order with the`,
          `schedule's windows). M3 = the contract theorems.`,
          `You have ~8 hours. Keep every landed file compiling. No sorry, no admit, no axiom, no`,
          `native_decide. If a target resists, land the strongest true statement you can and report`,
          `precisely which invariant broke.`,
          ``,
          `Report: files, exact signatures proved (verbatim), what is not proved and why, integrator TODOs.`,
        ].join("\n"),
      },
      {
        key: "review",
        label: "Review the FjTree lane",
        agent: "reviewer",
        timeoutMs: H2,
        task: review("FjTree", "SortBounds/Projects/FjTree/Main.lean"),
      },
    ],
  },
]);

return board.map((lane) => ({
  key: lane.key,
  state: lane.state,
  failedStage: lane.failedStage,
  stages: lane.stages.map((s) => ({ key: s.key, state: s.state, ok: s.ok, runId: s.runId, verdict: s.verdict })),
}));
