// Four research lanes: one worker stage each, then a fresh-context review stage.
// Contract for every lane lives in SortBounds/Projects/<lane>/README.md.
const ROOT = "/home/bot/sortbounds";

const common = (lane) => [
  `Repository: ${ROOT} (Lean 4.35.0-rc2, Mathlib pinned by lake-manifest.json, already built).`,
  `You own EXACTLY ONE directory: SortBounds/Projects/${lane}/. Create your .lean files there.`,
  `Do NOT edit anything outside it: not lakefile.toml, not SortBounds.lean, not SortBounds/Core,`,
  `not SortBounds/Comparison, not docs/PROGRESS.md. Do NOT run git. Do NOT run "lake build"`,
  `(the integrator builds; concurrent builds race in .lake). Validate only with:`,
  `  cd ${ROOT} && lake env lean SortBounds/Projects/${lane}/<File>.lean`,
  ``,
  `READ FIRST: docs/STRUCTURE.md, docs/PROGRESS.md, and SortBounds/Projects/${lane}/README.md.`,
  `That README is your CONTRACT: it lists the exact target signatures. Copy them verbatim`,
  `(namespace SortBounds.Projects.${lane}; module SortBounds.Projects.${lane}.<File>).`,
  `You may add helper lemmas; you may NOT rename, weaken, or drop a contract signature.`,
  `Useful existing material: SortBounds/Core/Branching.lean (bits per probe),`,
  `SortBounds/Comparison/Tree.lean (decision trees, cost, Correct),`,
  `SortBounds/Comparison/Examples.lean (concrete small trees), SortBounds/Instances/MergeSort.lean`,
  `(counted merge sort). Importing those is fine; editing them is not.`,
  ``,
  `HARD RULES: no sorry, no admit, no axiom, no native_decide for general theorems.`,
  `If a target is blocked, STOP, prove the closest true statement, and report exactly what failed;`,
  `never leave a hole. Land M0 first and make sure it compiles before starting M1.`,
  `Time-box: finish M0 and M1. Start M2/M3 only if M0+M1 compile with time to spare.`,
  ``,
  `Report at the end: (a) files created, (b) exact signatures proved (verbatim),`,
  `(c) what you did not prove and why, (d) anything the integrator must do`,
  `(import into SortBounds.lean, add a [[lean_lib]] entry, doc fixes).`,
].join("\n");

const review = (lane) => [
  `Read-only review of a freshly written Lean 4 lane in ${ROOT}. Do not edit files, do not run git,`,
  `do not run "lake build" (you may run "lake env lean <file>" to re-check a claim).`,
  `Lane: SortBounds/Projects/${lane}/. Start from SortBounds/Projects/${lane}/README.md (the contract)`,
  `and docs/STRUCTURE.md, then read every .lean file in the lane.`,
  `Check, citing file:line:`,
  `1. Does every contract signature exist with the exact name and statement? List any that are`,
  `   missing, renamed, weakened, or whose statement is trivialised/vacuous.`,
  `2. Is each theorem meaningful (hypotheses satisfiable, conclusion non-trivial, no definition`,
  `   crafted so that the theorem is rfl)?`,
  `3. Any sorry/admit/axiom/native_decide in the lane? Any imports outside Mathlib + SortBounds?`,
  `4. Do docstrings claim more than the theorems state? Quote overclaims.`,
  `5. Would the next milestone be possible from here? Name the concrete next lemma.`,
  `Output: numbered PASS/CONCERN/FAIL verdicts, then a bullet list of concrete fixes ordered by`,
  `severity. Be blunt and specific; do not rewrite code.`,
].join("\n");

const board = await runs.lanes([
  {
    key: "fj",
    stages: [
      { key: "impl", label: "FordJohnson: binary insertion + merge-insertion with count", agent: "worker", task: common("FordJohnson") },
      { key: "review", label: "Review FordJohnson lane", agent: "reviewer", task: review("FordJohnson") },
    ],
  },
  {
    key: "sn",
    stages: [
      { key: "impl", label: "SN: exists_correct_tree + S(n) + S 0..3", agent: "worker", task: common("SN") },
      { key: "review", label: "Review SN lane", agent: "reviewer", task: review("SN") },
    ],
  },
  {
    key: "xy",
    stages: [
      { key: "impl", label: "XY: pairSums, counting corollary, naive counted sort", agent: "worker", task: common("XY") },
      { key: "review", label: "Review XY lane", agent: "reviewer", task: review("XY") },
    ],
  },
  {
    key: "benor",
    stages: [
      { key: "impl", label: "BenOr: algebraic decision tree model + cell bound", agent: "worker", task: common("BenOr") },
      { key: "review", label: "Review BenOr lane", agent: "reviewer", task: review("BenOr") },
    ],
  },
]);

return board.map((lane) => ({
  key: lane.key,
  state: lane.state,
  failedStage: lane.failedStage,
  stages: lane.stages.map((s) => ({
    key: s.key,
    state: s.state,
    ok: s.ok,
    runId: s.runId,
    verdict: s.verdict,
    outputReference: s.outputReference,
  })),
}));
