// Three stages, sequential: theory note → implementation → independent review.
const ROOT = "/home/bot/sortbounds";
const H4 = 4 * 60 * 60 * 1000;

const theory = await runs.run("theory", {
  label: "Theory of guaranteed-bound attractor constructions",
  agent: "worker",
  timeoutMs: H4,
  cwd: ROOT,
  task: [
    `Research + theory task. Repository ${ROOT}. READ AGENTS.md, then tools/approx/README.md (the contract) and docs/research/space.md (prior cited material: the hierarchy delta <= gamma <= b <= c <= z <= g_rl <= g, the separations, and the NP-hardness discussion).`,
    `You own EXACTLY ONE file: docs/research/attractor-approx.md. Do not touch other files, do not run git.`,
    ``,
    `GOAL: a theory note on *guaranteed-bound* constructions for the minimum string attractor gamma, and the structure that might beat them. Sections:`,
    `1. State of the art, with primary citations and verdicts (PROVED / STATED-UNPROVED / OPEN / UNVERIFIED): minimum attractor NP-hardness and what is known about approximation (the O(log k) via set cover; APX-completeness results for constant k; what is known/open for the FULL attractor, k = n); the constructive bounds gamma <= z (LZ77, Kempa-Prezza Lemma 3.7), gamma <= g (SLP, Thm 3.5), z = O(delta log(n/delta)) (KNP II.2), delta <= gamma (KNP II.4), and hence the O(log n) ratio. Quote the theorem statements verbatim where you can fetch them.`,
    `2. The structure. For fixed k, factor S[i..i+k) is covered by positions p in [i, i+k) — consecutive positions — so a single-k instance is "stab the unions of length-k intervals"; if a factor's occurrences are pairwise disjoint it becomes interval stabbing (exactly solvable). Write out precisely: (a) the set-cover formulation (universe = distinct factors, sets = positions), (b) what the consecutive-ones structure buys for a single k, (c) why the union over all k breaks it, (d) the integrality gap question for this specific family, (e) the hardness question that actually matters for us: NP-hardness for k >= 3 is stated for general alphabets — what is known for sigma = 2?`,
    `3. Certified lower bounds beyond delta: the packing bound (factors pairwise non-co-coverable ⇒ gamma >= k), LP-dual bounds, bounds from z, r, chi, n, sigma. Which are computable in linear/near-linear time, and what is known about their tightness?`,
    `4. Falsifiable conjectures, each with the experiment that settles it. At minimum: (i) "the LZ-based construction is within a constant factor of gamma on highly repetitive corpora" — measurable on Fibonacci/Thue-Morse/HPRC-like texts; (ii) "the LP integrality gap on this family is O(1)" — measurable on small instances by solving the LP by hand/exhaustive for n <= 14; (iii) "the packing bound exceeds delta on some family" — measurable on Thue-Morse. State each so that a failed experiment refutes it.`,
    `5. A one-page summary of what an implementer should build, with the ratio each construction gives and its cost.`,
    ``,
    `RULES: do NOT fabricate. Every theorem needs a citation (arXiv/DOI/URL) or must be marked MY-INFERENCE. If you cannot verify a claim (e.g. the exact APX-hardness statement, or the sigma=2 hardness), say so and state what would settle it. This note will be used to write an implementation and, later, a Lean contract, so precision about *which* bound is proved matters more than completeness.`,
    `Output: write docs/research/attractor-approx.md (<= 2200 words), then report: the three load-bearing citations, the strongest *provable* ratio statement, and everything you could not verify.`,
  ].join("\n"),
});

const impl = await runs.run("impl", {
  label: "Implement and verify the LZ77 → attractor construction",
  agent: "worker",
  timeoutMs: H4,
  cwd: ROOT,
  output: "approx-results.md",
  task: [
    `Implementation task. Repository ${ROOT}. You own EXACTLY ONE directory: tools/approx/. Python 3, stdlib only. No git, no Lean edits, no other directories.`,
    `Read AGENTS.md, tools/approx/README.md (contract) and docs/research/attractor-approx.md, which the theory stage just wrote. Treat its verdict labels as authoritative: implement only constructions it marks PROVED, and label anything else HEURISTIC.`,
    ``,
    `DELIVER:`,
    `1. lz.py — an LZ77 parse (greedy, hash-chain matcher; O(n) expected) producing phrases (len, dist) or literals, with an honest complexity note.`,
    `2. attractor_from_lz.py — the construction of an attractor from an LZ77 parse with |Γ| <= z, following the cited construction. Document each step: which position is emitted per phrase, and why every distinct factor has an occurrence crossing Γ.`,
    `3. verify.py — an INDEPENDENT definition-level verifier (every distinct factor has an occurrence crossing Γ), not a reuse of the construction's bookkeeping.`,
    `4. check.py — self-tests (must exit non-zero on failure): on all binary strings of length <= 12, the constructed Γ passes verify.py, and delta <= |Γ| <= z (integer z = phrase count). Report the worst ratio.`,
    `5. run.py — a results table: for each of "ababa", "mississippi", Fibonacci F_k (k = 10..18), Thue-Morse 2^12 and 2^16, a^n for n in {100, 1000}, and random binary 4096: n, z, delta, |Γ_LZ|, |Γ_LZ|/z, |Γ_LZ|/delta, and exact gamma where n <= 14. Timeout every run.`,
    ``,
    `HARD RULES: no fabricated numbers; if a construction does not actually give |Γ| <= z, say so loudly rather than adjusting the claim. Every loop must assert progress. Keep every run under a `+ "`timeout 120`" + `. Report: files, the table, whether |Γ| <= z held everywhere (and the worst case if not), and what the integrator must know.`,
  ].join("\n"),
});

const review = await runs.run("review", {
  label: "Review the theory note and the construction",
  agent: "reviewer",
  timeoutMs: 2 * 60 * 60 * 1000,
  cwd: ROOT,
  task: [
    `Read-only review in ${ROOT}. Do not edit, do not git. You MAY run 'cd ${ROOT} && timeout 120 python3 tools/approx/check.py' and the measure scripts.`,
    `Scope: docs/research/attractor-approx.md (theory note) and tools/approx/ (implementation), against tools/approx/README.md.`,
    `The central claim to audit is the ratio: delta <= gamma <= z <= 4(delta log(n/delta)+delta), hence an O(log n) approximation, delivered CONSTRUCTIVELY by an LZ77 parse. Check:`,
    `1. Is each step cited and correctly directed? (delta <= gamma, gamma <= z, z = O(delta log(n/delta)) — in particular, is "gamma <= z" the correct direction and is the construction the one the citation gives?)`,
    `2. Does the implementation actually satisfy |Γ| <= z on every tested input, and does the independent verifier agree? Is the verifier independent (definition-level) or a reuse of the construction?`,
    `3. Is any ratio or claim in the note stronger than what is proved — in particular any suggestion that this beats O(log n), or that the construction is optimal, or that an untested conjecture is a theorem?`,
    `4. Are the "falsifiable conjectures" actually falsifiable as stated, and does the implementation test the ones it can?`,
    `5. Trust/process: any fabricated number, any loop without a progress assertion, any run without timeout?`,
    `Output: numbered PASS/CONCERN/FAIL, then fixes ordered by severity.`,
  ].join("\n"),
});

return { theory: theory.outputReference, impl: impl.outputReference, implSummary: impl.output, review: review.output };
