// Three lanes, each swarmed, each ending in an independent review.
//
//   A. is minimum-attractor hard on a BINARY alphabet? (every reduction uses a growing alphabet)
//   B. what is the LP integrality gap of this instance family? (nobody has measured it)
//   C. when is gamma = ceil(delta)? (the empirical pattern the anytime search found)
const ROOT = "/home/bot/sortbounds";
const H3 = 3 * 60 * 60 * 1000;
const H4 = 4 * 60 * 60 * 1000;
const H2 = 2 * 60 * 60 * 1000;

const RULES = [
  `Repository ${ROOT}. READ AGENTS.md first; it records how this project fails.`,
  `HARD RULES: never fabricate; every theorem needs a citation (arXiv/DOI/URL) or must be`,
  `labelled MY-INFERENCE; mark UNVERIFIED claims and say what would settle them. Python: stdlib`,
  `only, 'timeout' on every run, assert progress in every loop (two lanes lost hours to hangs).`,
  `Do not edit files outside your assigned path. Do not run git.`,
].join("\n");

// ---------------------------------------------------------------- lane A
const a1 = await runs.run("a1", {
  label: "Attractor hardness: exact statements and the alphabet question",
  agent: "worker",
  timeoutMs: H3,
  cwd: ROOT,
  output: "docs/research/hardness-attractor.md",
  task: [
    RULES,
    `You own EXACTLY ONE file: docs/research/hardness-attractor.md.`,
    ``,
    `QUESTION A1: what exactly is proved about the complexity of the minimum string attractor,`,
    `and does any of it hold for a BINARY alphabet (sigma = 2)?`,
    `1. Quote verbatim, with citations: the NP-completeness statement for k-attractors`,
    `   (Kempa-Prezza STOC'18 / Kempa-Policriti-Prezza-Rotenberg ESA'18), the APX-completeness for`,
    `   constant k, and the hardness-of-approximation result (Cor 4.4, ratio ~1+1/11809). Be precise`,
    `   about WHICH problem each is: k-attractor for a fixed k, or the full attractor (k = n)?`,
    `2. For each reduction you can actually read: what alphabet does it use? Quote the line that`,
    `   fixes the alphabet size (e.g. "our reduction requires a large alphabet"). This is the crux:`,
    `   if every hardness reduction needs sigma growing with n, then for sigma = 2 nothing is known.`,
    `3. Report what IS known for sigma = 2, if anything: exact attractors for small fixed k and`,
    `   sigma, the O(n) algorithm for fixed k and sigma, the status of k = 2, and any polynomial`,
    `   algorithm for binary strings.`,
    `4. Say plainly whether "minimum attractor is NP-hard for sigma = 2" is PROVED, OPEN, or`,
    `   UNVERIFIED, and what a reduction would have to overcome (binary gadgets for set cover).`,
    `End with a short "what would settle it" list. <= 1800 words.`,
  ].join("\n"),
});

const a2 = await runs.run("a2", {
  label: "Related problems: what is hard on a binary alphabet?",
  agent: "worker",
  timeoutMs: H3,
  cwd: ROOT,
  output: "docs/research/hardness-related-binary.md",
  task: [
    RULES,
    `You own EXACTLY ONE file: docs/research/hardness-related-binary.md.`,
    ``,
    `QUESTION A2 (a different angle on the same question): which problems *close to* minimum`,
    `attractor are known hard or known easy on a BINARY alphabet?`,
    `Cover, with exact statements and citations:`,
    `* shortest SLP / smallest grammar (NP-hard: over what alphabet? what about binary?);`,
    `* LZ77 parsing into the minimum number of phrases (NP-hard; alphabet dependence;`,
    `  approximation results);`,
    `* minimum macro scheme / bidirectionality (b);`,
    `* set cover restricted to consecutive-ones or interval structure (poly), and what breaks`,
    `  when sets are unions of intervals;`,
    `* suffixient sets (chi, Cenzato et al. 2024) — is minimising chi polynomial? On what alphabet?`,
    `* anything about the "at most k" or "exactly k" variants and their parameterised complexity`,
    `  (FPT in k? in sigma?).`,
    `The purpose is to know whether binary-alphabet hardness is inherited from any of these, and`,
    `which structural restrictions are known to restore tractability. Distinguish PROVED / OPEN /`,
    `UNVERIFIED throughout; label your own inferences. <= 1500 words.`,
  ].join("\n"),
});

const aRev = await runs.run("a-review", {
  label: "Review the hardness notes",
  agent: "reviewer",
  timeoutMs: H2,
  cwd: ROOT,
  task: [
    `Read-only review in ${ROOT}. Do not edit, do not git.`,
    `Scope: docs/research/hardness-attractor.md and docs/research/hardness-related-binary.md.`,
    `Check, citing file:line: (1) is every quoted hardness statement attributed to the right paper`,
    `and the right problem variant (k-attractor vs full attractor; decision vs approximation)?`,
    `(2) Is the alphabet hypothesis of each reduction actually as claimed, or is it asserted?`,
    `(3) Does any note claim NP-hardness for sigma = 2 without a reduction, or claim tractability`,
    `without an algorithm? (4) Is every MY-INFERENCE labelled? (5) Is anything fabricated?`,
    `Output: numbered PASS/CONCERN/FAIL then fixes by severity.`,
  ].join("\n"),
});

// ---------------------------------------------------------------- lane B
const b1 = await runs.run("b1", {
  label: "Measure the LP integrality gap of the attractor cover family",
  agent: "worker",
  timeoutMs: H4,
  cwd: ROOT,
  output: "docs/research/lp-gap.md",
  task: [
    RULES,
    `You own EXACTLY ONE directory: tools/gap/ (plus the single note docs/research/lp-gap.md).`,
    ``,
    `QUESTION B: what is the integrality gap of the set-cover LP for the minimum attractor?`,
    `If it is O(1), a constant-factor approximation is within reach; if it is Theta(log n), the`,
    `log-factor bounds are essentially inherent for LP-based methods. NOBODY has measured this.`,
    `Method:`,
    `1. Build the instance exactly as specified: universe = distinct factors; set_p = factors with`,
    `   an occurrence crossing position p. Reuse tools/repmeter (SA/LCP, exact delta) and`,
    `   tools/attractor (instance building, independent verifier) via sys.path rather than`,
    `   rewriting; they exist and are tested.`,
    `2. Solve the LP relaxation EXACTLY in rational arithmetic (write a small two-phase simplex`,
    `   over fractions.Fraction; instances are tiny). Do not approximate the LP and do not use`,
    `   floating point to decide a bound. Sanity: LP* <= gamma, and LP* >= delta.`,
    `3. Compute the exact integer optimum gamma for the same instances (exhaustive for small n)`,
    `   and report gap = gamma / LP* over (a) ALL binary strings n <= 12, (b) ALL ternary strings`,
    `   n <= 8, (c) Fibonacci and Thue-Morse words up to the largest n your LP handles,`,
    `   (d) random binary strings. Report the MAXIMUM gap, the argmax instance, and the`,
    `   distribution — not just the mean.`,
    `4. Also measure the gap of the SINGLE-k instance (universe = length-k factors only) for`,
    `   k = 1, 2, 3: the fixed-k case has consecutive-ones structure, so its gap should be 1 (or`,
    `   prove it is). If the fixed-k gap is 1 and the full gap is large, say exactly that: it`,
    `   localises the difficulty.`,
    `Deliverables: tools/gap/{instance.py,simplex.py,gap.py,check.py,README.md}, the note, and a`,
    `results table with the max gap and its witness. 'check.py' must exit non-zero if any sanity`,
    `invariant fails (LP* <= gamma, LP* >= delta, simplex answers verified by duality).`,
    `Nothing printed without a certificate; no floating point in any bound; timeout every run.`,
  ].join("\n"),
});

const bRev = await runs.run("b-review", {
  label: "Review the LP-gap measurement",
  agent: "reviewer",
  timeoutMs: H2,
  cwd: ROOT,
  task: [
    `Read-only review in ${ROOT}. Do not edit, do not git. You MAY run 'timeout 300 python3`,
    `tools/gap/check.py' and the gap script.`,
    `Scope: tools/gap/ and docs/research/lp-gap.md.`,
    `The claim to audit is a MEASURED integrality gap, so check the solver above all:`,
    `(1) Is the LP actually solved exactly (rational arithmetic end to end, no float)?`,
    `(2) Is the LP the relaxation of the *same* problem (same universe, same sets), or of a`,
    `weaker one? (3) Is the integer optimum exact (exhaustive) at the sizes reported, or a`,
    `heuristic being compared to an LP? (4) Does the note report max and argmax, or only a mean?`,
    `(5) Any number without a reproducible command behind it? (6) Is the fixed-k claim (gap 1 or`,
    `not) supported by measurement or only asserted?`,
    `Output: numbered PASS/CONCERN/FAIL, then fixes by severity.`,
  ].join("\n"),
});

// ---------------------------------------------------------------- lane C
const c1 = await runs.run("c1", {
  label: "Theory: when is gamma = ceil(delta)?",
  agent: "worker",
  timeoutMs: H3,
  cwd: ROOT,
  output: "docs/research/gamma-equals-delta.md",
  task: [
    RULES,
    `You own EXACTLY ONE file: docs/research/gamma-equals-delta.md.`,
    ``,
    `QUESTION C: the anytime search in tools/attractor found the bracket CLOSED on every`,
    `highly repetitive instance tried (mississippi [4,4], abracadabra [5,5], Thue-Morse 2^8/2^10`,
    `[4,4], Fibonacci F_14/F_18 [2,2]) because gamma = ceil(delta) there, while on random text`,
    `gamma is well above delta. What is the theory?`,
    `1. What is known: gamma/2 <= delta <= gamma is false; the true relation is delta <= gamma`,
    `   and gamma = O(delta log(n/delta)) (KNP). Exact statements with citations. Is there any`,
    `   family of strings for which gamma = delta is PROVED? (Unary? periodic? runs? Sturmian?`,
    `   Fibonacci? Thue-Morse? de Bruijn? — check the attractor literature for small attractors`,
    `   of structured words.)`,
    `2. Formulate the sharpest true conjecture you can defend, e.g. "gamma(S) <= delta(S) + f(n)`,
    `   for run-length-bounded S" or "gamma = ceil(delta) whenever delta(S) = d_1(S)/1" — and`,
    `   say what would refute it. Be careful: gamma <= ceil(delta) is FALSE in general (give`,
    `   the separation that kills it), so any conjecture must be restricted.`,
    `3. Which structural quantity controls the gap? Candidates: the number of distinct`,
    `   factors of length 1 and 2; the number of distinct "crossing" patterns; periodicity;`,
    `   the ratio r/delta; the number of distinct factors per length (the d_k profile).`,
    `   Propose the most likely, with an experiment that separates them.`,
    `4. State the practical consequence: if gamma = ceil(delta) on repetitive corpora, then`,
    `   gamma is computable in O(n) there and the anytime search is unnecessary; if not, the`,
    `   gap's growth rate is the thing to measure.`,
    `<= 1800 words. No fabricated theorem: every claim PROVED (cited) / MY-CONJECTURE / UNVERIFIED.`,
  ].join("\n"),
});

const c2 = await runs.run("c2", {
  label: "Experiment: gamma vs delta across families",
  agent: "worker",
  timeoutMs: H4,
  cwd: ROOT,
  output: "docs/research/gamma-delta-table.md",
  task: [
    RULES,
    `You own EXACTLY ONE directory: tools/attractor/experiments/ (create it) plus the single`,
    `file docs/research/gamma-delta-table.md. Do not modify tools/attractor/*.py or tools/approx/.`,
    `Import them via sys.path.`,
    ``,
    `TASK: measure the gap gamma - delta across string families, with certified bounds.`,
    `Use tools/attractor (anytime.py: certified bracket [lb,ub], monotone yields) and`,
    `tools/repmeter (exact delta) — do not reimplement either.`,
    `Families, each at several sizes (as far as the budget allows):`,
    `* Fibonacci words, * Thue-Morse words, * a^n, * (ab)^n, * Sturmian/rational periodic words,`,
    `* de Bruijn sequences of order k, * random over sigma = 2 and 4, * "run-length" texts`,
    `  (a^L b^L ...), * concatenations of a random string with itself (S S), and S S^R.`,
    `For each: n, delta (exact fraction), lb (certified), ub (certified), gamma where exact`,
    `(n <= 14 or bracket closed), and whether the bracket CLOSED. Then:`,
    `1. Tabulate where gamma = ceil(delta), and where the gap grows.`,
    `2. Fit/eyeball how the gap scales with n on the families where it is nonzero — is it`,
    `   constant, sqrt(n), log n? Say plainly that this is an empirical trend, not a theorem.`,
    `3. Report the single most surprising row, and the one that most clearly REFUTES the naive`,
    `   conjecture "gamma = ceil(delta) for repetitive strings".`,
    `Deliverables: tools/attractor/experiments/run_families.py (+ a check.py that asserts every`,
    `reported bracket has verified endpoints), the results table in docs/research/`,
    `gamma-delta-table.md, and a run.sh. Timeout every run; assert progress; no fabricated rows —`,
    `if a case does not finish in budget, print "not computed" and say why.`,
  ].join("\n"),
});

const cRev = await runs.run("c-review", {
  label: "Review the gamma-vs-delta lane",
  agent: "reviewer",
  timeoutMs: H2,
  cwd: ROOT,
  task: [
    `Read-only review in ${ROOT}. Do not edit, do not git. You MAY run 'timeout 300 python3`,
    `tools/attractor/experiments/check.py'.`,
    `Scope: docs/research/gamma-equals-delta.md, docs/research/gamma-delta-table.md,`,
    `tools/attractor/experiments/.`,
    `Check: (1) is every "gamma = ..." claim backed by a CLOSED bracket (lb = ub, both verified),`,
    `or is an upper bound being reported as gamma? (2) Does the theory note propose a conjecture`,
    `that is actually false as stated (e.g. gamma <= ceil(delta) in general)? Quote the note if`,
    `so. (3) Are the tables reproducible from the scripts, and does check.py verify both ends?`,
    `(4) Is any empirical trend described as a theorem? (5) Any fabricated row?`,
    `Output: numbered PASS/CONCERN/FAIL, then fixes by severity.`,
  ].join("\n"),
});

return {
  laneA: { notes: [a1.outputReference, a2.outputReference], review: aRev.output },
  laneB: { note: b1.outputReference, summary: b1.output, review: bRev.output },
  laneC: { notes: [c1.outputReference, c2.outputReference], review: cRev.output },
};
