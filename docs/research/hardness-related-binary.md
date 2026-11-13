# A2 — Hardness and easiness of problems *near* minimum attractor on a binary alphabet

**PROVED** = read in the paper; **ATTRIBUTED** = P on unread Q; **OPEN** = source says unknown;
**MY-INFERENCE** = mine; **UNVERIFIED(-ABSENCE)** = unchecked / nothing found.

## 0. The answer

Minimum-phrase LZ77 is **not hard at all** (greedy is optimal, §2); the smallest suffixient set
`χ` is **polynomial** (§5); the proved-hard neighbours need a fixed alphabet of **size ≥ 17** (§1),
a **growing** alphabet (§3–4), or a different variant (LZ78/LZ-End, §2). No binary hardness is
inherited by any argument I found, the transfer to binary reaching a factor 6 where `8569/8568` is
needed (§1, §7); `γ ≤ b ≤ z ≤ g` carries **no** complexity implication (§7).

## 1. Smallest grammar / shortest SLP (`g`)

* **PROVED (unbounded `σ`)**: NP-hard, no PTAS (Charikar et al., *IEEE TIT* 2005;
  Storer–Szymanski, *JACM* 1982; confirmed in arXiv:1908.06428 §1).
* **PROVED (fixed `σ`)**: **NP-complete and APX-hard for a fixed alphabet of size ≥ 17** (Casel et
  al., *Theory Comput. Syst.* 2021, doi:10.1007/s00224-020-10013-w: "even if the alphabet is fixed
  and has size of at least 17"). ICALP'16 said 24; the boundary lies in `17 ≥ σ ≥ 2`.
* **OPEN (`σ = 2`)**: ibid., §1: "it is open whether this problem is NP-hard. This is one of the
  most intriguing unsolved problems in the area of grammar-based compression"; and to prove it "one
  would have to reduce the factor 6 to at most 8569/8568".
* **PROVED (transfer that exists)**: binary ratio `c` ⇒ arbitrary-alphabet ratio `24c + ε`
  (Arpe–Reischuk, DCC 2006, doi:10.1109/dcc.2006.59), improved to `6c` by Bannai et al.
* **UNVERIFIED**: Chen, arXiv:2610.32298v2, **Thm 1.4** — "SGP over the binary alphabet {0,1} is
  NP-complete", answering Casel et al. §6.1. Mechanism: an anchor bit per codeword plus a
  boundary-synchronising code (`m = 128`), giving **Lemma 6.3** (a grammar for the encoding yields
  one with "`|H↓| ≤ |H|`") — an *additive* gap, then amplified. Unreviewed; it also invokes an
  external "Boolean tensor contraction theorem".

## 2. LZ77 minimum phrases — the brief's premise is false

* **PROVED (correction)**: for the standard definition (a phrase must occur earlier; source may
  overlap) greedy longest-match is **optimal**, so the minimum phrase count is computable in
  **linear time**. Navarro arXiv:2004.02781 §3.2.2: "This greedy parsing method can be proved to
  be optimal … among all left-to-right parses … [Lempel and Ziv 1976, Thm. 1]"; also
  Navarro–Ochoa–Prezza arXiv:1803.09517: "`z` … the optimal one when phrases can be copied only
  from the left … in linear time with a greedy algorithm". No alphabet dependence, no
  approximation ratio. The no-overlap `z_no` is *also* greedy-optimal (survey: "Thm. 10 with
  p = 1" of Storer–Szymanski 1982).
* **PROVED (what *is* hard)**: optimal **LZ-End** — "a decision version of computing the optimal
  LZ-End parsing is NP-complete by showing a reduction from the vertex cover problem"
  (arXiv:2302.02586, Thm 3), greedy/optimal approaching 2 on a **binary** family.
* **ATTRIBUTED**: optimal (off-line) **LZ78** is NP-hard — De Agostino & Storer, *IPL*
  59(3):169–174, 1996, per Bannai et al.: "the NP-hardness of computing the optimal version of the
  LZ78 variant".
* **MY-INFERENCE**: "optimal parsing is hard" folklore concerns variants with a side constraint
  (boundary rule, dictionary, bounded access) or bidirectional parses; the unidirectional problem
  has an exchange argument — why `z` is easy and `b` hard.

## 3. Minimum bidirectional macro scheme (`b`)

* **PROVED (three abstracts; original ATTRIBUTED)**: computing `b` is NP-complete —
  Navarro–Ochoa–Prezza: "Since computing `b` is NP-complete, a popular gold standard is `z`";
  arXiv:1910.02151: "though it is NP-complete to compute". Navarro's survey attributes it to
  **Gallant, *String compression algorithms*, PhD thesis, Princeton 1982** (also Storer–Szymanski
  1982); Gallant's alphabet **UNVERIFIED** (thesis unread) ⇒ binary status
  **UNVERIFIED-ABSENCE**.
* **PROVED**: the only approximation-type result is `z = O(b log(n/b))`, tight (Navarro–Ochoa–
  Prezza: "we prove that `z = O(b log(n/b))` … where `z = Ω(b log n)`"). Also `b ≤ 4s`, `b = O(χ)`,
  with `s` (smallest SES) "NP-hard and `(1+ε)`-inapproximable" (arXiv:2604.04377, unreviewed).

## 4. Set cover with interval structure, and what breaks

* **PROVED/folklore** (`attractor-approx.md` §2b): with one occurrence per factor each
  constraint is "pick a position in a contiguous range" — interval stabbing, solved exactly by
  right-endpoint greedy, the LP being integral via the consecutive-ones/TU property
  (Fulkerson–Gross 1965).
* **What breaks**: with ≥ 2 occurrences each constraint is a **union of equal-length intervals**
  and no TU structure survives. `k`-attractor is NP-complete for `k ≥ 3` (Kempa–Prezza, STACS
  2018, Thm 4.2, "a reduction from `k`-set cover") **and at `k = 2`**: "NP-complete and APX-hard
  for any `k ≥ 2`" (Fuchs–Whittington, STACS 2024, doi:10.4230/LIPIcs.STACS.2024.41) via
  *colorful edge cover*. This **corrects `attractor-approx.md` §1.2**, which records `k = 2` as
  open (KPRR18's status, resolved 2023–24).
* **PROVED — restrictions restoring tractability**: (i) fixed `k`, small `σ`: candidates collapse
  to `≤ min{n, σ^{2k−1} + 2k − 2}` classes (KPRR18 Lem. 13), exact `γ_k` in
  `O(n) + exp(O(σ^k log σ^k))` (Thm 29); (ii) bounded number of grammar rules, handled "by
  encoding it as a problem on graphs with interval structure" (Casel et al.). Interval structure
  is the tractable core. **OPEN**: the LP integrality gap of this cover (in-repo question B).

## 5. Suffixient sets (`χ`) — polynomial, binary included

* **PROVED**: the minimum suffixient set is computable in **linear time** — "simple linear-time
  online algorithms to compute smallest suffixient sets" (arXiv:2506.05638, SPIRE 2025), in "the
  transdichotomous RAM model over polynomial-size integer alphabets": the
  alphabet is a machine-model assumption, so `σ = 2` is an instance, not an obstruction; likewise
  for "a suffixient set of minimum cardinality" (arXiv:2506.08225).
* **PROVED**: `χ ≤ 2r`; `χ ≤ σ + 2` on episturmian words (`χ ≤ 4` on Fibonacci); `χ` incomparable
  with most copy-paste measures; `χ(T)/χ(T^R) ≤ 2` (Fujimaru–Navarro–Romana–Urbina).
  Reachability holds (`O(χ)`-size SES, Shibata–Bannai).
* **MY-INFERENCE**: `χ` is easy where `γ` is hard because of quantifier order — a suffixient set
  needs **some** witness per suffix-tree edge, an attractor must cover **all** occurrences. KPRR18
  Lem. 11 phrases `γ` over tree edges too, so universality is the difficulty.

## 6. "At most `k` / exactly `k`" and parameterised complexity

* **PROVED**: `k`-attractor NP-complete for `k ≥ 3` with growing `σ` ⇒ no `poly(n)` algorithm for
  unbounded `σ` ⇒ **MY-INFERENCE**: not FPT in `k` alone (constant `k = 3` would be FPT).
  **PROVED**: exact `γ_k` in `O(n) + exp(O(σ^k log σ^k))` (KPRR18 Thm 29) ⇒ FPT in `(k, σ)` with
  a near-linear factor in `n`. **MY-INFERENCE**: with `σ = 2` the exponential is `exp(O(2^k k))`,
  so **`γ_k` is polynomial-time computable on binary strings for every fixed `k`** — binary
  hardness at fixed `k` cannot exist; any binary hardness must live at `k = n`.
* **PROVED**: SGP is **W[1]-hard** in the number of rules, yet "if the number of nonterminals … is
  bounded by a constant, then the smallest grammar problem can be solved in polynomial time … on
  graphs with interval structure" (Casel et al.). **MY-INFERENCE**: consistent only in the *XP*
  reading (degree depends on the bound).
* **UNVERIFIED-ABSENCE**: `W[2]`-hardness of "`γ ≤ t`" in `t`; FPT/kernel results for SGP in the
  size budget. Branching over all covering positions of an uncovered factor is `O(n^t)` —
  MY-INFERENCE, not a citable theorem.

## 7. Is binary hardness inherited from any of these?

**MY-INFERENCE (negative)**: SLP hardness stops at `σ ≥ 17` (binary open, obstruction "6 vs
8569/8568"); minimum-phrase LZ77 is polynomial; LZ-End/LZ78 hardness does not cover the
unconstrained problem; `b`'s reduction alphabet is unread; `χ` is polynomial. **No proved
binary-hard neighbour is left to inherit from.**

**MY-INFERENCE**: `γ ≤ b ≤ z ≤ g` transfers **nothing** about complexity — inequalities between
optima, not reductions, and none either way is known (UNVERIFIED-ABSENCE). Even a verified binary
NP-hardness for SGP would **not** give binary hardness for `γ`, nor conversely.

**PROVED — every attractor hardness reduction grows the alphabet**: KP18's `Σ` has
`Θ(uk + t + t')` symbols; Fuchs–Whittington's 2-attractor proof uses `m + 6 + n` symbols for an
`n`-variable, `m`-clause formula — both unary-encoding gadgets, what binary input forbids.
**MY-INFERENCE**: a binary proof must separate `m` colours with `O(log m)`-length blocks while
keeping the optimum within an additive constant; that is Chen's programme (§1).

## 8. Unverified items and what would settle them

| item | status | what settles it |
| --- | --- | --- |
| SGP on `σ = 2` (Chen Thm 1.4) | UNVERIFIED | re-derive Lem. 6.2–6.3 (empty projections, RHS accounting) + amplification; run Appendix B's checker |
| Gallant 1982 reduction alphabet | UNVERIFIED | read the thesis, or a restatement of it |
| `W[2]`-hardness of `γ ≤ t` | UNVERIFIED-ABSENCE | parameterised Set Cover reduction, as occurrences |
| `b` on binary | UNVERIFIED-ABSENCE | binary version of Gallant's gadget, or a poly algorithm |

## 9. Sources

DOI 10.1109/TIT.2005.850116 · 10.1007/s00224-020-10013-w (abstract in full) · 10.1109/dcc.2006.59 ·
10.4230/LIPIcs.STACS.2024.41 · 10.1016/0020-0190(96)00068-3 (attributed only) · arXiv:1908.06428
§1 · 2610.32298 §§1,6,7 · 2004.02781 §3.2 · 1803.09517 · 2302.02586 · 1710.10964 · 2304.06523 ·
1910.02151 · 1803.01695 (via `attractor-approx.md`) · 2207.02571 · 2604.04377 · 2506.08225 ·
2506.05638. Fulkerson–Gross 1965 (TU; folklore, unread).
