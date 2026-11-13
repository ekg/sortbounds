# `σ = 2` attractors: what the neighbour gadgets give

**Question.** Minimum attractor at `σ = 2`, `k = n` is OPEN (`hardness-attractor.md`). What do the
neighbours — SLP (`g`), LZ77 (`z`), bidirectional macro scheme (`b`), `k`-attractor — supply for a
*binary* gadget, and what do they leave unsolved?

**Labels.** PROVED = verbatim in the primary source (locator given). ATTRIBUTED = from this repo's
notes, primary unfetchable here. COMPUTATIONALLY-CHECKED = exact `γ`, certified solver, script and
command given. MY-CONJECTURE / UNVERIFIED as marked. The label sits on the *quotation*.

**Read here:** C16 = Casel et al., ICALP 2016, LIPIcs 55, 122:1–122:15; C21 = same authors, *Theory
Comput. Syst.* 65(2), **abstract only** (Springer full text bot-blocked). arXiv ids: KP18 1710.10964,
FW24 2304.06523, B23 2302.02586, KPRR18 1803.01695, N21 2004.02781, Ch26 2610.32298v2 (unreviewed).

---

## 1. The four neighbours: statement, source problem, alphabet sentence

### 1.1 SLP (`g`)

* PROVED-quote (C16 §3): Charikar et al. prove it "NP-complete by a reduction from the vertex cover
  problem"; "an approximation ratio better than 8568/8569 ≈ 1.0001 is not possible … assuming P ≠ NP".
* **Alphabet — crux** (PROVED-quote, C16 §3): "we encode the different vertices of a graph by single
  symbols and also use individual separator symbols (i. e., symbols with only one occurrence in the word
  to be compressed)."
* Successors (PROVED-quote, C16 Thm 3, Thm 7): "1-SGP is NP-hard, even for `|Σ| = 5`."; "SGP is
  NP-complete, even for alphabets of size 24."; C21 abstract: "it is shown that the smallest grammar
  problem remains NP-complete … even if the alphabet is fixed and has size of at least 17."
* Binary — ATTRIBUTED (`hardness-related-binary.md` §1): "it is open whether this problem is NP-hard";
  "one would have to reduce the factor 6 to at most 8569/8568". Ch26 (UNVERIFIED) claims closure: "we
  prove that SGP is NP-complete over a binary alphabet". Note also (PROVED-quote, C16 §1) that a
  published "size 3" claim did not survive: "a closer look into [21] does not confirm this".

### 1.2 Minimum LZ77 phrases (`z`)

* Nothing to inherit (PROVED-quote, N21 §3.2.1): "This greedy parsing method can be proved to be optimal
  … among all left-to-right parses" — alphabet-free, linear time, no ratio needed.
* What is hard is constrained: optimal LZ-End "is NP-complete … by showing a reduction from the vertex
  cover problem" (PROVED-quote, B23 abstract). **Alphabet** (PROVED-quote, B23 §3): "We identify each
  vertex `v_i` as a symbol `v_i` and each edge `e_i` as a symbol `e_i`." The authors pose binary as
  open (PROVED-quote, B23 §6): "Our reduction from the vertex cover problem uses a polynomially large
  alphabet. How can we construct a reduction with a small alphabet?" Binary work here is about ratios
  (PROVED-quote, B23 Thm 4): "There exists a family of binary strings such that the ratio `z_e/z_end`
  asymptotically approaches 2".

### 1.3 Bidirectional macro scheme (`b`)

PROVED-quote (N21 §3.3): "Instead, finding the smallest bidirectional macro scheme is NP-hard [Gallant
1982]." Neither that nor N21's grammar sentence beside it carries alphabet information ⇒ binary
UNVERIFIED-ABSENCE.

### 1.4 `k`-attractor

* PROVED-quote (KP18 Thm 4.2, source `k`-SET COVER): "For `k ≥ 3`, `k`-ATTRACTOR is NP-complete."
  FW24 Thm 9 (source: (3,B2)-SAT via colorful edge cover): "The 2-attractor problem is NP-complete."
* **Alphabet, in the neighbours' words.** KPRR18 §1 (PROVED-quote): "The problem remains NP-hard even
  under the restriction that only substrings of length at most `k` are captured by `Γ`, for any `k ≥ 3`
  and **on large alphabets**." KP18 Eq. (4) builds `Σ` from five symbol families indexed by `u`, `k`,
  `n_i`, so `σ = Θ(uk+t)`. FW24 (PROVED-quote): "It is vital that each vertex has a unique label so that
  each vertex uniquely corresponds to a 2-substring. For that reason, we need to introduce more symbols
  and pay attention that they are all covered."; "`Σ = C ∪ L ∪ L̄ ∪ X = {C_1,…,C_m} ∪ {L_1,L_2,L_3} ∪
  {L̄_1,L̄_2,L̄_3} ∪ {X_1,…,X_n}`".
* No fixed-`k` binary target (PROVED-quote, KPRR18 Thm 29, Cor. 7): `O(n) + exp(O(σ^k log σ^k))` —
  constant at `σ = 2`. A binary attack must target `k = n`.

---

## 2. Gadget mechanisms, transplantably

| reduction | "variable" | "clause" | "satisfaction" | symbols |
|---|---|---|---|---|
| C16 1-level | codeword `v̄_i` | block `#v̄_u#v̄_v#` | buying rule `#v̄_j#` | 5 |
| C16 multi-level | palindromic `f(i)⋆f(i)^R` | coloured blocks | nonterminal per codeword | 24 |
| KP18 | `x_t^{(1)}…x_t^{(k)}` | block `S_i` | extra position in `S_i` | `σ ≥ uk` |
| FW24 | symbol `X_a` | symbol `C_i` | marking `X_a` once | `m+n+6` |

**C16 1-level — the only 5-symbol reduction on record** (PROVED-quote, §3.1; glyphs per image): "We
define `Σ = {a, b, ◇, ★, #}` and `[◇] = ◇^{n³}`. For each `i` … we encode `v_i` by a word
`v̄_i ∈ {a, b}^{⌈log(n)⌉}` such that `v̄_i ≠ v̄_j` if and only if `i ≠ j`". The word repeats each vertex
cell `#v̄_i[◇]v̄_i#[◇]` `2^{⌈log n⌉+3}` times, each `#v̄_i#[◇]` `⌈log n⌉+1` times, each edge block
`#v̄_u#v̄_v#[◇]` twice, and ends `★[◇]^{n³}`. Satisfaction is buying the rule `#v̄_j#`; the exponents
make a vertex rule exactly break-even, so only edge blocks yield profit — "The grammar is smallest, if
every edge `#v̄_{j_{2i-1}}#v̄_{j_{2i}}#` is compressed by using a rule of the last
type; thus, those rules translate into a vertex cover." `◇^{n³}` is a huge *uniform* region making one
rule overwhelmingly profitable, `★` a unique cutter, `#` a delimiter. **`{a,b}` has no `★`.**

**C16 multi-level** (PROVED-quote, §3.2): "we use palindromic codewords `u ⋆ u^R`, where `⋆ ∈ Σ`" —
palindromy makes codewords prefix/suffix-free *and* cheapest built "from the middle"; colourings of the
square graph and of an auxiliary multigraph kill repeated *boundaries*.

**Ch26 (UNVERIFIED, unreviewed) — the only binary technique on record.** (i) A fixed-length binary code
with one **anchor bit** per codeword and boundary synchronisation, giving Lemma 6.2 (a factor spanning
≥2 anchors projects identically at every occurrence) and the Projection Theorem `|H↓| ≤ |H|`,
quantified as Thm 6.4: "`g_Σ(W) ≤ g_2(C(W)) ≤ g_Σ(W) + mq`". (ii) Amplification: "we first take `K =
D + 1` copies of the source graph, which amplifies the unit gap in the vertex cover size by a factor of
`K`", with `K − D = 1`.

**KP18** (PROVED, §4): element `t` gets `k` distinct symbols `x_t^{(1)}…x_t^{(k)}`, collection `C_i` gets a
block `S_i`; `2n_i+1` positions are forced inside `S_i`, `2n_i+2` also cover the element factors; `P_i`,
`R_i` cover nuisance factors "for free". The `(j)` superscripts make element factors occur **in `S_i`
only**; at `σ = 2` such factors recur at every compatible junction.

**FW24** (PROVED-quote, §4): each *vertex of the constraint graph* becomes a **symbol**, so "each vertex
uniquely corresponds to a 2-substring" and one charge pays for both occurrences; ledger
`5n+6 = n+|φ|+6`. At `σ = 2` there are **four** 2-substrings and two symbols: unexpressible, not merely
costly.

---

## 3. What a binary attractor reduction would look like — and the unsolved step

**Architecture (MY-CONJECTURE, modelled on Ch26).** Stage 1: a reduction over a moderate alphabet with
an **exact ledger** `γ(T_G) = f(u,t,k) + h(G)` — this exists (KP18 §4, lifted to `k = n`). Stage 2: an
**alphabet-reduction lemma for `γ`**: `γ_Σ(W) ≤ γ_2(C(W)) ≤ γ_Σ(W) + D`. Stage 3: amplification.

**Steps the neighbours do not supply.**

1. **No projection theorem for `γ`.** Ch26's `|H↓| ≤ |H| − Σ|α_A|` works because a grammar's local
   nonterminals can be **deleted**. An attractor has no deletion move: every distinct factor of `C(W)`,
   codeword-internal ones included, must still be covered, and shared codeword structure makes them
   cheap. There is no `γ`-analogue of the move.
2. **`γ` does not even order-transform.** COMPUTATIONALLY-CHECKED (this lane): code
   `0↦0011, 1↦0101, 2↦1010, 3↦1100` (`q=4`, `m=4`), **all** 1364 words over 4 letters of length 1..5:
   `γ_4('aaca') = 2` with `γ_2(C('aaca')) = 4`, while `γ_4('abcd') = 4` with `γ_2(C('abcd')) = 3`. The
   source objective falls while the encoded one rises, so no monotone function of `γ_2(C(·))` carries
   `γ_Σ(·)`. `γ_2 < γ_Σ` on 72/1364 instances (`γ_2 − γ_Σ ∈ {−1,0,1,2}`), so even the lower half of the
   lemma fails — `hardness-attractor.md` §4(1) measured.
3. **"Take `K` copies" does not amplify `γ`.** Ch26's Stage 3 needs the source term to grow like `K`,
   but at `σ = 2` there is no delimiter, so `K` copies means `T^K`. COMPUTATIONALLY-CHECKED: `γ(T^K) = γ(T)`
   for `K = 1..5` on five words with `γ = 2, 3`, and for `K = 1..3` on four length-12 words. With `K`
   **distinct** delimiters `γ` grows 1 per copy — `aabbaab`: `2 → 4, 5, 6` for `K = 2,3,4` — growth is
   the forced delimiter (one new symbol per copy), not `γ(T)` per copy; it is also sub-additive.
4. **The sharing primitive differs in kind.** An SLP shares a *rule* with unbounded fan-out; an
   attractor shares a *position*, whose cover set is the geometric family of factors crossing it. The
   nest-or-cross dichotomy of `sigma2-gadget.md` §8 is exactly this mismatch, and no neighbour reduction
   meets it. **MY-CONJECTURE**, then: the source objective must ride on a property of `γ` that is not its
   value — a forced-coverage statement ("every attractor of size ≤ `B` marks one of these `c`
   positions"), a `Π`-type constraint a codeword-internal factor does not satisfy for free. UNVERIFIED:
   nothing here shows such a gadget exists.

---

## 4. Does `γ ≤ g` or `γ ≤ z` transfer hardness? No — direction matters

* PROVED (KP18 Thm 3.5, Lemma 3.7, per `attractor-approx.md`; `γ ≤ b ≤ z ≤ g`): optima of the **same
  string**, so no map between instances. Even Ch26's theorem gives only
  `γ_2(C(W)) ≤ g_2(C(W)) ≤ g_Σ(W) + D` — an **upper** bound on `γ`.
* **Wrong direction.** Hardness of an upper-bounding quantity says nothing about the bounded one: `g`
  NP-hard at `σ = 2` is consistent with `γ` linear-time at `σ = 2` (`γ` is a hitting set over ≤ `2n−1`
  classes); binary hardness of `γ` says nothing about `g` or `z`. `hardness-related-binary.md` §7
  concurs.
* **What they are good for:** `z` is linear-time computable (N21 §3.2.1), so `γ(T) ≤ z(T)` is a **free
  upper bound** — run it before any exact-`γ` computation; `sigma2-gadget.md` §6.2 (`γ` correlates 0.943
  with `δ(T)`, not `τ`) is that fact measured.

---

## 5. Scope

1. No hardness claimed or refuted; `σ = 2`, `k = n` stays OPEN. Every neighbour's hardness is a
   *unary-label* phenomenon (vertices, edges, elements, clauses each get a symbol); the only binary
   technique on record is UNVERIFIED and rests on steps that fail for `γ` (§3).
2. **Cheapest next check:** re-run §3.2 with Ch26's `(SI)`-satisfying code (`m = 128`) on a few source
   words of length ≤ 4 — 512-bit texts fit the certified solver.
3. **Reproduce** (`cd /tmp/s2t/exp`; `enc.py`, `amp.py`, `amp2.py`; solver `tools/attractor/anytime.
   exact_gamma`, `Instance.verify` asserted, deadline 30–60 s, incomplete runs raise): `timeout 900
   python3 enc.py 5` → 1364 instances, 0 incomplete, 3 inversions; `timeout 600 python3 amp.py` → both
   tables.
4. Ch26 leans on C21's `g(w_G) = 299N + 3M + 5 + τ(G)`; **UNVERIFIED** — C21's full text was not
   fetchable, and C16 states only "`|G| = f(m,n) + |Γ|`".
