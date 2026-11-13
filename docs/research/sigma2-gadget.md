# σ = 2, full attractor: three candidate binary gadgets, all refuted

**Lane.** `tools/sigma2/`. **Question attacked (OPEN).** Is the minimum string
attractor (`k = n`) at alphabet `σ = 2` NP-hard? `docs/research/hardness-attractor.md`
§3/§4 and `docs/research/hardness-related-binary.md` §6–7 record: every published
hardness reduction (KP18 = Kempa–Prezza STOC 2018; KPRR18 = ESA 2018; FW24 = STACS
2024) uses an alphabet that grows with `n` (`σ = Θ(uk+t)`, `σ = Θ(n)`), no source
gives a polynomial algorithm for `σ = 2`, `k = n`, and at fixed `k` with `σ = 2` the
exact problem is linear-time solvable. So the problem is open in both directions.

**Labels used below.** PROVED = proof written out here (short). COMPUTATIONALLY-
CHECKED = exact `γ` computed by a certified solver over an explicitly enumerated
instance set, with the instance list and commands given. MY-CONJECTURE = my guess,
no proof. UNVERIFIED = not checked. Literature statements are quoted from the
repo's research notes, not re-read in the primary sources here.

---

## 0. Verdict

I built three explicitly stated polynomial reductions from VERTEX COVER to
"binary word of length `O((n+m) log n)`, decision question `γ(T_G) ≤ B`", and tested
the equivalence exhaustively with exact `γ`. **All three are refuted, and they are
refuted for *every* threshold function `B`, not just for the ledger's `B = m + q`**
(§6.2): there are instance pairs `G1, G2` with `τ(G1) < τ(G2)` but `γ(T_G1) > γ(T_G2)`,
which no monotone threshold can separate.

Two things survive as usable results:

* **PROVED (necessary condition, cheap to test).** Any candidate of the threshold
  form must have `γ(T_G)` depend on the *isomorphism class* of `G` only (up to the
  bands of `B`). All three of my constructions violate that. This is a five-line
  filter that kills a binary gadget candidate before any proof is attempted, and
  it is not in the repo's research notes.
* **PROVED (the nest-or-cross dichotomy, §8).** For "payment-site" designs (one
  charge pays for a vertex by covering all of its incident obligations at one
  position), either the site forces a charge (payment unconditional) or the
  payment is available at a position a block needs anyway (payment free). Neither
  leaves the trade-off that a vertex-cover ledger needs. This is the concrete form
  of the two obstacles named in `hardness-attractor.md` §4 ("unique labels must
  become unique factors", "the ±1 coverage ledger").

**No NP-hardness is claimed, and nothing here refutes hardness either.** The
obstructions in §8 are about *hub-style* ledgers; a gadget built on a different
mechanism is not excluded (§9).

---

## 1. Target definition, and why `k = n`

`γ(T)` = the minimum size of a set `Γ` of positions of `T` such that every distinct
factor of `T` has an occurrence `[i, i+ℓ)` with `i ≤ p < i+ℓ` for some `p ∈ Γ`
(full attractor, `k = n`). All instances below are over `{0,1}` and all questions
are about `k = n`.

**Role of `k` (PROVED from the literature as recorded in this repo).** At `σ = 2`
and *fixed* `k`, exact `γ_k` is computable in `O(n)` — KPRR18 Thm 29 gives
`O(n) + exp(O(σ^k log σ^k))`, which is `O(n)` at `σ = 2`, constant `k`
(`docs/research/hardness-attractor.md` §3). Hence **no binary hardness can live at
fixed `k`**; any reduction must target *growing* `k`, and `k = n` is the natural
extreme. This report therefore never uses a `k`-attractor: hardness at `k = 3`
would not transfer. (ATTRIBUTED: I did not re-read KPRR18; the statement is taken
from the repo's quoted Thm 29.)

## 2. The source problem, and why vertex cover

VERTEX COVER (decision form): given `G = (V, E)` and `q`, is there `S ⊆ V` with
`|S| ≤ q` meeting every edge? `τ(G)` = the minimum `|S|`.

Why this source (MY-JUDGEMENT, stated because the mission asks):

1. KP18's own reductions (Thm 4.2 from `k`-SET COVER, Thm 4.3 from bounded-degree
   VERTEX COVER) already target this structure, so the gadget architecture to
   imitate is the one that is known to work — with a large alphabet.
2. VERTEX COVER is the smallest source that can be enumerated *completely*: all
   graphs on `n` vertices, `2^{C(n,2)}` of them. "≤ 4 variables, ≤ 6 clauses" of
   3-SAT is `Σ_{k≤6} C(56,k) ≈ 3.6·10^7` instances with texts far too long for
   exact `γ`; the vertices are the wrong currency for a lane whose acceptance
   criterion is an exhaustive check (§9).
3. The ledger below (`m + τ`) is arithmetically exact for vertex cover (Lemma 4.1),
   so a working gadget would give the *identity* `γ(T_G) = m + τ(G)`, the sharpest
   possible form of a reduction — which makes a refutation correspondingly strong.

## 3. The three reductions, stated as algorithms

Let `n = |V|`, `m = |E|`, `L = ⌈log₂ n⌉` (so `2^L ≥ n`), and for `v ∈ V`
let `tag(v) = "1" ‖ bin_L(v)` — the `(L+1)`-bit label of `v`. Let `sep = "00"`.
Write `edges(G)` in the canonical order `(min(u,v), max(u,v))` sorted lexicographically.

* **tags** `T_G = tag(0) tag(1) … tag(n−1) ‖ Π_{e=(u,v) ∈ edges(G)} tag(u) tag(v)`
* **tags_sep** `T_G = Π_v (tag(v) sep) ‖ Π_{e=(u,v)} (tag(u) sep tag(v) sep)`
* **hubs** `T_G = Π_v (tag(v) tag(v) tag(v) sep) ‖ Π_{e=(u,v)} (tag(u) sep tag(v) sep)`

**Size bound (PROVED, and asserted by `check.py` on every instance).**

| variant | `|T_G|` |
|---|---|
| tags | `(L+1)(n + 2m)` |
| tags_sep | `(L+3)n + (2L+6)m` |
| hubs | `(3L+5)n + (2L+6)m` |

All are `O((n+m) log n)` since `L = ⌈log₂ n⌉`; the mapping is a polynomial-time
reduction in the sense required.

**Design intent ("the ledger").** Each edge owns a contiguous *block* (`tag(u)
tag(v)`), each vertex owns a *cell* (its tag, and in `hubs` a three-copy hub). The
intent is: the block contains a factor occurring nowhere else, so it forces ≥ 1
charge; the class of `tag(u)` reoccurs outside the block, so it can be covered from
`u`'s cell instead — "paying for `u`". Unpaid vertices then cost one extra charge
per incident block. §4 shows that this accounting would give `m + τ` exactly.

## 4. The ledger arithmetic (PROVED)

**Lemma 4.1.** For every graph `G` with `m ≥ 0`,
`m + min_{H ⊆ V} (|H| + #{e ∈ E : e ∩ H = ∅}) = m + τ(G)`.

*Proof.* Let `H` attain the minimum and let `U = {e : e ∩ H = ∅}`; adding one
endpoint of each edge of `U` to `H` gives a vertex cover of size `≤ |H| + |U|`, so
`τ ≤ |H| + |U|`. Conversely `H` = a minimum vertex cover gives `|H| + 0 = τ`. ∎

So *if* a construction realised the ledger — one mandatory charge per block, one
charge per paid vertex covering all of that vertex's incident block-sides, one
extra charge per unhit block, and nothing else — then `γ(T_G) = m + τ(G)`.

The identity is also machine-checked, exhaustively, on all `1099` graphs with
`n ≤ 5` (`python3 check.py --variant tags --nmax 1 --ledger-check 5`, output
`{"instances": 1099, "violations": []}`): the arithmetic is not where the plan
fails.

## 5. How the check certifies `γ`

`tools/sigma2/check.py` computes `γ` twice, independently, and never silently:

* **fast solver** — the suffix-tree node universe of `../attractor/instance.py`
  (rule R1: an attractor is a hitting set of the *shortest* factor of every node,
  `≤ 2n−1` elements) with iterative deepening, greedy upper bound and exhaustive
  search below it;
* **definition solver** — the universe is *every* distinct factor, no suffix-tree
  reasoning at all; run on every text with `|T| ≤ 40` and required to agree;
* every returned attractor is re-verified against the definition
  (`is_attractor`), and a disagreement raises instead of being reported;
* hitting a node/time cap raises `SearchIncomplete`, which `check.py` counts
  separately — **an incomplete check is never counted as a pass**;
* the source optimum `τ(G)` is brute force over all `2^n` vertex subsets.

## 6. Results

### 6.1 What was enumerated

| variant | instance set | instances checked | longest text | incomplete | seconds |
|---|---|---|---|---|---|
| tags | **all** graphs, `n ≤ 4` | 75 | 48 | 0 | 3.5–3.9 |
| tags_sep | **all** graphs, `n ≤ 4` | 75 | 80 | 0 | 48–51 |
| hubs | all graphs `n ≤ 3` (11) + all `n = 4, m ≤ 2` (11 of 22) | 22 | 64 | 11 | ~480 |

(COMPUTATIONALLY-CHECKED. `hubs` was capped: `hub(v) = tag(v)^3` makes `|T_G| = 104`
for `K₄`, beyond exact `γ` in this lane. The hubs column is the union of two runs,
`--nmax 3` (11 instances) and `--nmax 4 --mmax 2` (11 of the 22 `n = 4, m ≤ 2`
instances decided); the other 11 are the length-64 texts the solver could not close
inside 10 s / 2·10⁶ nodes. They are counted as *incomplete*, never as passes.)

`τ` and `γ` both vary over the enumerated sets — the equivalence is not being
tested on a constant:

| variant | `τ` distribution | `γ` distribution | `γ = m+τ` | `γ < m+τ` | `γ > m+τ` |
|---|---|---|---|---|---|
| tags | `{0:4, 1:29, 2:41, 3:1}` | `{2:3, 3:16, 4:23, 5:25, 6:7, 7:1}` | 19 | 31 | 25 |
| tags_sep | `{0:4, 1:29, 2:41, 3:1}` | `{2:2, 3:4, 4:10, 5:30, 6:20, 7:8, 8:1}` | 32 | 2 | 41 |
| hubs | `{0:4, 1:17, 2:1}` | `{2:1, 3:1, 4:1, 5:1, 6:3, 7:7, 8:7, 9:1}` | 0 | 0 | 22 |

So the ledger `γ(T_G) = m + τ(G)` (CLAIM, §3) fails on 56/75, 43/75 and 22/22
instances respectively. Excess histogram for `tags`: `{−2:1, −1:30, 0:19, 1:19,
2:4, 3:2}`; for `tags_sep`: `{−1:2, 0:32, 1:17, 2:17, 3:6, 4:1}`; for `hubs`:
`{2:2, 3:2, 4:6, 5:8, 6:2, 7:2}` (never within 2). **Both directions
break**: there are instances where `γ` is *below* the ledger (the gadget gives away
coverage it should not — a cheating attractor) and instances where it is above
(the designed attractor does not cover the text, i.e. accidental obligations).

The two directions separately, as the mission asks for them:

* **upper direction** (`τ(G) ≤ q ⟹ γ(T_G) ≤ m + q`, tested at `q = τ(G)`): fails on
  **25/75** (`tags`), **41/75** (`tags_sep`) and **22/22** (`hubs`) instances — there
  the attractor the ledger prescribes already needs more than `m + τ` charges, and
  in fact the ledger's explicit charge pattern
  (`reduce.designed_charge_pattern`) is **not an attractor at all** on 60/75 and
  74/75 of those instances (column `easy_dir_violations`), because the text has
  classes outside every block and cell that the pattern covers;
* **lower direction** (`γ(T_G) ≤ m + q ⟹ τ(G) ≤ q`, tested at `q = τ(G) − 1`): fails
  on **31/75** and **2/75** — witness attractors are in §6.2 and §6.4.

### 6.2 The refutation that does not depend on the choice of `B`

CLAIM as stated uses `B(q) = m + q`. A weaker, `B`-free claim is

> **CLAIM′.** There is a function `B` (of `q` and of the instance's `n`, `m`) with
> `γ(T_G) ≤ B(q) ⟺ τ(G) ≤ q` for every graph `G`.

CLAIM ⟹ CLAIM′. CLAIM′ is refuted by a single *inversion pair*: `τ(G₁) < τ(G₂)` yet
`γ(T_{G₁}) > γ(T_{G₂})`, because `B` must satisfy
`γ(T_{G₂}) ≤ B(τ(G₂)−1) < γ(T_{G₁})` — impossible. (COMPUTATIONALLY-CHECKED,
`τ(G)` and `γ(T_G)` both exact; texts verified by two solvers.)

| variant | `G₁` (low `τ`, high `γ`) | `γ(T_{G₁})` | `G₂` (high `τ`, low `γ`) | `γ(T_{G₂})` |
|---|---|---|---|---|
| tags | `{(0,2),(0,3)}`, `n=4`, `τ=1`, `m=2`, `|T|=24` | **5** | `{(0,1),(2,3)}`, `n=4`, `τ=2`, `m=2`, `|T|=24` | **3** |
| tags_sep | `{(0,1),(1,2),(1,3)}`, `n=4`, `τ=1`, `m=3`, `|T|=50` | **6** | `{(0,1),(0,2),(1,2)}`, `n=3`, `τ=2`, `m=3`, `|T|=45` | **4** |
| hubs | `{(1,3)}`, `n=4`, `τ=1`, `m=1`, `|T|=54` | **9** | `{(0,1),(0,2),(1,2)}`, `n=3`, `τ=2`, `m=3`, `|T|=63` | **8** |

The `tags` pair is the cleanest: **two graphs with the same `n` and the same `m`,
the `τ=2` one gets a strictly smaller `γ` than the `τ=1` one.**
`G₁ = P₃ ⊕ K₁`, `T = 100101110111|100110|100111`, `γ = 5`, attractor
`{4,6,11,15,19}`; `G₂ = 2K₂`, `T = 100101110111|100101|110111`, `γ = 3`,
attractor `{2,8,12}`. The reason is visible in the texts: `G₂`'s two blocks are
exactly the two halves of the tag region (`100101` = `tag(0)tag(1)`, `110111` =
`tag(2)tag(3)`), so `T = (100101110111)²` — a square — and `γ` collapses to 3;
`G₁`'s blocks (`100110`, `100111`) are near-copies of each other but not of the
region. **`γ` is measuring
how repetitious the label sequence is, not how hard the graph is to cover.**
Supporting measurement (COMPUTATIONALLY-CHECKED, all 75 `tags`/`tags_sep` instances
at `n ≤ 4`, reproduce with `python3 check.py --variant tags --nmax 4 --correlate`):
Pearson correlation of `γ` with `δ(T)` (`δ = max_ℓ d_ℓ/ℓ`, computed by
`../repmeter/measure.py`) is **0.943** (tags) / **0.909** (tags_sep), with `|T|`
0.911 / 0.896, with `m` 0.905 / 0.855, and with `τ` only **0.742** / **0.743**.

### 6.3 Isomorphism invariance — the general necessary condition

**Lemma 6.4 (PROVED).** Suppose a construction `G ↦ T_G` and a threshold function
`B` satisfy CLAIM′. Let `G, H` be isomorphic graphs. Then for every `q`,
`γ(T_G) ≤ B(q) ⟺ γ(T_H) ≤ B(q)`. In particular, if `B` is injective on the
relevant range (e.g. `B(q) = m + q`, the ledger's threshold), then
`γ(T_G) = γ(T_H)`.

*Proof.* `τ(G) = τ(H)`, so the right-hand sides agree for every `q`; hence the
left-hand sides agree for every `q`. If `γ(T_G) < γ(T_H)` and `B` is injective,
choose `q` with `γ(T_G) ≤ B(q) < γ(T_H)`, contradiction. ∎

**The three constructions violate it** (COMPUTATIONALLY-CHECKED, exact `γ`, texts
`≤ 48` chars, all solvers cross-checked; reproduce with
`python3 check.py --variant tags --nmax 4 --labels --relabels 0`).
`tags`, all 24 relabellings of each isomorphism class on 4 vertices (and all 6 of
each class on 3 vertices, where the empty graph gives `{2:2, 3:4}` and `P₃` gives
`{3:3, 4:3}`; 12 of the 15 classes vary in total):

| class | `τ` | `γ` over the 24 labelings |
|---|---|---|
| empty | 0 | `{2: 3, 3: 21}` |
| `K₂` | 1 | `{3: 24}` |
| `P₃` | 1 | `{3: 3, 4: 21}` |
| `K_{1,3}` | 1 | `{4: 9, 5: 15}` |
| `K₃` | 2 | `{4: 17, 5: 7}` |
| `2K₂` | 2 | `{3: 1, 4: 23}` |
| `P₄` | 2 | `{4: 17, 5: 7}` |
| `K₃+e` | 2 | `{4: 2, 5: 20, 6: 2}` |
| `C₄` | 2 | `{5: 8, 6: 16}` |
| `K₄−e` | 2 | `{5: 2, 6: 22}` |
| `K₄` | 3 | `{6: 5, 7: 19}` |

Ten of the eleven classes take at least two values. `tags_sep` (6 relabellings per
class) varies on 6 of 15 classes, e.g. empty `{3:4, 4:2}` at `n=3`, `K_{1,3}`
`{5:4, 6:2}`, `C₄` `{6:3, 7:3}` at `n=4`.

This is the first thing any future binary gadget should be tested for: it costs a
handful of exact `γ` computations and it kills a candidate outright.

### 6.4 Where exactly the ledger breaks (smallest witness)

Instance: `G = K₃`, `tags`, `n = 3`, `m = 3`, `τ = 2`, `m + τ = 5`, `γ = 4`.
`T = 100101110 100101 100110 101110` (27 chars), optimal `Γ = {5, 11, 16, 21}`
(verified an attractor from the definition). Cell by cell
(`python3 check.py --variant tags --witness 3 0-1,0-2,1-2`):

```
tag(0)        [0,3)    charges: []          block(0,1)  [9,15)  charges: [11]
tag(1)        [3,6)    charges: [5]         block(0,2)  [15,21) charges: [16]
tag(2)        [6,9)    charges: []          block(1,2)  [21,27) charges: [21]
```

Every block has exactly **one** charge, and `tag(2)` — vertex 2's payment cell — has
**none**, so the ledger's price is 5 and the truth is 4. Three facts produce the
discount, all of them binary-alphabet artefacts:

1. The class `100` (= `tag(0)`) occurs at `0` (tag region), `9` (block `(0,1)`) and
   `15` (block `(0,2)`), so **one** payment serves two blocks — that is the ledger's
   intent, but here it is served by a block's *mandatory* charge (`p = 11`), not by
   a dedicated payment.
2. The class `110` (= `tag(2)`) occurs at starts `6, 14, 18, 24`. The occurrence
   `[14, 17)` **straddles the junction between block `(0,1)` and block `(0,2)`**
   (the junction is at 15), and the charge `p = 16` — which the ledger counts as
   block `(0,2)`'s charge *in vertex 0's spot* — lies inside it. So vertex 2's
   obligation is discharged from a position that belongs to another vertex's spot:
   the ledger's "an unhit block costs an extra charge" premise is false.
3. 17 classes have occurrences in ≥ 2 different block cells (`n_fusion_classes` in
   the breakdown), among them `101` (5 occurrences, 4 cells) and `110`
   (4 occurrences, 3 blocks): short binary words cannot be kept local, because
   labels must be reused.

This is the precise failure: **the objects the ledger needs to be per-block are
per-block only if each occurrence of a label is a fresh symbol** — exactly KP18's
Eq. (4) and FW24's "it is vital that each vertex has a unique label". In `{0,1}`
the label of a vertex is a word that re-appears at every junction of two blocks
that happen to end and start with compatible bits.

### 6.5 Why `hubs` is worse, not better

`hubs` never came within 2 of the ledger (excess `+2 … +7`, all 22 decided
instances): `hub(v) = tag(v)^3` adds a region whose own factors (those spanning two
or three copies of `tag(v)`, and the region's own long factors) are *unique to the
hub*, so they force charges inside the hub — the hub is never inert. Making it inert
requires its content to be replicated, which (§8, Lemma 8.2) hands the payment to a
position outside the site. Corollary 8.3 states the dichotomy.

## 7. Why this was expected: what the ledger demands in `{0,1}`

Read as a specification, CLAIM needs a text in which, for each vertex `u`:

* (P1) the classes of `u`'s incident block-sides are *distinct classes* (`A_e^u`,
  `e ∋ u`) — otherwise one charge covers all of them for free and payment is
  automatic;
* (P2) those distinct classes all have an occurrence containing one common
  position `p_u` — otherwise no single charge pays for `u`;
* (P3) the `A_e^u` have *no other* occurrences except inside their own block's
  u-spot — otherwise some unrelated charge pays for `u` (§6.4 fact 2);
* (P4) every class occurring at the payment site `p_u` occurs somewhere else as
  well — otherwise a charge inside `u`'s cell is forced and payment is automatic
  (§6.5);
* (P5) the block of `e` contains a class occurring nowhere else, so the block's
  mandatory charge is real.

(P2) forces the `A_e^u` to be the nested-or-crossing factor family at `p_u` (two
intervals sharing `p_u` either nest or cross). §8 proves that this specification is
*unsatisfiable*: nesting violates (P3) outright, crossing plus (P4) hands the payment
to a position outside the site (§8, Lemma 8.2 and Corollary 8.3). So the tension
below is not a failure of imagination: for payment-site designs it is a dichotomy.

## 8. Why a hub-style ledger cannot work: the nest-or-cross dichotomy (PROVED)

Setting. A *payment-site design* gives, for each vertex `u`:

* a site region `S_u = [a_u, b_u)` and a position `p_u ∈ S_u`;
* for each incident edge `e`, a class `A_e^u` with
  (a) an occurrence `I_e = [α_e, β_e) ⊆ S_u` with `α_e ≤ p_u < β_e` — this is what
      would make one charge at `p_u` cover *all* of `u`'s obligations at once, i.e.
      what makes a single payment possible at all;
  (b) an occurrence inside block `e`'s u-spot;
  (c) no other occurrences;
* and blocks are *insulated*: (d) every occurrence of every factor lies entirely
  inside one block or one site cell (blocks and site cells tile `T`; nothing
  straddles a junction).

`tags` and `tags_sep` satisfy (a), (b), (d) by construction and violate (c);
`hubs` satisfies (c) for the per-edge classes and violates the inertness premise
below. Hypotheses (a)–(d) are exactly "the naive hub": one payment site per vertex,
per-incidence classes, insulated blocks.

**Lemma 8.1 (nest-or-cross).** Under (a)–(d), if `deg(u) ≥ 2` then for any two
incident edges `e ≠ e'` the site spans `I_e`, `I_{e'}` cross: neither contains the
other.
*Proof.* If `I_e ⊆ I_{e'}`, then `T[I_e]` is a factor of `T[I_{e'}]`, so `A_e^u` has
an occurrence inside the u-spot of block `e'` (at the corresponding offset of the
copy of `A_{e'}^u`). That occurrence is neither the one in `S_u` nor the one in
block `e`, contradicting (c). Symmetrically for `I_{e'} ⊆ I_e`. ∎

**Lemma 8.2 (payments are never optional).** Under (a)–(d), `deg(u) ≥ 2`, and the
site hypothesis

> (S) every class having an occurrence inside `S_u` has another occurrence outside
>     `S_u`  ("the site is inert, so no charge is forced inside it")

the class `F_u := T[min_e α_e .. max_e β_e)` — the union factor, which contains
`p_u` because every `I_e` does — has an occurrence outside `S_u`, and at any such
occurrence the position at the offset of `p_u` covers every `A_e^u`.
*Proof.* `F_u` is a factor containing `p_u`, hence (S) gives it an occurrence
outside `S_u`. Because `T[min α .. max β) = F_u` contains `T[α_e .. β_e] = A_e^u` as
a factor at that offset for every `e`, the position of `F_u`'s occurrence at offset
`p_u − min α` lies inside that occurrence of every `A_e^u`, so it covers all of
them. ∎

By (d) such an occurrence lies either inside a block (where a charge is needed
anyway, so the payment is free) or inside another vertex's site cell. In the second
case the argument repeats for that site, and the chase terminates because there are
finitely many cells and it never returns to `S_u` (`F_u` was not confined to
`S_u`) — so it ends at a block, or at a site where (S) fails.

**Corollary 8.3 (the dichotomy that kills the ledger).** In a payment-site design
satisfying (a)–(d), for every vertex `u` of degree `≥ 2` exactly one of the
following holds, and neither is the ledger:

* **(S) fails** — some class is confined to `S_u`, so *every* attractor has a charge
  inside `S_u`: the payment is unconditional (`u ∈ H` always), so Lemma 4.1's
  minimisation over `H` is not exercised and nothing in the ledger tracks `τ`
  through this vertex;
* **(S) holds** — by Lemma 8.2 a position outside `S_u` already covers every
  `A_e^u`, and the chase of Lemma 8.2 ends at a block charge or at a site where
  (S) fails; in the first case the payment is a side effect of a charge the block
  needs anyway, so the payment adds nothing to the count and again `τ` is not
  tracked.

There is no third case: `(S)` is a yes/no question about the site, and both answers
remove the trade-off "spend 1 charge to save `deg(u)` block charges" that Lemma 4.1
needs. ∎

The measured data match the two horns exactly. `tags`/`tags_sep` violate (c) (label
classes acquire occurrences at block junctions, §6.4), which is the mechanism of the
31 and 2 instances with `γ < m + τ`: a charge serves two blocks. `hubs` keeps (c)
for its per-edge classes, but its site `tag(v)^3` carries classes confined to the
site (the factors spanning two or three copies), so (S) fails: the site forces
charges — measured as `γ = m + τ + {2..7}` on all 22 decided instances. The 25
instances of `tags` with `γ > m + τ` are the symmetric horn: accidental obligations
(a label class occurring in a block *and* elsewhere forces two charges).

**Relation to the repo's notes.** This is the binary form of the two obstacles named
in `hardness-attractor.md` §4: "unique labels must become unique factors" (here:
(c) fails because a label is a word, and its occurrences are wherever the word
occurs) and "the ±1 coverage ledger" (here: Corollary 8.3, the payment is either
forced or free). It also explains why KP18's construction cannot be transliterated
(MY-INFERENCE from the alphabet display quoted in `hardness-attractor.md` §2): there
the per-incidence objects are single *symbols* `$_{i,j}`, `x_t^{(j)}`, one per
occurrence, so (c) holds by construction and (S) can be made to fail only at the
designated payment position.

## 9. What remains unproved (explicit scope)

1. **No NP-hardness and no algorithmic result is claimed.** The `σ = 2, k = n`
   question stays open. Three specific constructions are refuted; that is all.
2. **§8 is not a general impossibility theorem.** It excludes *payment-site
   (hub) designs* satisfying (a)–(d) — one charge per vertex, per-incidence classes,
   insulated blocks. A gadget with a different saving mechanism is not excluded —
   e.g. the "anchor bit + self-synchronising code" programme of Chen
   (arXiv:2610.32298, unreviewed per `hardness-related-binary.md` §1), or a gadget
   whose saving is *inside* a block (as KP18's `2n_i+1` marks are) rather than at a
   site.
3. **Scope of the exhaustive check.** `tags`, `tags_sep`: *all* graphs with `n ≤ 4`
   (75 instances) — complete for that size, nothing sampled. `hubs`: all `n ≤ 3`
   (11) plus 11 of the 22 graphs with `n = 4, m ≤ 2`, with 11 instances left
   undecided by the solver (counted, not passed). Not checked: `n ≥ 5`, where
   `|T_G| > 60` and exact `γ` is out of reach of the certified solvers used here
   (`tools/attractor/anytime.py` is an anytime *search*, not a certificate, so it
   cannot decide equality).
4. **The 3-SAT form of the mission was not run.** `≤ 4` variables `≤ 6` clauses is
   `3.6·10^7` instances and the corresponding texts are far longer than 40 bits;
   the check would be a sample, not an exhaustive test. Vertex cover at `n ≤ 4` is
   exhaustive and the `τ`/`γ` distributions (§6.1) show the source optimum varies,
   which is what matters for the test to be meaningful.
5. **The labels used** (`tag(v) = "1" ∙ bin_L(v)`) are one choice out of `2^{L·n}`;
   the isomorphism-invariance data (§6.3) shows the *value* depends on the choice,
   so a refutation obtained with these labels is a refutation of these three
   constructions only, and conversely a positive result would have required a proof
   that no labelling helps. Lemma 6.4 is exactly that filter.

## 10. Reproduce

```
cd tools/sigma2
python3 check.py --variant tags     --nmax 4 --quiet                    # 75 graphs, ≈4 s
python3 check.py --variant tags_sep --nmax 4 --quiet                    # 75 graphs, ≈50 s
python3 check.py --variant hubs     --nmax 3 --time-cap 10 --node-cap 2000000
python3 check.py --variant hubs     --nmax 4 --mmax 2 --time-cap 10 --node-cap 2000000
python3 check.py --variant tags --labels --relabels 0 --nmax 4 --quiet  # §6.3, all 24 labelings
python3 check.py --variant tags --nmax 4 --correlate --quiet            # §6.2 correlations
python3 check.py --variant tags --nmax 1 --ledger-check 5 --quiet       # Lemma 4.1, all n<=5
python3 check.py --variant tags --witness 3 0-1,0-2,1-2                 # §6.4, ledger breakdown
```

Every run prints a JSON summary: instance count, `τ`/`γ`/excess histograms,
`incomplete` count, and the failure rows with their attractors. `check.py` raises
rather than reporting a disagreement between the two solvers.
