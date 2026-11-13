# `σ = 2` minimum attractor: claim register after three attacks

**Question (OPEN).** Is the minimum string attractor (`k = n`) NP-hard on `{a,b}`? Baseline:
`hardness-attractor.md` §3–4, `hardness-related-binary.md` §6–7. **Lanes:** `tools/sigma2/` →
`sigma2-gadget.md`; `tools/sigma2-alg/` → `sigma2-algorithm.md`; neighbour lane →
`sigma2-technique.md` (scripts in `/tmp/s2t/exp/`, not in the repo).

**Labels.** PROVED (proof given, or quoted with a locator); CHECKED (exact `γ` from a *closed*
bracket — upper bound verified at definition level, every smaller set refuted — scope stated);
MY-CONJECTURE; UNVERIFIED.

## 1. What is now established

**E1** (PROVED — KPRR18 Thm 29/Cor 7, KP18 Eq. 4, FW24, all quoted; `hardness-attractor.md` §2–3).
At `σ = 2`, fixed `k`: `γ_k` in `O(n)+exp(O(2^k k))` = `O(n)`, so no binary hardness below `k = n`.
Every published attractor reduction grows `σ` (KP18 `Θ(uk+t)`; FW24 `m+n+6`). *Scope:* all `n`.

**E2** (PROVED — Lemmas 1–3; CHECKED, `k ≤ 6`; `sigma2-algorithm.md` §3). `γ ≤ γ₂ + c` false for
every constant `c`; `γ/γ₂` unbounded. `γ₂ ≤ 6`, `γ ≥ δ ≥ 2^k/k` on de Bruijn `B_k`; `γ(B_6)=11`,
`γ₂(B_6)=2`. *Scope:* measured to `n = 69`, proof unbounded.

**E3** (CHECKED — exhaustive to `n = 13`, plus one certified witness at `n = 32`; ibid. §2, §4).
`max(γ−⌈δ⌉) = 2` over **all** `2^n` words, `n ≤ 13` (first at `n=12`: `aabababbabbb`, `γ=4`, `δ=2`),
0 incomplete; `γ−⌈δ⌉ = 3` at `n=32` (`bbbaaaabbabbaaabbaaaabbaabbaabaa`, `γ=6`, `δ=3`, `γ₂=2`), so
`γ ≤ ⌈δ⌉+2` is dead. *Scope:* all words `n ≤ 13`; one word `n=32`.

**E4** (CHECKED — exhaustive; recount confirmed by me; ibid. §6). `k* = min{k: γ_k = γ}` reaches 5 at
`n=12` (`aaaaabaaaabb`), 4 at `n=10` — `≈n/2`; `γ₃ < γ` on 264/2048 = 12.9 % of `n=12` words (the
lane's "54 %" does not reproduce; `γ₂ < γ` on 66.6 %). *Scope:* `n ≤ 12`.

**E5** (CHECKED — exhaustive; ibid. §5). `γ` is not a function of `δ`, the `d_k` profile, `γ₂`,
runs/period or packing: `aaabba` and `aababb` share profile `(2,4,4,3,2,1)`, `γ = 2` vs `3` —
arrangement decides, not counts. *Scope:* all words `n ≤ 10`.

**E6** (PROVED + CHECKED; `sigma2-gadget.md` §4). Lemma 4.1: `m + min_H(|H| + #{unhit edges}) =
m + τ`; machine-checked on 1099 graphs, 0 violations. *Scope:* graphs `n ≤ 5`.

**E7** (PROVED — Lemma 6.4; ibid. §6.3). If `γ(T_G) ≤ B(q) ⟺ τ(G) ≤ q` with `B(q)=m+q`, then
`G ≅ H ⟹ γ(T_G)=γ(T_H)`. *Scope:* any threshold-form reduction.

**E8** (PROVED — Lem 8.1–8.2, Cor 8.3; ibid. §8). Nest-or-cross: in a *payment-site* design with
`deg(u) ≥ 2`, either a class is confined to the site (payment forced) or a position outside it
already covers all of `u`'s incident classes (payment free) — never the ledger. *Scope:*
payment-site designs only.

## 2. What failed, and why

**F1** `tags`: VCOVER → `(L+1)(n+2m)`-bit word, ledger `γ = m+τ`. Fails on 56/75 graphs `n ≤ 4`;
smallest witness `K₃`: `T = 100101110100101100110101110`, `γ = 4 < 5`. Reason: class `110` occurs at
`6,14,18,24`, and `[14,17)` **straddles the junction at 15**, so block `(0,2)`'s mandatory charge `16`
pays vertex 2 free. Over `{0,1}` a "unique label" is a *word*, and short words recur at every
compatible junction.

**F2** `tags_sep`: 43/75 fail, 41 with `γ > m+τ` and 2 with `γ < m+τ`; the designed charge pattern is
no attractor at all on 74/75. Reason: same.

**F3** `hubs` (`tag(v)³` payment hub): 11/11 at `n ≤ 3` fail (excess `+2…+5`); 11/22 at `n=4` decided,
all fail (`+2…+7`), 11 incomplete. Reason: the hub is never inert — factors spanning copies of
`tag(v)` are confined to it (horn 1 of E8).

**F4** **Any** threshold `B(q,n,m)` for `tags`. Refuted by an inversion pair with the same
`n=4, m=2, |T|=24`: `P₃⊕K₁` (`τ=1`, `γ=5`) versus `2K₂` (`τ=2`, `γ=3`), both certified. Reason: `γ`
measures repetitiousness of `T_G`, not covering hardness of `G` (`T_{2K₂}` is a square); corr `γ–δ`
0.943 against `γ–τ` 0.742.

**F5** iso-invariance (E7), violated by `tags` at `n=3`: empty graph `γ ∈ {2,3}`, `K_{1,2}`
`γ ∈ {3,4}` over 6 labellings. Reason: label *values* matter and no construction is label-canonical.
Monotonicity `H ⊆ G ⟹ γ(T_H) ≤ γ(T_G)` holds at `n ≤ 4`, so that filter alone does not kill it.

**F6** binary-encoding lemma `γ_Σ(W) ≤ γ₂(C(W)) ≤ γ_Σ(W)+D` (`0↦0011,…,3↦1100`): `γ₄('aaca')=2` but
`γ₂(C)=4`; `γ₄('abcd')=4` but `γ₂(C)=3`; 3 inversions, `γ₂<γ_Σ` on 20/340 words. Reason: the source
objective falls while the encoded one rises — an attractor has **no deletion move**, unlike a
grammar's nonterminals.

**F7** `K`-copy amplification `γ(T^K) ≈ K·γ(T)`. `γ(T^K)=γ(T)` is **false**: `aabbab`, `γ=2`,
`γ(T^K)=3` for `K=2…6`; yet over all words `n ≤ 7`, `K ≤ 4`, `max(γ(T^K)−γ(T)) = 1`. Reason: no
delimiter at `σ=2`, so copies are `T^K`; distinct delimiters restore growth (2,4,5,6) but by one
fresh symbol per copy. **Correction to `sigma2-technique.md` §3.3**: its five-word sample missed the
increment; "no `K`-linear amplification" is measured, unproved.

**F8** algorithm via `γ = γ_k` for small `k`: dead, since `k* = 5` already at `n = 12` (E4) and the
needed `k` is `Θ(n)`; the `O(n)`-per-fixed-`k` route is not an algorithm.

**F9** `γ ≤ ⌈δ⌉ + c` as a value pin: `c=0` fails at `n=6`, `c=1` at `n=12`, `c=2` at `n=32`. The
hill-climb maxima `2,2,2,2,3,2,3` at `n=16…48` are **lower bounds only**.

## 3. The strongest true statement about `σ = 2` today

At `σ = 2` the problem is open in both directions, asymmetrically: every fixed `k` is linear-time
(E1), so no hardness exists below `k = n`; the only *proved* obstruction to a reduction is the
nest-or-cross dichotomy for payment-site designs (E8), and the only *proved* algorithmic negative is
`γ > γ₂ + c` for every `c` (E2) — the rest is measurement. No binary construction on record makes `γ`
separate `τ`, and the failure is not alphabet size: with `Θ(log n)`-bit tags the text is
`O((n+m)log n)` long, ledger arithmetic `m+τ` and monotonicity all check out. What breaks is that a
per-block obligation must be *mandatory* (a class occurring nowhere else in the block) and *payable*
from one position; over `{0,1}` a class is confined to a block only if its label is a fresh symbol —
otherwise it recurs at junctions (F1) — while restoring confinement by padding forces charges inside
the payment cell instead (F3). The missing step is a **block-internal** saving (KP18's shape:
`2n_i+1` positions forced in `S_i`, one more when the element is bought), the two local optima
differing by exactly one charge — by E8 the only surviving placement. Nor is there a "lift": fixed
`k` is polynomial at `σ = 2`, so the gadget must be `k = n` outright and its long factors — where
`k* ≈ n/2` puts the cost (E4) — are load-bearing. Closing it needs the §4-X3 variant to pass the
inversion test at `n ≤ 4`, then a proof; the algorithm side needs a proof of `γ ≤ ⌈δ⌉+3` (measured to
`n = 48`), a *value* statement, not an algorithm.

## 4. Next three experiments

**X1 — is `K`-copy amplification dead?** Certify `γ(T^K)`, `K=1…6`, for every complement
representative `T` with `n ≤ 10`; record `D(n) = max_K(γ(T^K) − γ(T))`:
```
cd tools/sigma2-alg && timeout 5400 python3 -c "import sys,itertools;sys.path.insert(0,'.');import features as F
for n in range(1,11):
 m=0
 for b in itertools.product('ab',repeat=n):
  if b[0]=='a':
   s=''.join(b);g0=F.gamma_certified(s)[0]
   m=max([m]+[F.gamma_certified(s*K)[0]-g0 for K in range(2,7)])
 print('n',n,'D',m,flush=True)"
```
*Decision:* `D(n) ≥ 2` for some `n ≤ 10` with 0 incomplete ⇒ `sigma2-technique.md` §3.3 is wrong and
copy-amplification revives; `D(n) = 1` through `n = 10` ⇒ record MY-CONJECTURE `γ(T^K) ≤ γ(T)+1` and
drop the route.

**X2 — does `γ − ⌈δ⌉` stay ≤ 3?** Single-flip hill climb, 5 restarts, seed 0:
```
cd tools/sigma2-alg && timeout 7200 python3 check.py hunt --ns 64,80 --rounds 5
```
*Decision:* a certified `γ−⌈δ⌉ ≥ 4` kills `γ ≤ ⌈δ⌉+3` and supports the `Θ(log n)` conjecture;
all restarts ≤ 3 at `n = 80` ⇒ attempt a proof of `γ ≤ ⌈δ⌉+3`.

**X3 — the surviving hardness mechanism: a block-internal ledger.** Add variant `blk` to
`tools/sigma2/reduce.py`: payment position *inside* the block (KP18 shape — a mark region charged
`2n_i+1` if the endpoint is unbought, `2n_i+2` otherwise), no per-vertex site.
```
cd tools/sigma2 && timeout 1800 python3 check.py --variant blk --nmax 4 --quiet   # then --nmax 5 --mmax 6
```
plus a pairwise inversion scan over `τ` on the same rows.
*Decision:* any inversion pair at `n ≤ 4` kills it (the cheap `B`-free test of F4); `γ = m+τ` on all
75 graphs `n ≤ 4` **and** no inversion ⇒ promote to `n = 5–6`, only then attempt a proof. E8 excludes
no other design, so this is the surviving slot.

## 5. Residual risks

* `sigma2-technique.md`'s computations are not in the repo; two lane claims are corrected here (E4
  percentage, F7). Its quotations were not re-read (UNVERIFIED as quotes).
* E3/E4 are exhaustive only to `n = 13` / `n = 12`; above that: samples and hill climbs (lower
  bounds), never proofs. For `hubs`, `n = 4` is 11/22 decided and `n ≥ 5` is out of reach of the
  certified solvers — "checked on all instances" never applies above `n = 4` there.
