# probes — integrator-side measurements kept for reproducibility

`gap_exhaustive.py` (run from `tools/sigma2-alg/`, which it imports):
for every binary string up to a chosen `n`, compute `γ − ⌈δ⌉` from a **closed** certified
bracket only (`lb == g`), using `features.gamma_certified`.  Exhaustive results:

| n | 2–5 | 6–11 | 12–15 | 16 | 17 | 18 |
| --- | --- | --- | --- | --- | --- | --- |
| max `γ − ⌈δ⌉` | 0 | 1 | 2 | 2 | 2 | **2** |

with all `2^19 − 1` strings up to `n = 18` checked and every bracket closed (262 144 of
262 144 at `n = 18`, 130 s).  First witnesses: gap 1 at `n = 6` (`aababb`: `γ = 3`, `δ = 2`),
gap 2 at `n = 12` (`aaabaabababb`: `γ = 4`, `δ = 2`) — i.e. the *first n at which gap k
appears* is 6, 12, … (doubling), while the padding family `a^m + baabababb` **saturates** at
gap 2 for `m` up to 45: `γ = 4`, `δ = 2` regardless of `m`.  So padding is not the axis that
grows; `δ = 2` for every binary string, so the question reduces to *how large can `γ` be*.

Also measured (same method): `max(γ − γ₂)` = 0 (n ≤ 6), 1 (n = 7..11), 2 (n = 12), i.e. the
2-attractor is within 2 of `γ` on every binary string up to `n = 18`.
