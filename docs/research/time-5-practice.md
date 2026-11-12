# Time-5 — where the time actually goes: measured practice vs. the word-RAM story

Web sources only. Labels: **MEASURED** = the authors' own printed timing;
**CLAIMED-BY-AUTHOR** = abstract/intro sentence, not traceable to a table;
**MY-INFERENCE** = my arithmetic on quoted numbers; **UNVERIFIED** = no primary
source reached. µs values are not comparable across machines — read the ratios.

## 1. What the implementations report

| implementation | reported speedup / result | baseline | setting | citation |
|---|---|---|---|---|
| r-index (Prezza impl., BigBWT build) | 8.03 µs/pattern count, 0.149 µs/occ locate, 13.13 MiB — MEASURED; the base everyone beats | online-RLBWT r-index | DNA coll., n = 629,140,006, σ = 10, r = 1,288,876; 1000 patterns, m = 8; 1 core Xeon E5-1650V3 @3.5 GHz | Gagie–Navarro–Prezza, arXiv:1802.05906v6, Table 3 |
| Move-r | "2–35 (typically 15) times as fast as with any other r-index supporting locate queries while being 0.8–2.5 (typically 2) times as large"; §5.2: "factors between 3 and 35" vs r-index — CLAIMED-BY-AUTHOR | r-index, online-rlbwt, rcomp-glfig | 5 texts, 0.47–84.19 GB (sars2), 2× EPYC 7452 | Bertram–Fischer–Nalbach, SEA 2024, LIPIcs 301 |
| Move-r vs count-only block-RLBWT | "2–3 (typically 2) times as fast and 0.8–6 (typically 2) times as large" — CLAIMED-BY-AUTHOR | fastest block-rlbwt | same | same, §5.2 |
| Move-rb (bi-directional) | "1-4 orders of magnitude faster than br-index, 1.9-10x faster than b-move and up to 5.5x faster than … columba, which is 36-42x larger" — CLAIMED-BY-AUTHOR | br-index, b-move, columba | approximate matching | Fischer–Nalbach, arXiv:2609.30089 |
| MONI | "2-11 times less memory and … 2-32 times faster for index construction" — CLAIMED-BY-AUTHOR (construction, not query) | PuffAligner, Bowtie2, BWA-MEM, CHIC | MEM finding, repetitive collections | Rossi et al., J. Comput. Biol. 29(2), 2022 |
| MONI + augmented thresholds | "48.37% faster and 22.89% larger" (Aug-DAC vs PHONI) — MEASURED | one-pass MONI | 1000×chr19, 1 thread, Xeon Bronze 3204 | Martínez-Guardiola et al., arXiv:2211.07794, §5 |
| sr-index | "retains the performance of the r-index while using 1.5–4.0 times less space"; Chr19: 0.076 → 0.032 bps and "search time from 0.69 to 0.58 µs" — MEASURED | r-index, r-csa, hyb-index, LZ indexes | Chr19 ≈ 55 Gbp, 404–465 patterns | Cobas–Gagie–Navarro, arXiv:2409.14654, §5 |
| VLB | "up to 5.5 for count queries and 9.77 for locate"; "ri is 3.22–8.14 times slower" — MEASURED | ri, sri-va, fbb, mn, move | BAC/COVID/HUM/KERNEL, 50 000 patterns, EPYC 7713 | Díaz-Domínguez–Mäkinen, arXiv:2602.17201, §8 |
| Movi | "backward search up to 30 times faster … by minimizing the number of cache misses and using memory prefetching" — CLAIMED-BY-AUTHOR | r-index-based pangenome tools | nanopore classification | Zakeri et al., iScience 2024 |

**No r-index paper I found reports a like-for-like query win over a plain
FM-index/BWA on non-repetitive text.** Wins are structural (space: "less than one
thousandth the size of competing indexes", MONI) or against *other r-index
variants*. r-index-vs-FM-index query speed is unbenchmarked at scale.

## 2. What dominates

**Locate, not count, once `occ` passes a few dozen.** From Table 3 above
(MEASURED): crossover at occ ≈ 54 for DNA (8.03 µs/pattern ÷ 0.149 µs/occ) —
MY-INFERENCE. Read-mapping queries sit far above that.

**Φ is the locate inner loop, and a pointer chase.** "we need to evaluate a
function Φ for every occurrence, which turns out to be the main performance
bottleneck in practice" (Dinklage et al., arXiv:2507.17300, §1); "the Φ steps …
remain a bottleneck … each causing cache misses" (ibid., §5). Move-r's benchmark
is built around this: with occ ≈ m a query mixes "occ ≈ m Φ queries, 2m LF queries
and at most 2m rank-select queries on L′", while occ ≈ 10⁵·m "practically only
measure[s] Φ query performance" (SEA 2024, §5.2).

**Cache behaviour, not operation counts, is the accepted explanation.** VLB
instrumented `PAPI_L1_DCM` and finds its variants "incur fewer L1 data-cache
misses per query symbol than fbb, mn, ri, and sri-va … memory locality is a
primary driver" (arXiv:2602.17201, §8.4); Movi attributes its 30× to prefetching
and "latency hiding". The RLZ-compressed differential suffix
array beside the r-index buys "up to two orders of magnitude faster locate
queries (with many occurrences) at the cost of using 2–13 times as much memory"
(arXiv:2507.17300, §5) — same asymptotics, a different memory-hierarchy bet.

**σ-dependent tables.** Move-rb names as one br-index/b-move bottleneck the
"O(σ) character-predecessor/-successor queries on the run-length-encoded BWT per
extension" (arXiv:2609.30089). Cheap for DNA (σ ≈ 5), not for KERNEL (σ ≈ 200).

**The `log log` factors are numerically irrelevant.** r-index locate is
O(m log log_w(σ + n/r) + occ log log_w(n/r)) (arXiv:2409.14654, §3). At w = 64:
σ + n/r = 93 for chr19_50 gives log_w = 1.09, log log_w ≈ 0.12; n/r = 10⁵ gives
≈ 1.47. The factor stays in [0.1, 1.8] and cannot produce the observed 3–35×
(Move-r) or 9.77× (VLB) swings — MY-INFERENCE.

## 3. Construction: usually the real bill

* "With repetitive texts, index construction time and peak memory usage are
  dominated by the construction of the BWT" (Move-r, §5.1); Move-r itself builds
  "0.9–2 (typically 2) times as fast while requiring 1/3–1 (typically 1/2) times
  as much memory" as the closest locate-capable r-index.
* MEASURED, same machine as the query numbers: BigBWT builds the r-index for the
  629 MB DNA collection in **103.10 s using 534 MiB** working space
  (arXiv:1802.05906, Table 2). At 0.149 µs/occ that is amortised only after
  ≈ 7·10⁸ reported occurrences (MY-INFERENCE).
* BigBWT/PFP: a "131-megabyte run-length compressed FM-index (restricted to
  support only counting and not locating) for 1000 copies of human chromosome 19
  in 2 hours using 21 gigabytes of memory" (arXiv:1803.11245, abstract) — locate
  samples excluded.
* ropebwt3 (arXiv:2409.00613, Table 3): ~600 Gb input (100 human assemblies, both
  strands) in **20.5 h / 83.0 GB peak**; "Ropebwt3 took 21 hours … of which
  7.7 hours was spent on libsais"; human320 81.2 h; AllTheBacteria (7.3 Tb)
  25.6 d. grlBWT is faster (8.3 h) but needs "~2 terabytes of working disk space"
  — an I/O cost no word-RAM model sees.
* Terabase check: with 17.6·10⁹ runs, "An r-index is likely to take more than
  200GB, while an FM-index sampled at one position per 8,192bp takes 17.5GB"
  (arXiv:2409.00613, §3.3).

## 4. Where theory and practice part company

1. **Same asymptotics, 15× apart.** Move-r and the r-index both evaluate one
   constant-size Φ step per occurrence; measured ratio 3–35× (SEA 2024). Theory
   cannot distinguish them.
2. **The sr-index inverts its own bound.** Theory says subsampling multiplies
   per-occurrence time by s; in practice it keeps r-index speed at 1.5–4.0× less
   space, and the authors say "the theoretical analysis falls short in describing
   the practical advantages of the sr-index, because it performs much better on
   real texts than on synthetic ones" (arXiv:2409.14654, abstract).
3. **Tricks with no asymptotic story**: run blocking and block-size tuning
   (block-rlbwt, VLB's ≤ w runs per block), branch-light scanning, SIMD (VLB uses
   SSE4.2; Move-r uses ips4o), prefetching (Movi), layout effects, and hybrid
   halves — "move-r can also be constructed without locate support, which roughly
   halves its size" (SEA 2024, §5.2).
4. **What is not hidden**: r itself. Runtime and space track n/r exactly as
   theory says; the disagreement is all in per-run constants.

## 5. What a formalization could and could not say

* **Could**: the counting skeleton — φ/Φ step counts, one word-RAM step per run
  step, toehold/SA-sample invariants, size in r·(bits per run), the s·occ worst
  case, and correctness (every occurrence reported, none twice).
* **Could not**: cache misses (the instrumented quantity separating Move-r from
  r-index by 15×), prefetching/SIMD width, page faults and working-disk I/O (2 TB
  for grlBWT), memory bandwidth, construction constants (libsais = 7.7 of 21 h).
  A word-RAM cost of 1 per step is consistent with implementations an order of
  magnitude apart, so any "faster queries" claim must stay a claim about step
  counts unless measured.

## 6. Confidence and open items

* **UNVERIFIED**: MONI's own MEM-query timings (full text publisher-restricted;
  only the abstract's construction claim verified).
* **UNVERIFIED**: the "pangenome r-index / thesis (Ahmed–Rossi–Boucher)" item.
  Nearest verifiable descendant: Moni-align (Varki et al., Genome Res. 2025),
  claiming *accuracy* parity with vg giraffe/vg map and "best suited for aligning
  to localized pangenomes owing to computational constraints" — no speed factor.
* **UNVERIFIED**: Move-r's absolute per-query throughputs exist only in Figure 6;
  I quote its prose claims instead.
* Source inconsistency: ropebwt3 gives 20.5 h in Table 3, "21 hours" in text.
