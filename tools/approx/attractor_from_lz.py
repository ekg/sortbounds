#!/usr/bin/env python3
"""attractor_from_lz.py -- an attractor of size at most z from an LZ77 parse.

[PROVED, KP18 Lemma 3.7]  "Let z be the number of factors of the Lempel-Ziv
factorization of a string T.  Then T has an attractor of size z."  Quoted in
docs/research/attractor-approx.md §1.1, whose proof line is "we insert in
Gamma_LZ77 all positions at the end of a phrase".  The construction below is
exactly that, and nothing else: no search, no greedy, no pruning.

THE CONSTRUCTION, STEP BY STEP.

  1. Parse: S[0..n) = P_1 ... P_z, phrase j covering [b_j, e_j] with
     b_1 = 0, b_{j+1} = e_j + 1, e_j = b_j + L_j - 1 (lz.py).  Positions are
     0-based; e_j is the index of the LAST character of phrase j.
  2. Emit ONE position per phrase: e_j, for every j.  So

         Gamma_LZ = { e_1, ..., e_z }.

     e_1 < e_2 < ... < e_z because every phrase is nonempty, so the e_j are
     distinct and |Gamma_LZ| = z exactly -- not "at most z": z.

WHY GAMMA_LZ IS AN ATTRACTOR (i.e. why every distinct factor has an occurrence
crossing Gamma_LZ).  Let f be a distinct factor, |f| = m, and take its LEFTMOST
occurrence S[i .. i+m).  Let j be the phrase containing its start, so
b_j <= i <= e_j.  Exactly one of two things happens.

  (A) i + m - 1 >= e_j.  Then i <= e_j <= i + m - 1, i.e. position e_j lies
      inside the occurrence [i, i+m): the occurrence crosses e_j, and e_j is in
      Gamma_LZ.  Done.

  (B) i + m - 1 < e_j: the whole occurrence lies strictly inside phrase j.
      Then phrase j is not a literal (a literal is one character, so i = e_j
      would contradict i + m - 1 < e_j), hence a copy with distance d,
      1 <= d <= b_j.  A copy phrase satisfies S[p] = S[p-d] for EVERY position p
      in [b_j, e_j] (see lz.py: for t >= d the source character has already
      been written, so this is induction on t; overlap of the copy with itself
      does not break it).  Applying that to p = i, ..., i+m-1 gives
      S[i+t] = S[i-d+t] for all t < m, i.e. f occurs again at i - d.  As
      d <= b_j <= i we have i - d >= 0, so this is a genuine occurrence, and
      i - d < i contradicts the leftmost choice of i.  So (B) never happens.

Cases (A) and (B) are exhaustive, so every distinct factor is covered: Gamma_LZ
is an attractor by the definition in tools/attractor/README.md (every distinct
factor has an occurrence crossing a position of Gamma).  This argument needs
nothing from the greedy rule -- any valid parse gives an attractor of size z --
and nothing from the matcher: even a `max_chain`-truncated parse (lz.py) yields a
valid parse, hence a valid attractor.

REMARK -- the phrase STARTS would do as well.  [MY-INFERENCE: this is not in
docs/research/attractor-approx.md, it is my own derivation, and it is checked
computationally in check.py (all binary texts of length <= 12) and reproduced on
every text of run.py.]  Gamma' = { b_j } is an attractor by the same two cases:
take the leftmost occurrence [i, i+m) of f and the phrase j containing i.

  (A') i + m - 1 >= b_{j+1}: then i <= b_{j+1} <= i + m - 1, so the occurrence
       crosses the NEXT phrase's start b_{j+1}, which is in Gamma'.  (When j is
       the last phrase, i + m <= n = b_{j+1} so this case cannot arise.)
  (B') i + m - 1 < b_{j+1}: the occurrence lies inside phrase j.  If i = b_j it
       crosses b_j, done.  Otherwise phrase j is a copy (a literal starts at b_j),
       so f occurs again at i - d < i -- contradicting leftmost-ness.

So both ends and starts work, one position per phrase either way; this file emits
the ENDS because that is the position KP18 Lemma 3.7 names.  Nothing in this
directory depends on the remark.

WHAT THIS DOES AND DOES NOT GIVE.

  * delta <= gamma <= |Gamma_LZ| = z.  [PROVED]  KP18 Lemma 3.7 for gamma <= z;
    KNP23 Lemma II.4 for delta <= gamma (machine-checked in this repository:
    `substringComplexity_le_card_attractor` in
    SortBounds/Projects/Repetitiveness/Attractor.lean).
  * |Gamma_LZ| <= 4(delta log(n/delta) + delta) <= gamma (4 log(n/gamma) + 4).
    [PROVED for the first step, KNP23 Lemma II.2; the chaining with delta <= gamma
    is MY-INFERENCE, as flagged in docs/research/attractor-approx.md §1.1]
    -- an O(log n) ratio, not a constant one.
  * |Gamma_LZ| / gamma is NOT bounded by a constant, and this construction is not
    claimed to be within any constant factor of gamma.  [PROVED-refutation, the
    C1 entry of attractor-approx.md §4: z(t_n) = 2n on the Thue-Morse word t_n
    (|t_n| = 2^n) where gamma = 4, and z(F_m) = m on the Fibonacci word where
    gamma = 2.]  run.py reproduces both numbers; see its table.
  * No claim of optimality, minimality, or irredundancy is made.  Gamma_LZ is a
    certificate, not an answer.
"""

from lz import lz77, phrase_count, to_bytes


def phrase_ends(phrases):
    """[e_j] = the last character of each phrase, strictly increasing."""
    ends = [p.end for p in phrases]
    for a, b in zip(ends, ends[1:]):
        assert a < b, "phrase ends must be strictly increasing"
    return ends


def attractor_from_parse(phrases, n=None):
    """Gamma_LZ = the phrase ends.  |Gamma_LZ| == number of phrases."""
    ends = phrase_ends(phrases)
    if n is not None:
        for e in ends:
            assert 0 <= e < n, "phrase end %d outside a text of length %d" % (e, n)
    assert len(ends) == phrase_count(phrases)
    return ends


def attractor_for_text(text, **lz_kwargs):
    """(Gamma_LZ, phrases) for one text.  lz_kwargs go to lz.lz77."""
    seq = to_bytes(text)
    phrases = lz77(seq, **lz_kwargs)
    return attractor_from_parse(phrases, len(seq)), phrases


def describe(phrases, seq):
    """The construction as text: one line per phrase (for the report/tests)."""
    out = []
    for j, p in enumerate(phrases, 1):
        piece = seq[p.start:p.start + p.length].decode("latin-1")
        if p.is_literal:
            what = "literal %r" % piece
        else:
            what = "copy of S[%d..] (d=%d) = %r" % (
                p.start - p.dist, p.dist, seq[p.start - p.dist:p.start - p.dist + p.length].decode("latin-1"))
        out.append("P%-3d [%3d,%3d] %-28s -> emits e=%d" % (j, p.start, p.end, what, p.end))
    return out
