#!/usr/bin/env python3
"""lz.py -- greedy LZ77 factorization with a hash-chain matcher.

WHICH LZ77.  A parse of S = S[0..n) is a sequence of phrases P_1..P_z; phrase j
starts at b_j, has length L_j >= 1 and covers S[b_j .. b_j+L_j), with b_1 = 0 and
b_{j+1} = b_j + L_j, so the phrases tile S exactly.  Phrase j is either

  a LITERAL  L_j = 1, dist = 0, or
  a COPY     distance d with 1 <= d <= b_j and S[b_j + t] = S[b_j - d + t] for
             all 0 <= t < L_j.

This is the standard LZ77 of KP18 (Lemma 3.7) / KNP23, where z is the number of
phrases.  By default a copy may overlap its own output (t >= d, "self-
referencing", what gzip/zlib do); `overlap=False` gives the variant whose source
must lie entirely in the already-parsed prefix b_j - d + L_j <= b_j.

The overlap only changes z, never validity, and it is what makes z(a^n) = 2:
with `overlap=False`, a^n has Theta(log n) phrases instead.  On the two texts
where the literature pins z down, both variants agree (see check.py:

    z(Thue-Morse word t_n) = 2n     KTMSIT20, reproduced for n = 4..16
    z(Fibonacci word F_m)  = m      W25 Thm 10, reproduced for m = 10..18

in this file's numbering, F_1 = "a", F_2 = "ab", |F_m| = Fib_m).

WHY OVERLAP DOES NOT WEAKEN THE ATTRACTOR ARGUMENT (used in attractor_from_lz).
Inside a copy phrase S[b_j + t] = S[b_j - d + t] holds for EVERY t in [0, L_j):
for t < d the source is outside the phrase, and for t >= d the character
S[b_j + t - d] has already been written because b_j + t - d < b_j + t.  So
S[p] = S[p - d] for every position p of a copy phrase, by induction on t.  That
single property is all the construction uses.

GREEDY.  At each phrase start b we take the longest copy available,

    L = max { lcp(S[b:], S[s:]) : s < b },  capped by n - b (and, when
                                             overlap=False, by b - s),

and emit a literal only when L < 2.  That is the canonical parse whose phrase
count is the published z.

THE MATCHER, AND WHAT IT COSTS.
  * Hash chains on g-grams (g = 3): bucket position i under S[i:i+g] and link it
    to the previous position with the same g-gram, so every position s < b whose
    g-gram equals S[b:b+g] is reachable from b by walking the chain.  A match of
    length >= g is found by that walk.  A g-gram bucket cannot see a match of
    length exactly 2, so a second chain (2-grams) supplies those.  For
    overlap=True one candidate is enough for that chain -- the most recent one --
    because every candidate is capped at n - b, so a candidate whose lcp is >= 3
    is also in the g-gram chain, and a candidate whose lcp is 2 is matched by the
    most recent one as well (its 2-gram matches, so its lcp is >= 2).  For
    overlap=False the cap b - s depends on the candidate, so the whole 2-gram
    chain is walked.
  * lcp(i, s) is computed by exponential search plus binary search on *slice
    equality*, which is a single C-level memcmp per probe: O(log L) probes and
    O(L) bytes moved per candidate, not O(L) Python iterations.
  * Expected cost: O(n) hash insertions + O(#phrases * chain_length) chain steps.
    With `max_chain=None` (the default) the walk is unbounded, so the parse is
    EXACTLY the greedy longest-match parse and the cost is
    O(n + sum over phrases of (chain length * L)) -- i.e. Theta(n) expected on
    random text, but not a linear-time guarantee: an adversarial text with long
    g-gram chains and long matches can make it quadratic.  With an integer
    `max_chain` the work is O(n * max_chain * L) worst case and z can exceed the
    greedy z, because a truncated walk can miss the longest match; the parse
    stays VALID (every copy is still a real earlier occurrence), so every
    attractor statement in this directory is unaffected.
  There is no suffix-array shortcut here on purpose: the attractor construction
  must not depend on the same machinery that verifies it, and this matcher is
  a different algorithm from verify.py's suffix array.

Symbols are bytes: str is UTF-8 encoded, bytes/bytearray is used as is, an
iterable of ints must be in 0..255.
"""

from collections import namedtuple

GRAM = 3          # hash-key length for the chain walk (matches of length >= GRAM)
TWO = 2           # hash-key length for the "match of length exactly 2" table


class Phrase(namedtuple("Phrase", "start length dist")):
    """One LZ77 phrase: S[start .. start+length), copied from start - dist.

    dist == 0 marks a literal (then length == 1).  A copy has 1 <= dist <= start
    and dist may be smaller than length (overlapping copy).
    """

    __slots__ = ()

    @property
    def is_literal(self):
        return self.dist == 0

    @property
    def end(self):
        """The index of the LAST character of the phrase: start + length - 1."""
        return self.start + self.length - 1

    def __repr__(self):
        kind = "lit" if self.is_literal else "cpy d=%d" % self.dist
        return "Phrase(%d..%d %s)" % (self.start, self.end, kind)


def to_bytes(text):
    """str | bytes | iterable of ints in 0..255 -> bytes."""
    if isinstance(text, str):
        return text.encode("utf-8")
    if isinstance(text, (bytes, bytearray)):
        return bytes(text)
    out = bytearray()
    for c in text:
        if not isinstance(c, int) or not 0 <= c <= 255:
            raise TypeError("symbols must be ints in 0..255, got %r" % (c,))
        out.append(c)
    return bytes(out)


def lcp(seq, a, b, limit):
    """Longest common prefix of seq[a:] and seq[b:], capped at `limit`.

    Exponential search for a failing length, then binary search; every probe is
    one slice comparison, i.e. C-speed memcmp, so the Python overhead is
    O(log limit) and the byte traffic is O(limit).
    """
    if limit <= 0:
        return 0
    lo, step = 0, 2
    while step <= limit and seq[a:a + step] == seq[b:b + step]:
        lo = step
        step <<= 1
        assert lo <= limit                       # progress: lo strictly grows
    hi = min(step, limit)
    assert lo <= hi
    while lo < hi:
        mid = (lo + hi + 1) >> 1
        if seq[a:a + mid] == seq[b:b + mid]:
            lo = mid                             # progress: lo strictly grows
        else:
            hi = mid - 1
    return lo


def _chains(seq, gram, two):
    """prev[i] = previous position with the same gram-gram, prev2[i] likewise for 2-grams."""
    n = len(seq)
    prev = [-1] * n
    prev2 = [-1] * n
    head = {}
    head2 = {}
    for i in range(n):
        if i + gram <= n:
            key = seq[i:i + gram]
            prev[i] = head.get(key, -1)
            head[key] = i
        if i + two <= n:
            key2 = seq[i:i + two]
            prev2[i] = head2.get(key2, -1)
            head2[key2] = i
        # progress: every position is linked exactly once, in increasing order, so
        # both chains are strictly decreasing and terminate at -1
        assert prev[i] == -1 or prev[i] < i
        assert prev2[i] == -1 or prev2[i] < i
    return prev, prev2


def lz77(text, overlap=True, max_chain=None, gram=GRAM, two=TWO):
    """The greedy LZ77 parse of `text` as a list of Phrase, in text order.

    overlap=True  copies may overlap their own output (standard, default);
    max_chain     bound on the hash-chain walk (None = unbounded = exact greedy).
    """
    seq = to_bytes(text)
    n = len(seq)
    if n == 0:
        return []
    if gram < 2:
        raise ValueError("gram must be >= 2")
    prev, prev2 = _chains(seq, gram, two)

    phrases = []
    pos = 0
    while pos < n:
        best_len = 0
        best_dist = 0
        cap = n - pos                            # a copy can never be longer

        # every match of length >= gram starts with a gram-gram candidate
        if pos + gram <= n:
            cand = prev[pos]
            steps = 0
            while cand >= 0 and (max_chain is None or steps < max_chain):
                assert 0 <= cand < pos           # progress: cand decreases
                steps += 1
                limit = cap if overlap else min(cap, pos - cand)
                if limit > best_len:
                    got = lcp(seq, pos, cand, limit)
                    if got > best_len:
                        best_len = got
                        best_dist = pos - cand
                        if best_len == cap:
                            break
                cand = prev[cand]

        # matches of length exactly two: a g-gram bucket cannot see them.  With
        # overlap the most recent candidate settles the whole chain (see the
        # module docstring); without it the cap depends on the candidate, so the
        # chain is walked.
        if pos + two <= n:
            cand = prev2[pos]
            steps = 0
            while cand >= 0 and (max_chain is None or steps < max_chain):
                assert 0 <= cand < pos           # progress: cand decreases
                steps += 1
                limit = cap if overlap else min(cap, pos - cand)
                if limit > best_len:
                    got = lcp(seq, pos, cand, limit)
                    if got > best_len:
                        best_len = got
                        best_dist = pos - cand
                        if best_len == cap:
                            break
                if overlap:
                    break                        # every other 2-gram candidate is
                cand = prev2[cand]               # in the g-gram chain or no better

        if best_len < two:
            phrases.append(Phrase(pos, 1, 0))
            pos += 1                             # progress
        else:
            phrases.append(Phrase(pos, best_len, best_dist))
            pos += best_len                       # progress: best_len >= 2
    assert pos == n
    return phrases


def phrase_count(phrases):
    """z, the number of phrases.  The empty text has z = 0 (no phrases)."""
    return len(phrases)


def longest_match_bruteforce(seq, b, overlap=True):
    """The longest copy length available at b, by exhaustive search.  O(n^2).

    The reference the greedy matcher is checked against in check.py; not used by
    anything else.  `seq` must be bytes.
    """
    best = 0
    for s in range(b):
        limit = len(seq) - b if overlap else min(len(seq) - b, b - s)
        got = lcp(seq, b, s, limit)
        if got > best:
            best = got
    return best
