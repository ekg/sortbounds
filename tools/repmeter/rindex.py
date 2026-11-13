#!/usr/bin/env python3
"""A run-length FM-index: count and locate on the BWT of T$ in O(r) space.

This is the r-index's core primitive (Gagie-Navarro-Prezza 2020), not the full
r-index: there is no move structure and no toehold lemma, so locate walks the
LF-mapping per occurrence instead of jumping between runs, and count spends a
binary search per rank query.  Both are honest but slower:

    count   O(m log r)        (binary search over run boundaries per character)
    locate  O(m log r + occ*s) (s = sampling stride; each occurrence walks <= s steps)

Space: O(r) runs + O(n/s) sampled suffix-array entries + O(r) prefix counts per
distinct character of sigma.

The point of the exercise is the space: on a repetitive text r << n, and this
index is r-sized where an FM-index would be n-sized.
"""
import sys, argparse, random
from bisect import bisect_right

# ---------------------------------------------------------------- suffix array
def suffix_array(s):
    """Prefix-doubling SA of a list of ints.  O(n log^2 n) with sort keys."""
    n = len(s)
    sa = sorted(range(n), key=lambda i: s[i:])       # base: full comparison
    return sa

def suffix_array_fast(s):
    """Prefix doubling with rank arrays: O(n log^2 n) but with cheap comparisons."""
    n = len(s)
    if n == 0:
        return []
    rank = list(s)
    k = 1
    sa = sorted(range(n), key=lambda i: rank[i])
    tmp = [0] * n
    while True:
        # sort by (rank[i], rank[i+k]) using the previous sa to build ranks
        key = [(rank[i], rank[i + k] if i + k < n else -1) for i in range(n)]
        sa = sorted(range(n), key=lambda i: key[i])
        tmp[sa[0]] = 0
        for j in range(1, n):
            tmp[sa[j]] = tmp[sa[j - 1]] + (1 if key[sa[j]] != key[sa[j - 1]] else 0)
        rank = tmp[:]
        if rank[sa[-1]] == n - 1:
            break
        k *= 2
    return sa

# ---------------------------------------------------------------- the index
class RLFM:
    """Run-length FM-index over T, with an explicit sentinel that sorts first."""

    def __init__(self, text, stride=32):
        self.text = list(text)
        n = len(self.text)
        # sentinel: 0, text symbols: 1 + symbol (symbols are non-negative ints)
        t = [0] + [1 + c for c in self.text]
        self.t = t
        self.n1 = len(t)
        sa = suffix_array_fast(t)
        self.sa = sa
        # BWT
        bwt = [t[(i - 1) % self.n1] for i in sa]
        self.bwt = bwt
        # runs
        runs = []
        for c in bwt:
            if runs and runs[-1][0] == c:
                runs[-1][1] += 1
            else:
                runs.append([c, 1])
        self.runs = [(c, l) for c, l in runs]
        self.r = len(self.runs)
        # run start positions and cumulative counts per symbol
        starts = []
        pos = 0
        for c, l in self.runs:
            starts.append(pos)
            pos += l
        self.starts = starts
        self.symbols = sorted({c for c, _ in self.runs})
        # cum[c][j] = # of c in runs[0:j]
        self.cum = {c: [0] * (self.r + 1) for c in self.symbols}
        for j, (c, l) in enumerate(self.runs):
            for d in self.symbols:
                self.cum[d][j + 1] = self.cum[d][j]
            self.cum[c][j + 1] += l
        # C[c] = # of symbols < c in BWT (= in T)
        self.C = {}
        acc = 0
        for c in self.symbols:
            self.C[c] = acc
            acc += self.cum[c][self.r]
        # sampled SA for locate
        self.stride = stride
        self.sample = [i for i in range(self.n1) if sa[i] % stride == 0]

    # rank(c, i) = # of c in BWT[0:i]
    def rank(self, c, i):
        cum = self.cum.get(c)
        if cum is None or i <= 0:
            return 0
        j = bisect_right(self.starts, i - 1) - 1   # run containing i-1
        if j < 0:
            return 0
        cnt = cum[j]                               # occurrences in runs[0:j]
        cj, lj = self.runs[j]
        if cj == c:                                # plus the part of run j before i
            cnt += min(i - self.starts[j], lj)
        return cnt

    def count(self, pat):
        pat = [1 + c for c in pat]
        sp, ep = 0, self.n1 - 1
        for c in reversed(pat):
            sp = self.C.get(c, 0) + self.rank(c, sp)
            ep = self.C.get(c, 0) + self.rank(c, ep + 1) - 1
            if sp > ep:
                return 0, sp, ep
        return ep - sp + 1, sp, ep

    def locate(self, pat):
        cnt, sp, ep = self.count(pat)
        out = []
        for row in range(sp, ep + 1):
            steps = 0
            j = row
            while self.sa[j] % self.stride != 0:     # walk down to a sampled row
                j = self.C[self.bwt[j]] + self.rank(self.bwt[j], j)
                steps += 1
            out.append((self.sa[j] + steps - 1) % self.n1)  # -1: sentinel shift
        return cnt, out

    def size_words(self):
        # runs (char, len) = 2 words each; cum per symbol over runs; samples
        return 2 * self.r + len(self.symbols) * (self.r + 1) + len(self.sample)

# ---------------------------------------------------------------- self-test
def brute_count(T, pat):
    T = list(T); p = list(pat); n = len(T); m = len(p)
    return [i for i in range(n - m + 1) if T[i:i + m] == p]

def selftest(verbose=False):
    checks = 0
    for n in range(0, 10):
        for mask in range(2 ** n):
            T = [(mask >> i) & 1 for i in range(n)]
            idx = RLFM(T, stride=4)
            for m in range(0, min(n, 3) + 1):
                for patmask in range(2 ** m):
                    pat = [(patmask >> i) & 1 for i in range(m)]
                    got_cnt, _sp, _ep = idx.count(pat)
                    ref = brute_count(T, pat)
                    assert got_cnt == len(ref), (T, pat, got_cnt, len(ref))
                    got_loc = sorted(idx.locate(pat)[1])
                    assert got_loc == sorted(ref), (T, pat, got_loc, ref)
                    checks += 1
    print("selftest: %d pattern queries, count and locate both agree with brute force" % checks)
    return checks

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--text")
    ap.add_argument("--gen")
    ap.add_argument("--m", type=int, default=8)
    ap.add_argument("--queries", type=int, default=200)
    a = ap.parse_args()
    if a.selftest:
        selftest(); sys.exit(0)
    if a.text is not None:
        T = [ord(c) for c in a.text]
    elif a.gen:
        kind = a.gen.split(":")[0]
        k = int(a.gen.split(":")[1])
        if kind == "fibonacci":
            x, y = [0], [1]
            for _ in range(k):
                x, y = y, x + y
            T = y
        elif kind == "thue-morse":
            T = [0]
            while len(T) < 2 ** k:
                T = T + [1 - c for c in T]
        elif kind == "random-binary":
            rnd = random.Random(int(a.gen.split(":")[2]) if a.gen.count(":") > 1 else 1)
            T = [rnd.getrandbits(1) for _ in range(k)]
        else:
            sys.exit("unknown gen")
    else:
        sys.exit("need --text or --gen")
    n = len(T)
    idx = RLFM(T, stride=32)
    rnd = random.Random(7)
    hits = 0
    for _ in range(a.queries):
        i = rnd.randrange(0, max(1, n - a.m))
        pat = T[i:i + a.m]
        if idx.count(pat)[0] > 0:
            hits += 1
    print("input      n=%d" % n)
    print("runs r     %d   (r/n = %.5f)" % (idx.r, idx.r / n if n else 0))
    print("index size ~%d words  (%.1f%% of n words)" % (idx.size_words(), 100.0 * idx.size_words() / n if n else 0))
    print("FM-index would be %d words (100%%)" % n)
    print("count      %d queries of m=%d, %d non-empty" % (a.queries, a.m, hits))
