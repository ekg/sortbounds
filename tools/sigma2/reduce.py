"""reduce.py -- candidate polynomial reductions to "minimum attractor of a binary string".

Source problem: VERTEX COVER (decision form)
    VC(G, q):  is there S subset of V(G) with |S| <= q and every edge of G met by S?
    tau(G)    = the minimum such |S|.

Target problem: minimum string attractor, full attractor (k = n), alphabet {0,1}
    gamma(T)  = min |Gamma| such that every distinct factor of T has an
                occurrence crossing some position of Gamma.

Both variants below map a graph G with n = |V| and m = |E| to a binary word T_G
whose length is O((n + m) log n), and the *candidate* claim under test is

    (CLAIM-tags / CLAIM-hubs)   gamma(T_G) <= m + q   iff   tau(G) <= q .

Since gamma and tau are integers, CLAIM is equivalent to the exact identity
gamma(T_G) = m + tau(G); check.py tests the identity AND the threshold form.

Why vertex cover: Kempa-Prezza's k-attractor hardness (STOC 2018, Thm 4.2 and
Thm 4.3) already reduces from k-SET COVER / bounded-degree vertex cover, so the
*gadget architecture* to imitate is theirs; and vertex cover is the smallest
source whose every instance can be enumerated, which is what the mission's
"check the equivalence exhaustively" requires.

Vocabulary used below (all of it is the set-cover view, see
../attractor/instance.py for the definitions this file relies on):

    class        a distinct factor of T, identified with the content string
    cover(p)     the classes with an occurrence [i, i+|f|) such that i <= p < i+|f|
    charge       one position of the attractor; the cost is the number of charges

Design intent (the "ledger") that the two variants try to realise:

    * every edge e = (u,v) owns a *block* -- a contiguous region of T_G.  The
      block contains a factor that occurs nowhere else, so every attractor needs
      at least one charge inside the block ("the block's own charge").
    * the block additionally owns two *spots*, A_e^u and A_e^v, one per endpoint.
      A_e^u's class reoccurs outside the block (in the region we call hub(u)), so
      A_e^u can be covered either by a charge inside the block's u-spot or by a
      charge inside an occurrence of A_e^u elsewhere.
    * "paying for u" means spending one charge that covers A_e^u for every edge e
      incident to u at once; "not paying for u" costs one extra charge per
      incident block (each block then needs a charge at its u-spot).
    * the ledger value is then  #paid + sum_e (1 + [neither endpoint paid])
      = m + min_H( |H| + #{e : e meets H is empty} ) = m + tau(G),
      because a set H meeting every edge is a vertex cover.

The second bullet is what breaks in {0,1}.  See sigma2-gadget.md.
"""

import itertools
import random


# --------------------------------------------------------------------------
# labels
# --------------------------------------------------------------------------


def label_bits(n):
    """Number of bits L with 2**L >= n, so that n vertices get distinct labels."""
    if n <= 1:
        return 1
    L = 0
    while (1 << L) < n:
        L += 1
    return L


def tag(v, L):
    """The label word of vertex v: '1' followed by the L-bit binary of v.

    Length L+1, so tags are distinct; they are NOT prefix-free against each other
    (all start with '1'), which is one of the deliberate defects the checker
    measures: a tag can occur across a block boundary.
    """
    assert 0 <= v < (1 << L)
    return "1" + format(v, "0%db" % L)


# --------------------------------------------------------------------------
# the two constructions
# --------------------------------------------------------------------------


def edges_in_order(n, edges):
    """Canonical edge order (u < v, sorted), so the text is a function of (n, edges)."""
    return sorted((min(u, v), max(u, v)) for (u, v) in edges)


def text_tags(n, edges, L=None, relabel=None):
    """Variant 'tags':  concat_v tag(v)  ++  concat_e tag(u) tag(v).

    relabel: optional permutation, applied so that the labelled text can differ
    while the abstract graph stays the same (used by the label-variance test).
    """
    if L is None:
        L = label_bits(n)
    lab = list(range(n)) if relabel is None else list(relabel)
    assert sorted(lab) == list(range(n))
    out = []
    for v in range(n):
        out.append(tag(lab[v], L))
    for (u, v) in edges_in_order(n, edges):
        out.append(tag(lab[u], L))
        out.append(tag(lab[v], L))
    return "".join(out)


def text_tags_sep(n, edges, L=None, sep="00", relabel=None):
    """Variant 'tags+sep': every tag is followed by the same separator.

    The separator is a repeated homogeneous word, so its own factors cost O(1)
    charges in total (they occur at every gap).  The purpose of the variant is to
    test whether block-boundary factors -- not the blocks themselves -- were what
    broke 'tags'.
    """
    if L is None:
        L = label_bits(n)
    lab = list(range(n)) if relabel is None else list(relabel)
    out = []
    for v in range(n):
        out.append(tag(lab[v], L) + sep)
    for (u, v) in edges_in_order(n, edges):
        out.append(tag(lab[u], L) + sep + tag(lab[v], L) + sep)
    return "".join(out)


def text_hubs(n, edges, L=None, sep="00", copies=3, relabel=None):
    """Variant 'hubs': a hub region per vertex, then one block per edge.

    hub(v) = tag(v) repeated `copies` times, followed by the separator; the block
    of e = (u,v) is tag(u) sep tag(v) sep.  The intent was that one charge inside
    hub(u) covers A_e^u for every edge e at u (since the class tag(u) occurs
    there); the measurement in check.py shows whether that is enough to make the
    ledger m + tau, and the report explains why it cannot be.
    """
    if L is None:
        L = label_bits(n)
    lab = list(range(n)) if relabel is None else list(relabel)
    out = []
    for v in range(n):
        out.append(tag(lab[v], L) * copies + sep)
    for (u, v) in edges_in_order(n, edges):
        out.append(tag(lab[u], L) + sep + tag(lab[v], L) + sep)
    return "".join(out)


VARIANTS = {
    "tags": text_tags,
    "tags_sep": text_tags_sep,
    "hubs": text_hubs,
}


def build(variant, n, edges, **kw):
    return VARIANTS[variant](n, edges, **kw)


# --------------------------------------------------------------------------
# size bound
# --------------------------------------------------------------------------


def size_bound(variant, n, m):
    """Proved upper bound on |T_G| for each variant (L = label_bits n)."""
    L = label_bits(n)
    tag_len = L + 1
    sep = 2
    if variant == "tags":
        return n * tag_len + 2 * m * tag_len
    if variant == "tags_sep":
        return n * (tag_len + sep) + m * (2 * tag_len + 2 * sep)
    if variant == "hubs":
        return n * (3 * tag_len + sep) + m * (2 * tag_len + 2 * sep)
    raise KeyError(variant)


# --------------------------------------------------------------------------
# source problem: vertex cover, brute force (exhaustive, so exact)
# --------------------------------------------------------------------------


def tau(n, edges):
    """Minimum vertex cover size of a graph on 0..n-1, by exhaustive search."""
    edges = edges_in_order(n, edges)
    best = n
    for size in range(0, n + 1):
        if size >= best:
            break
        for S in itertools.combinations(range(n), size):
            Sset = set(S)
            if all(u in Sset or v in Sset for (u, v) in edges):
                return size
    return best


def cover_witness(n, edges, q):
    """A vertex cover of size <= q, or None."""
    edges = edges_in_order(n, edges)
    for size in range(0, q + 1):
        for S in itertools.combinations(range(n), size):
            Sset = set(S)
            if all(u in Sset or v in Sset for (u, v) in edges):
                return S
    return None


# --------------------------------------------------------------------------
# the intended attractor, for the easy direction of the claim
# --------------------------------------------------------------------------


def designed_charge_pattern(variant, n, edges, cover):
    """Positions of the attractor the *ledger* prescribes for a given vertex cover.

    Returns a list of positions in T_G, or None if the variant's layout is not
    known to this function.  check.py verifies that this set really is an
    attractor of T_G (definition-level), which is the ONLY thing needed for the
    direction tau(G) <= q  =>  gamma(T_G) <= m + q.
    """
    if variant not in ("tags", "tags_sep", "hubs"):
        raise KeyError(variant)
    L = label_bits(n)
    tl = L + 1
    sep = 2
    cover = set(cover)
    pos = []
    if variant == "tags":
        cur = n * tl
        for (u, v) in edges_in_order(n, edges):
            # block occupies [cur, cur + 2*tl); put one charge in the u-spot if
            # u is in the cover (that charge covers the block's unique factor and
            # the class of tag(u)), otherwise one charge in the v-spot.
            base = cur
            if u in cover:
                pos.append(base)                       # inside tag(u)
            else:
                pos.append(base + tl)                  # inside tag(v)
            cur += 2 * tl
        # the tag region at the front: cover the classes that only occur there
        for v in range(n):
            pos.append(v * tl + tl // 2)
        return sorted(set(pos))
    if variant == "tags_sep":
        cur = n * (tl + sep)
        for (u, v) in edges_in_order(n, edges):
            base = cur
            pos.append(base if u in cover else base + tl + sep)
            cur += 2 * tl + 2 * sep
        for v in range(n):
            pos.append(v * (tl + sep) + tl // 2)
        return sorted(set(pos))
    if variant == "hubs":
        cur = n * (3 * tl + sep)
        for (u, v) in edges_in_order(n, edges):
            base = cur
            pos.append(base if u in cover else base + tl + sep)
            cur += 2 * tl + 2 * sep
        for v in range(n):
            pos.append(v * (3 * tl + sep) + tl // 2)
        return sorted(set(pos))
    raise KeyError(variant)


# --------------------------------------------------------------------------
# labelings of one abstract graph (for the necessary-condition test)
# --------------------------------------------------------------------------


def random_relabelings(n, k, seed):
    rng = random.Random(seed)
    seen = set()
    out = []
    identity = tuple(range(n))
    out.append(identity)
    seen.add(identity)
    guard = 0
    while len(out) < k and guard < 100 * k:
        guard += 1
        p = list(range(n))
        rng.shuffle(p)
        p = tuple(p)
        if p not in seen:
            seen.add(p)
            out.append(p)
    return out


def canonical_edge_set(n, edges):
    """Edge set expressed on the smallest-vertex-first order (isomorphism key
    used only for tiny graphs, where brute force over permutations is affordable)."""
    return tuple(edges_in_order(n, edges))


def all_labelings_iso_classes(n):
    """Yield one representative edge set per isomorphism class of graphs on n nodes.

    Brute force over all n! relabellings and all edge sets; only for n <= 5.
    """
    import itertools as it
    perms = list(it.permutations(range(n)))
    seen = set()
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for mask in range(1 << len(pairs)):
        es = frozenset(pairs[k] for k in range(len(pairs)) if (mask >> k) & 1)
        if es in seen:
            continue
        orbit = set()
        for p in perms:
            img = frozenset(tuple(sorted((p[u], p[v]))) for (u, v) in es)
            orbit.add(img)
        seen |= orbit
        yield edges_in_order(n, es)
