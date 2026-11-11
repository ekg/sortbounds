"""Search for a minimum-depth comparison decision tree on `n` positions.

This is the generator behind the explicit trees in `Five.lean` (by hand there, by
this search for `Six.lean` / `Seven.lean`); it is *not* part of the trust base.
What it prints is a Lean literal, and the Lean kernel checks that literal:
`depth`, `numLeaves` and — through `correct_of_forall_run_xOfPerm` — correctness
on all `n!` canonical inputs are decided in `Six.lean` / `Seven.lean`.  A bug
here can only make the search fail or print a tree the kernel rejects; it cannot
make a wrong theorem pass.

Usage:  python3 search_optimal_tree.py N DEPTH [--threshold T] [--prefix NAME]

`N DEPTH` are the number of positions and the depth to search for.  The output is
the body of the corresponding `.lean` file: the definitions of the tree (split
into `private` subtrees when a single literal would be too large to elaborate
comfortably, see `--threshold`) and nothing else.

Model.  An *ordering* of `n` positions is a tuple `(p0, …, p_{n-1})` listing the
positions in increasing order of value, i.e. exactly the permutation that sorts
that input.  The search state at a node of the decision tree is the set of
orderings still consistent with the answers so far, held as a bitmask; comparing
positions `i` and `j` splits it into the orderings where `i` comes first and the
rest, and a leaf is a state with a single ordering.  The tree the search returns
is a depth-first one: at every node it tries the comparisons whose split is most
even (ties by the pair, then by the state), and backtracks.

The search is exhaustive and deterministic — a state that could not be finished
within the remaining depth is remembered, so it is never expanded twice — hence
the tree printed for a given `(N, DEPTH)` is always the same.
"""

import argparse
import itertools
import sys


def orderings(n):
    """All `n!` orderings of `range(n)`, and the bitmask of each comparison."""
    orders = list(itertools.permutations(range(n)))
    where = [{p: k for k, p in enumerate(o)} for o in orders]
    masks = {}
    for i in range(n):
        for j in range(i + 1, n):
            mask = 0
            for k, w in enumerate(where):
                if w[i] < w[j]:
                    mask |= 1 << k
            masks[(i, j)] = mask
    return orders, masks


def search(n, target, fix_first=(0, 1)):
    """A `Tree n` of depth `≤ target`, as nested `('node', i, j, l, r)` /
    `('leaf', state)` tuples, together with the list of orderings."""
    orders, masks = orderings(n)
    full = (1 << len(orders)) - 1
    failed = set()

    def go(state, r):
        m = state.bit_count()
        if m <= 1:
            return ('leaf', state)
        if r == 0 or m > (1 << r):
            return None
        if (state, r) in failed:
            return None
        capacity = 1 << (r - 1)
        candidates = []
        seen = set()
        for (i, j), mask in masks.items():
            left = state & mask
            size = left.bit_count()
            if size == 0 or size == m:
                continue
            if size > capacity or m - size > capacity:
                continue
            right = state ^ left
            key = (left, right) if size <= m - size else (right, left)
            if key in seen:
                continue
            seen.add(key)
            candidates.append((abs(2 * size - m), i, j, left))
        candidates.sort()
        for _, i, j, left in candidates:
            a = go(left, r - 1)
            if a is None:
                continue
            b = go(state ^ left, r - 1)
            if b is None:
                continue
            return ('node', i, j, a, b)
        failed.add((state, r))
        return None

    i, j = fix_first
    left = full & masks[(i, j)]
    a = go(left, target - 1)
    if a is None:
        return None, orders
    b = go(full ^ left, target - 1)
    if b is None:
        return None, orders
    return ('node', i, j, a, b), orders


def state_size(t):
    if t[0] == 'leaf':
        return t[1].bit_count()
    return state_size(t[3]) + state_size(t[4])


def tree_size(t):
    if t[0] == 'leaf':
        return 0
    return 1 + tree_size(t[3]) + tree_size(t[4])


def representative(state):
    """The single ordering of a leaf state, as an index."""
    return (state & -state).bit_length() - 1


def transpositions(order):
    """Transpositions `L` with `swapProd L = p`, where `p k = order[k]` and
    `swapProd [(a, b), …] = Equiv.swap a b * …` (rightmost factor applied first,
    as in `Verify.lean`).  A cycle `(a0 a1 … am)` is `[(a0,am), …, (a0,a1)]`."""
    perm = dict(enumerate(order))
    seen = set()
    out = []
    for start in range(len(order)):
        if start in seen:
            continue
        cycle = []
        x = start
        while x not in seen:
            seen.add(x)
            cycle.append(x)
            x = perm[x]
        for a in reversed(cycle[1:]):
            out.append((cycle[0], a))
    return out


def leaf_expr(order):
    ps = transpositions(order)
    if not ps:
        return '(.leaf 1)'
    return '(.leaf (swapProd [%s]))' % ', '.join('(%d, %d)' % p for p in ps)


def self_check(n, tree, orders):
    """Independent check of the certificate (the Lean kernel checks it again,
    from scratch, in `Six.lean` / `Seven.lean`): the leaf reached by the
    ordering `o` must carry `o` itself, and each leaf literal must denote the
    permutation it stands for."""
    for o in orders:
        t = tree
        while t[0] == 'node':
            _, i, j, l, r = t
            t = l if o.index(i) < o.index(j) else r
        if orders[representative(t[1])] != o:
            return 'leaf of ordering %r carries %r' % (o, orders[representative(t[1])])
        ps = transpositions(o)
        image = []
        for k in range(n):
            x = k
            for a, b in reversed(ps):
                if x == a:
                    x = b
                elif x == b:
                    x = a
            image.append(x)
        if tuple(image) != o:
            return 'leaf literal for %r denotes %r' % (o, tuple(image))
    return None


def emit(n, tree, orders, threshold, prefix):
    """The tree as Lean source, split so that no single term is huge."""
    pieces = []
    counter = [0]

    def inline(t, depth):
        pad = '  ' * depth
        if t[0] == 'leaf':
            return pad + leaf_expr(orders[representative(t[1])])
        _, i, j, l, r = t
        return '\n'.join([pad + '(.node %d %d   -- %d' % (i, j, state_size(t)),
                          inline(l, depth + 1), inline(r, depth + 1), pad + ')'])

    if threshold <= 0:
        threshold = 1 << 62

    def expr(t, depth):
        if tree_size(t) <= threshold:
            return inline(t, depth)
        pad = '  ' * depth
        _, i, j, l, r = t
        body = '\n'.join([pad + '(.node %d %d   -- %d' % (i, j, state_size(t)),
                          expr(l, depth + 1), expr(r, depth + 1), pad + ')'])
        name = '%s%d' % (prefix, counter[0])
        counter[0] += 1
        pieces.append((name, body))
        return pad + name

    top = expr(tree, 1)
    out = []
    if pieces:
        out.append('-- subtrees, children before parents')
        for name, body in pieces:
            out.append('private def %s : Tree %d :=\n%s\n' % (name, n, body))
        out.append('-- the whole tree')
    out.append('def %s : Tree %d :=\n%s' % (prefix, n, top))
    return '\n'.join(out)


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('n', type=int)
    parser.add_argument('depth', type=int)
    parser.add_argument('--threshold', type=int, default=120,
                        help='a subtree with more nodes than this becomes its own '
                             'private definition (0 disables the split)')
    parser.add_argument('--prefix', default=None)
    args = parser.parse_args(argv)

    prefix = args.prefix or 'tree%d' % args.n
    tree, orders = search(args.n, args.depth)
    if tree is None:
        print('no tree of depth %d on %d positions' % (args.depth, args.n),
              file=sys.stderr)
        return 1
    problem = self_check(args.n, tree, orders)
    if problem is not None:
        print('certificate does not check: ' + problem, file=sys.stderr)
        return 1
    print(emit(args.n, tree, orders, args.threshold, prefix))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
