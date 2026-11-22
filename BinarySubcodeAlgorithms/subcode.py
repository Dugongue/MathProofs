"""Exact binary permutation subcode containment. Rows are length-r bit masks.

The permutation returned by count_embeddings maps source indices to target
indices. The separator algorithm is exponential and is intended for short codes.
"""
from itertools import combinations


def positions(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def reduce_word(word, rows):
    for row in rows:
        word = min(word, word ^ row)
    return word


def basis(rows):
    """Canonical reduced basis, with decreasing pivot indices."""
    result = []
    for word in rows:
        word = reduce_word(word, result)
        if word:
            pivot = 1 << (word.bit_length() - 1)
            result = [v ^ word if v & pivot else v for v in result]
            result.append(word)
            result.sort(reverse=True)
    return tuple(result)


def normalized(r, rows):
    rows = tuple(rows)
    if r < 0 or any(v < 0 or v >= 1 << r for v in rows):
        raise ValueError("Expected nonnegative r and length-r binary rows.")
    return basis(rows)


def dual(r, rows):
    rows = basis(rows)
    pivot_mask = sum(1 << (row.bit_length()-1) for row in rows)
    result = []
    for i in positions(((1 << r)-1) ^ pivot_mask):
        word = 1 << i
        for row in rows:
            if row >> i & 1:
                word |= 1 << (row.bit_length()-1)
        result.append(word)
    return basis(result)


def words(rows):
    result = [0]
    for row in rows:
        result += [v ^ row for v in result]
    return result


def weight_classes(rows):
    classes = {}
    for v in words(rows):
        if v:
            classes.setdefault(v.bit_count(), []).append(v)
    return {w: basis(xs) for w, xs in classes.items()}


def prune_target(r, source, target):
    """Intersect every host span certified by a generating mask of the source."""
    src, dst = weight_classes(source), weight_classes(target)
    weights = tuple(sorted(src))
    constraints = dual(r, target)
    for size in range(len(weights)+1):
        for selected in combinations(weights, size):
            if len(basis(v for w in selected for v in src[w])) != len(source):
                continue
            candidate = basis(v for w in selected for v in dst.get(w, ()))
            constraints = basis((*constraints, *dual(r, candidate)))
    return dual(r, constraints)


def tighten(r, source, target):
    """Preserve the complete transporter set, alternating primal and dual."""
    source, target = normalized(r, source), normalized(r, target)
    while len(source) <= len(target):
        previous_gap = len(target)-len(source)
        target = prune_target(r, source, target)
        if len(source) > len(target):
            break
        source = dual(r, prune_target(r, dual(r, target), dual(r, source)))
        if len(target)-len(source) == previous_gap:
            break
    return source, target


def columns(r, rows):
    return [sum(((v >> i) & 1) << j for j, v in enumerate(rows)) for i in range(r)]


def spans_and_cuts(cols):
    full = (1 << len(cols))-1
    spans = [()] * (full+1)
    for mask in range(1, full+1):
        bit = mask & -mask
        spans[mask] = basis((*spans[mask ^ bit], cols[bit.bit_length()-1]))
    total_rank = len(spans[full])
    cuts = [len(spans[s])+len(spans[full ^ s])-total_rank for s in range(full+1)]
    return spans, cuts


def optimal_tree(r, source_cuts, target_cuts):
    full = (1 << r)-1
    max_target = [0] * (r+1)
    for t, width in enumerate(target_cuts):
        max_target[t.bit_count()] = max(max_target[t.bit_count()], width)
    cost = [0] * (full+1)
    splits = {}
    for s in range(1, full+1):
        node_cost = source_cuts[s] * max_target[s.bit_count()]
        cost[s] = node_cost
        if s & (s-1):
            pivot = s & -s
            left = (s-1) & s
            best = None
            while left:
                if left & pivot:
                    score = max(cost[left], cost[s ^ left], node_cost)
                    if best is None or score < best:
                        best, splits[s] = score, left
                        if score == node_cost:
                            break
                left = (left-1) & s
            cost[s] = best
    return cost[full], splits


def tree_count(r, a, b, spans_a, spans_b, splits):
    full = (1 << r)-1
    k, h = len(spans_a[full]), len(spans_b[full])
    column_mask = (1 << k)-1

    def outer(x, y):
        return sum(x << (k*j) for j in positions(y))

    def completable(total, outside_a, outside_b):
        cols = [(total >> (k*j)) & column_mask for j in range(h)]
        if any(reduce_word(v, outside_a) for v in cols):
            return False
        for i in range(k):
            row = sum(((v >> i) & 1) << j for j, v in enumerate(cols))
            if reduce_word(row, outside_b):
                return False
        return True

    def visit(s):
        # Each key (target subset, syndrome) stores a count and one partial map.
        table = {}
        if s & (s-1) == 0:
            i = s.bit_length()-1
            for j in range(r):
                t = 1 << j
                total = outer(a[i], b[j])
                if completable(total, spans_a[full ^ s], spans_b[full ^ t]):
                    table[t] = {total: (1, ((i,j),))}
            return table
        left = splits[s]
        left_table, right_table = visit(left), visit(s ^ left)
        right_size = (s ^ left).bit_count()
        for u, ls in left_table.items():
            for indices in combinations(positions(full ^ u), right_size):
                v = sum(1 << i for i in indices)
                if v not in right_table:
                    continue
                t = u | v
                out = table.setdefault(t, {})
                for x, (nx, wx) in ls.items():
                    for y, (ny, wy) in right_table[v].items():
                        z = x ^ y
                        if z in out:
                            count, witness = out[z]
                            out[z] = (count + nx*ny, witness)
                        elif completable(z, spans_a[full ^ s], spans_b[full ^ t]):
                            out[z] = (nx*ny, wx+wy)
        return table

    count, pairs = visit(full).get(full, {}).get(0, (0, ()))
    return count, tuple(j for _, j in sorted(pairs)) if count else None


def count_embeddings(r, source, target, prune=False):
    """Return (number of permutations, one permutation or None, tree cost)."""
    source, target = normalized(r, source), normalized(r, target)
    if prune:
        source, target = tighten(r, source, target)
    if len(source) > len(target):
        return 0, None, 0
    if r == 0:
        return 1, (), 0
    a, b = columns(r, source), columns(r, dual(r, target))
    sa, ca = spans_and_cuts(a)
    sb, cb = spans_and_cuts(b)
    x, tx = optimal_tree(r, ca, cb)
    y, ty = optimal_tree(r, cb, ca)
    if x <= y:
        n, p = tree_count(r, a, b, sa, sb, tx)
    else:
        n, inv = tree_count(r, b, a, sb, sa, ty)
        p = tuple(sorted(range(r), key=inv.__getitem__)) if inv is not None else None
    return n, p, min(x, y)


def quotient_spectrum(r, source, selected):
    """Number of distinct nonzero quotient cosets hit by the given weights."""
    source = normalized(r, source)
    return len({v for v in (reduce_word(x, source) for x in range(1 << r)
                            if x.bit_count() in selected) if v})


def count_group_epimorphisms(r, source, target, prune=False):
    """Count maps G(C) -> G(D) for the groups specified by the given codes.

    The returned permutation induces one epimorphism by relabeling both the
    ternary vector and the quaternary representative coordinatewise.
    """
    target = normalized(r, target)
    count, permutation, _ = count_embeddings(r, source, target, prune)
    return count * 6**r * 2**(r*(r-len(target))), permutation
