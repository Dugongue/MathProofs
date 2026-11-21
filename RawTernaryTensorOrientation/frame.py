"""Recover the ternary contraction lines of one mode from its raw matrix pencil."""

from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations


# Disjoint bit sets encode coefficients +1 and -1 in increasing basis order.
ZERO = (0, 0)


def neg(v):
    return v[1], v[0]


def add(v, w):
    p, n = v
    q, m = w
    return ((p & ~(q | m)) | (q & ~(p | n)) | (n & m),
            (n & ~(q | m)) | (m & ~(p | n)) | (p & q))


def terms(v):
    for mask, sign in zip(v, (1, -1)):
        while mask:
            bit = mask & -mask
            yield bit.bit_length() - 1, sign
            mask ^= bit


def unit(i):
    return 1 << i, 0


def combine(coeffs, columns):
    result = ZERO
    for i, sign in terms(coeffs):
        result = add(result, columns[i] if sign == 1 else neg(columns[i]))
    return result


def insert(rows, vec):
    while vec != ZERO:
        bit = (vec[0] | vec[1]).bit_length() - 1
        if vec[1] >> bit:
            vec = neg(vec)
        if bit not in rows:
            rows[bit] = vec
            return
        vec = add(vec, neg(rows[bit]))


def remainder(vec, rows):
    for i in sorted(rows, reverse=True):
        if (vec[0] >> i) & 1:
            vec = add(vec, neg(rows[i]))
        elif (vec[1] >> i) & 1:
            vec = add(vec, rows[i])
    return vec


def kernel(columns, height):
    rows, basis = {}, []
    low = (1 << len(columns)) - 1
    for i, (p, n) in enumerate(columns):
        shifted = (p << len(columns) | (1 << i), n << len(columns))
        assert (p | n).bit_length() <= height
        reduced = remainder(shifted, rows)
        pivot = (reduced[0] | reduced[1]).bit_length() - 1
        if pivot >= len(columns):
            rows[pivot] = reduced if reduced[0] >> pivot else neg(reduced)
        else:
            basis.append((reduced[0] & low, reduced[1] & low))
    return basis


def coordinates(coefficients, indices):
    p = n = 0
    for key, a in coefficients.items():
        if a % 3 == 1:
            p |= 1 << indices[key]
        if a % 3 == 2:
            n |= 1 << indices[key]
    return p, n


def recover(pencil):
    """Input pencil[row][column] is a coefficient list in the contraction variables."""
    d = len(pencil[0][0])
    mons = [list(combinations_with_replacement(range(d), k)) for k in range(7)]
    index = [{m: i for i, m in enumerate(level)} for level in mons]
    forms = [[[(i, a % 3) for i, a in enumerate(col) if a % 3] for col in row]
             for row in pencil]
    ideal = {}
    for rr in combinations(range(len(forms)), 3):
        for cc in combinations(range(len(forms[0])), 3):
            minor = Counter()
            for perm in permutations(range(3)):
                s = (-1) ** sum(perm[i] > perm[j] for i, j in combinations(range(3), 2))
                a, b, c = [forms[r][cc[j]] for r, j in zip(rr, perm)]
                for i, x in a:
                    for j, y in b:
                        for k, z in c:
                            minor[tuple(sorted((i, j, k)))] += s * x * y * z
            insert(ideal, coordinates(minor, index[3]))
    for k in range(3, 6):
        following = {}
        for var in range(d):
            shifts = [index[k+1][tuple(sorted(m + (var,)))] for m in mons[k]]
            for row in ideal.values():
                v = [0, 0]
                for i, s in terms(row):
                    v[s < 0] |= 1 << shifts[i]
                insert(following, tuple(v))
        ideal = following
    cubes = [remainder(unit(index[6][tuple(sorted(m * 3))]), ideal) for m in mons[2]]
    quadrics = kernel(cubes, len(mons[6]))
    if len(quadrics) != d*(d-1)//2:
        return None
    qrows = {}
    for q in quadrics:
        insert(qrows, q)

    # Stack the derivations of all the quadrics, reduced modulo their span.
    columns = []
    for a in range(d):
        for b in range(d):
            pos = minus = 0
            for q in quadrics:
                f = Counter()
                for ix, s in terms(q):
                    i, j = mons[2][ix]
                    if i == a:
                        f[tuple(sorted((j, b)))] += s
                    if j == a:
                        f[tuple(sorted((i, b)))] += s
                p, n = remainder(coordinates(f, index[2]), qrows)
                pos = (pos << len(mons[2])) | p
                minus = (minus << len(mons[2])) | n
            columns.append((pos, minus))
    derivations = kernel(columns, len(mons[2])*len(quadrics))
    if len(derivations) != d:
        return None
    spaces = [[unit(i) for i in range(d)]]
    for mat in derivations:
        cols = [[0, 0] for _ in range(d)]
        for i, s in terms(mat):
            cols[i % d][s < 0] |= 1 << (i // d)
        pieces = []
        for basis in spaces:
            images = [combine(v, cols) for v in basis]
            for sign in (0, 1, -1):
                shifted = [add(w, ZERO if not sign else neg(v) if sign == 1 else v)
                           for w, v in zip(images, basis)]
                eig = [combine(c, basis) for c in kernel(shifted, d)]
                if eig:
                    pieces.append(eig)
        spaces = pieces
    if len(spaces) != d or any(len(s) != 1 for s in spaces):
        return None
    return [tuple(dict(terms(s[0])).get(i, 0) % 3 for i in range(d)) for s in spaces]
