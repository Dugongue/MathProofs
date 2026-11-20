"""Exact finite controls for rank multiplicity, descent and valuation-free probes.

Runs without third-party dependencies. The experiment uses F2, F4 and Z/4.
The dimension- and ring-uniform statements are proved in the companion note.
"""

from collections import Counter
from itertools import product
from random import Random


def mul(a, b):
    """Multiply in F4 = F2[u]/(u^2+u+1)."""
    x = 0
    while b:
        if b & 1:
            x ^= a
        b >>= 1
        a <<= 1
        if a & 4:
            a ^= 7
    return x


def inv(a):
    assert a
    return mul(a, a)


def rref(rows, n):
    rows = [list(row) for row in rows]
    k = 0
    for j in range(n):
        pivot = next((i for i in range(k, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[k], rows[pivot] = rows[pivot], rows[k]
        base = [mul(v, inv(rows[k][j])) for v in rows[k]]
        rows[k] = base
        for i, row in enumerate(rows):
            if i != k:
                a = row[j]
                rows[i] = [v ^ mul(a, w) for v, w in zip(row, base)]
        k += 1
    return tuple(tuple(row) for row in rows[:k])


def subspaces(q, n):
    points = list(product(range(q), repeat=n))
    discovered = {()}
    todo = [()]
    for basis in todo:
        for v in points:
            space = rref((*basis, v), n)
            if space not in discovered:
                discovered.add(space)
                todo.append(space)
    return todo


def dot(u, v):
    r = 0
    for a, b in zip(u, v):
        r ^= mul(a, b)
    return r


def apply(a, x):
    return tuple(dot(row, x) for row in a)


def rank_at(a, b, field):
    return max(len(rref([tuple(mul(x, u) ^ mul(y, v) for u, v in zip(row, line))
                         for row, line in zip(a, b)], 3))
               for x, y in product(field, repeat=2))


def max_shrunk(a, b, spaces):
    scores = {}
    for u in spaces:
        im = rref([apply(m, x) for x in u for m in (a, b)], 3)
        scores[u] = len(u) - len(im)
    delta = max(scores.values())
    top = rref([v for u, d in scores.items() if d == delta for v in u], 3)
    assert scores[top] == delta
    return delta, top


def random_matrix(rng):
    return tuple(tuple(rng.randrange(2) for _ in range(3)) for _ in range(3))


def check_fields():
    f2 = subspaces(2, 3)
    f4 = subspaces(4, 3)
    a = ((1, 0, 0), (0, 0, 0), (0, 0, 1))
    b = ((0, 0, 0), (0, 1, 0), (0, 0, 1))
    assert rank_at(a, b, range(2)) == 2
    assert rank_at(a, b, range(4)) == 3
    rng = Random(20261119)
    cases = [(a, b)] + [(random_matrix(rng), random_matrix(rng)) for _ in range(400)]
    for a, b in cases:
        r = rank_at(a, b, range(2))
        # The largest minor has degree at most three. F4 has more than three
        # points, so its largest evaluation rank equals the generic rank.
        rho = rank_at(a, b, range(4))
        assert rho <= 2 * r
        delta, top = max_shrunk(a, b, f2)
        assert (delta, top) == max_shrunk(a, b, f4)
        assert 3 - delta <= 2 * rho
    print(f"F2 to F4: checked {len(cases)} matrix spaces, including a strict finite-field rank gap")


def check_ring():
    q = 4
    points = list(product(range(q), repeat=3))
    matrices = [(1, 1, 2), (1, 2, 2), (2, 2, 2), (0, 1, 2)]
    pairs_tested = 0
    for diag in matrices:
        image = Counter(tuple(d * v % q for d, v in zip(diag, y)) for y in points)
        assert len(set(image.values())) == 1
        for u, v in product(image, repeat=2):
            span = {tuple((a * x + b * y) % q for x, y in zip(u, v))
                    for a, b in product(range(q), repeat=2)}
            annihilator_size = sum(
                all(sum(x * a for x, a in zip(w, z)) % q == 0 for z in (u, v))
                for w in points
            )
            assert annihilator_size * len(span) == len(points)
            pairs_tested += 1
    print(f"Z/4: checked {pairs_tested} probe image pairs with mixed Smith valuations")


if __name__ == "__main__":
    check_fields()
    check_ring()
