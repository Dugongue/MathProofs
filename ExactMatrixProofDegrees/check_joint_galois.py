"""Finite controls for the Galois-field joint-prime formulas."""

from fractions import Fraction
from itertools import permutations, product


def parity(x):
    return x.bit_count() & 1


def perpendicular(plane):
    return {x for x in range(16) if all(parity(x & w) == 0 for w in plane)}


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def rank(matrix):
    rows = [list(map(Fraction, row)) for row in matrix]
    h = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(h, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[pivot], rows[h] = rows[h], rows[pivot]
        div = rows[h][col]
        rows[h] = [x / div for x in rows[h]]
        for i in range(h + 1, len(rows)):
            c = rows[i][col]
            rows[i] = [x - c * y for x, y in zip(rows[i], rows[h])]
        h += 1
    return h


def check_quaternions():
    # Elements are signs times 1, i, j, k. The allowed quotients here
    # are the whole Q8, its three order-two quotients and the trivial quotient.
    q = set(range(8))
    kernels = [{0}, {0, 4, 1, 5}, {0, 4, 2, 6}, {0, 4, 3, 7}, q]
    signatures = [[int(x in h) for h in kernels] for x in sorted(q)]
    assert rank(signatures) == len(kernels)
    # Admitting the Klein-four quotient introduces the familiar one-prime trade.
    enlarged = kernels + [{0, 4}]
    assert rank([[int(x in h) for h in enlarged] for x in q]) == len(enlarged) - 1


def check_twenty_four():
    # The two rulings of rank-one 2 by 2 matrices over F_2. Rows are
    # encoded as two-bit masks; u v^T gives the four encoded entries.
    def outer(u, v):
        return sum((((u >> i) & 1) * ((v >> j) & 1)) << (2 * i + j)
                   for i in range(2) for j in range(2))

    planes = [{outer(u, v) for v in range(4)} for u in range(1, 4)]
    planes += [{outer(u, v) for u in range(4)} for v in range(1, 4)]
    assert len({frozenset(w) for w in planes}) == 6
    identity = (0, 1, 2)
    group = list(product(permutations(range(3)), range(16)))
    kernels = [{(identity, x) for x in perpendicular(w)} for w in planes]
    weights = [24] * 3 + [-24] * 3
    assert all(len(group) // len(h) == 24 for h in kernels)
    indexes = [[len(group) // len(h & k) for k in kernels] for h in kernels]
    signatures = [tuple(int(g in h) for h in kernels) for g in group]
    for j in range(3):
        expected = sum(Fraction(a * b, indexes[i][k] ** j)
                       for i, a in enumerate(weights) for k, b in enumerate(weights))
        observed = 0
        for rows in product(signatures, repeat=j):
            mask = [int(all(row[col] for row in rows)) for col in range(6)]
            observed += dot(weights, mask) ** 2
        assert expected == Fraction(observed, len(group) ** j)
        assert (expected > 0) == (j == 2)


if __name__ == "__main__":
    check_quaternions()
    check_twenty_four()
    print("Verified quaternion quotient signatures and 9,313 ordered group-tuple energies "
          "for degree-24 nonabelian factor groups.")
