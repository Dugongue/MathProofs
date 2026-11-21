"""Finite controls for the fixed-dihedral epimorphism construction."""
from collections import Counter
from itertools import product


def multiply(g, h, order):
    a, b = g
    c, d = h
    return ((a + (-1 if b else 1) * c) % order, b ^ d)


def inverse(g, order):
    a, b = g
    return ((a if b else -a) % order, b)


def commutator(g, h, order):
    value = multiply(g, h, order)
    value = multiply(value, inverse(g, order), order)
    return multiply(value, inverse(h, order), order)


def quotient_determinant(g, h):
    a, b = g
    c, d = h
    return ((a * d) ^ (b * c)) & 1


def commuting_half(involutions, width, order):
    for half in product(involutions, repeat=width):
        if all(commutator(g, h, order) == (0, 0) for g in half for h in half):
            if any((a & 1, b) != (0, 0) for a, b in half):
                yield half


def verify_controls():
    pair_checks = 0
    for order in (4, 8, 16, 32):
        elements = tuple(product(range(order), range(2)))
        for g, h in product(elements, repeat=2):
            t, b = commutator(g, h, order)
            assert b == 0 and t % 2 == 0
            assert (t * (order // 4)) % order == (order // 2) * quotient_determinant(g, h)
            pair_checks += 1

    accepted = {}
    involutions = [(a, b) for a, b in product(range(4), range(2))
                   if multiply((a, b), (a, b), 4) == (0, 0)]
    for width in (1, 2, 3):
        counts = Counter()
        halves = list(commuting_half(involutions, width, 4))
        for a, b in product(halves, repeat=2):
            matrix = tuple(tuple(quotient_determinant(g, h) for h in b) for g in a)
            if not any(map(any, matrix)):
                continue
            if any(matrix[i][j] != matrix[j][i] for i in range(width) for j in range(width)):
                continue
            if any(matrix[i][i] != matrix[0][i] for i in range(1, width)):
                continue
            assert matrix[0][0] == 1
            x = matrix[0]
            assert matrix == tuple(tuple(i * j for j in x) for i in x)
            counts[x] += 1
        expected = {(1, *x): 2 ** (2 * width + 1) for x in product(range(2), repeat=width - 1)}
        assert counts == expected
        accepted[width] = sum(counts.values())
    print("Pairs checked:", pair_checks)
    print("Normalised onto assignments by rank-one matrix width:", accepted)


if __name__ == "__main__":
    verify_controls()
