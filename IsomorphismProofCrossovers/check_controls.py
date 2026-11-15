"""Exact finite controls for selected identities in the four informal proofs."""

from fractions import Fraction
from itertools import permutations, product
from math import gcd


def matmul(left, right, p):
    return [
        [sum(a * b for a, b in zip(row, col)) % p for col in zip(*right)]
        for row in left
    ]


def check_inversion():
    # Axioms x², xy−1, with Bezout multipliers y², −(xy+1).
    # Add a high-degree syzygy without changing the Bezout identity.
    checks = 0
    for p in (2, 3, 5, 7):
        for x, y in product(range(p), repeat=2):
            f1, f2 = x * x % p, (x * y - 1) % p
            s = pow(x + y, 9, p)
            g1, g2 = (y * y + s * f2) % p, (-(x * y + 1) - s * f1) % p
            assert (f1 * g1 + f2 * g2) % p == 1
            a = [[1, 0, 0], [-g1, 1, 0], [-g2, 0, 1]]
            b = [[1, f1, f2], [g1, 1 + g1 * f1, g1 * f2], [g2, g2 * f1, 1 + g2 * f2]]
            assert matmul(a, b, p) == [[1, f1, f2], [0, 1, 0], [0, 0, 1]]
            assert matmul(b, a, p)[0][0] == 0
            checks += 1
    return checks


def check_coefficient_orbits():
    # Coefficients A=C2×C4; scalar codes for the two target types.
    a = list(product(range(2), range(4)))
    types = (2, 4)
    rows = {
        d: [(r, s) for r, s in product(range(d), repeat=2) if 2 * r % d == 0 and 4 * s % d == 0]
        for d in types
    }
    endos = list(product(*(rows[d] for d in types)))

    def apply(f, point):
        return tuple(sum(x * y for x, y in zip(row, point)) % d for d, row in zip(types, f))

    autos = [f for f in endos if len({apply(f, point) for point in a}) == len(a)]

    def code(d, source):
        return frozenset(tuple(sum(x * y for x, y in zip(row, pt)) % d for pt in source) for row in rows[d])

    def edges(d, words):
        return frozenset(
            frozenset((i, bit) for i, val in enumerate(w) for bit in range(d.bit_length() - 1) if val >> bit & 1)
            for w in words
        )

    checks = 0
    for source in product(a, repeat=3):
        for perm in permutations(range(3)):
            twisted = tuple(source[i] for i in perm)
            pos = {old: new for new, old in enumerate(perm)}
            orbit = {tuple(apply(f, pt) for pt in twisted) for f in autos}
            transported = {
                d: frozenset(frozenset((pos[i], bit) for i, bit in edge) for edge in edges(d, code(d, source)))
                for d in types
            }
            for f in endos:
                target = tuple(apply(f, pt) for pt in twisted)
                accepted = all(transported[d] == edges(d, code(d, target)) for d in types)
                assert accepted == (target in orbit)
                checks += 1
    return checks


def check_quartic_weights():
    for n in range(3, 81):
        x1 = 2 ** (n - 1)
        x = [0] + [x1 * (Fraction(2, 3) + Fraction(1, 3) * Fraction(-1, 2) ** (j - 1)) for j in range(1, n)]
        x[0] = x1 - x[-1] / 2
        assert all(xi.denominator == 1 and xi > 0 for xi in x)
        assert gcd(*map(int, x)) == 1 and x[0] % 2 == 1
        assert sum(x) == ((3 * n + 1) * 2**n - (-1)**n) // 9
        weight_sum = [0] * n
        for i, xi in enumerate(x):
            weight_sum[i] += 2 * xi
            weight_sum[(i + 1) % n] -= xi
            weight_sum[(i + 2) % n if i else 1] -= xi
        assert weight_sum == [0] * n
    return 78


if __name__ == '__main__':
    print(f'PASS inversion fixtures: {check_inversion()}')
    print(f'PASS mixed-exponent coefficient comparisons: {check_coefficient_orbits()}')
    print(f'PASS quartic weight recurrences: {check_quartic_weights()}')
