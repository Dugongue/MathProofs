"""Exact checks for the slice gauge and common power laws on small carriers."""

from itertools import permutations
from random import Random


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return list(map(list, zip(*a)))


def matmul(a, b, modulus):
    return [[sum(u * v for u, v in zip(row, col)) % modulus
             for col in zip(*b)] for row in a]


def det(a):
    """Integer Bareiss determinant before reduction."""
    a = [row[:] for row in a]
    sign, previous = 1, 1
    for k in range(len(a) - 1):
        i = next((i for i in range(k, len(a)) if a[i][k]), None)
        if i is None:
            return 0
        if i != k:
            a[i], a[k] = a[k], a[i]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, len(a)):
            for j in range(k + 1, len(a)):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def carrier(p, exponent, active):
    dim = 4
    n = 2 * dim + 2
    q_rank = 0 if exponent == 1 or n % p else 1 if p == 2 else 2
    n += q_rank
    top = n - 1
    pairs = {(i, dim + i) for i in range(1, dim + 1)}
    pairs.add((0, top))
    if q_rank == 1:
        pairs.add((top - 1, top - 1))
    if q_rank == 2:
        pairs.add((top - 2, top - 1))
    gram = [[int((min(i, j), max(i, j)) in pairs) for j in range(n)]
            for i in range(n)]
    form = {}
    for i, j in pairs:
        for order in set(permutations((0, i, j))):
            form[order] = 1
    if active:
        s = p ** (exponent - 1)
        for triple in ((1, 2, 3), (2, 3, 4)):
            for order in permutations(triple):
                form[order] = s
    return form, gram, dim


def contract(form, x, modulus):
    b = [[0] * len(x) for _ in x]
    for (i, j, k), coefficient in form.items():
        b[j][k] = (b[j][k] + coefficient * x[i]) % modulus
    return b


def congruence(b, transform, modulus):
    return matmul(transpose(transform), matmul(b, transform, modulus), modulus)


def gauge(b, r, dim, modulus):
    n = len(b)
    r_inverse = pow(r, -1, modulus)
    shear = eye(n)
    for i in range(1, dim + 1):
        for j in range(i + 1, dim + 1):
            shear[dim + i][j] = -r_inverse * b[i][j] % modulus
    intermediate = congruence(b, shear, modulus)
    clear = eye(n)
    for j in range(1, n - 1):
        clear[-1][j] = -r_inverse * intermediate[0][j] % modulus
    return matmul(shear, clear, modulus)


def powers(form, gram, x, modulus, max_power=10):
    linear_map = matmul(gram, contract(form, x, modulus), modulus)
    current = [[int(i == 0)] for i in range(len(x))]
    result = []
    for _ in range(max_power + 1):
        result.append(tuple(row[0] for row in current))
        current = matmul(linear_map, current, modulus)
    return result


def check_block_determinant(form, gram, rng, modulus):
    n = len(gram)
    matrices = [[[rng.randrange(modulus) for _ in range(2)] for _ in range(2)]
                for _ in range(n)]
    block = [[0] * (2 * n) for _ in range(2 * n)]
    for i in range(n):
        basis = [int(i == j) for j in range(n)]
        operator = matmul(gram, contract(form, basis, modulus), modulus)
        for j in range(n):
            for k in range(n):
                for u in range(2):
                    for v in range(2):
                        block[2 * j + u][2 * k + v] += operator[j][k] * matrices[i][u][v]
    assert det(block) % modulus == pow(det(matrices[0]), n, modulus)


def main():
    rng = Random(1121)
    gauges = determinants = powers_checked = 0
    for p, exponent in ((2, 1), (2, 3), (3, 1), (3, 2), (5, 1), (5, 2)):
        modulus = p**exponent
        s = p ** (exponent - 1)
        f0, g, dim = carrier(p, exponent, False)
        f1, _, _ = carrier(p, exponent, True)
        n = len(g)
        for _ in range(8):
            x = [rng.randrange(modulus) for _ in range(n)]
            a = x[-1]
            for form in (f0, f1):
                b = contract(form, x, modulus)
                assert det(b) % modulus == det(g) * pow(x[0], n, modulus) % modulus
                check_block_determinant(form, g, rng, modulus)
                determinants += 2
            first, second = (powers(f, g, x, modulus) for f in (f0, f1))
            if p in (2, 3):
                for d, (left, right) in enumerate(zip(first, second)):
                    assert left[-1] == right[-1]
                    if p == 2 or d % 3 != 2:
                        assert left == right
                    powers_checked += 1
            x[0] = 1 + p * rng.randrange(s)
            r = x[0]
            expected = [[r * entry % modulus for entry in row] for row in g]
            expected[0][0] = a
            transforms = []
            for form in (f0, f1):
                b = contract(form, x, modulus)
                transform = gauge(b, r, dim, modulus)
                assert congruence(b, transform, modulus) == expected
                assert det(transform) % modulus == 1
                assert transform[0][0] == transform[-1][-1] == 1
                assert all(transform[j][0] == transform[j][-1] == 0
                           for j in range(1, n - 1))
                transforms.append(transform)
                gauges += 1
            assert all((u - v) % s == 0 for row0, row1 in zip(*transforms)
                       for u, v in zip(row0, row1))
    print(f"{gauges} exact gauges, {determinants} determinant checks, "
          f"{powers_checked} power-law checks")


if __name__ == "__main__":
    main()
