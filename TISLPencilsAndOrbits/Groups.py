"""Finite controls for scalar determinant characters and three-slice invariants."""

from itertools import combinations, permutations, product
from math import factorial, gcd, lcm


def determinant(rows, p):
    rows = [list(row) for row in rows]
    answer = 1
    for j in range(len(rows)):
        pivot = next((i for i in range(j, len(rows)) if rows[i][j] % p), None)
        if pivot is None:
            return 0
        if pivot != j:
            rows[j], rows[pivot] = rows[pivot], rows[j]
            answer = -answer
        value = rows[j][j] % p
        inverse = pow(value, -1, p)
        answer = answer * value % p
        for i in range(j + 1, len(rows)):
            multiplier = rows[i][j] * inverse % p
            if multiplier:
                for k in range(j + 1, len(rows)):
                    rows[i][k] = (rows[i][k] - multiplier * rows[j][k]) % p
                rows[i][j] = 0
    return answer % p


def check_scalar_lattice():
    checked = 0
    for p in (3, 5, 7):
        units = range(1, p)
        for a, b, c in product(range(2, 6), repeat=3):
            length = lcm(a, b, c)
            image = {(pow(lam, a, p), pow(mu, b, p), pow(lam * mu, -c, p))
                     for lam, mu in product(units, repeat=2)}
            kernel = {(x, y, z) for x, y, z in product(units, repeat=3)
                      if pow(x, length // a, p) * pow(y, length // b, p)
                      * pow(z, length // c, p) % p == 1}
            first = gcd(a, b, c)
            second = gcd(a * b, a * c, b * c) // first
            assert image <= kernel
            assert len(kernel) == len(image) * gcd(first, p - 1) * gcd(second, p - 1)
            checked += 1
    return checked


def koszul_det(slices, p):
    a, b, c = slices
    n = len(a)
    rows = []
    for source in range(3):
        for i in range(n):
            blocks = ((None, c, b), (c, None, a), (b, a, None))[source]
            signs = ((0, -1, 1), (1, 0, -1), (-1, 1, 0))[source]
            rows.append(tuple(sign * block[i][j] if block is not None else 0
                              for block, sign in zip(blocks, signs) for j in range(n)))
    return determinant(rows, p)


def check_weyl(n, p):
    root = next(z for z in range(2, p) if pow(z, n, p) == 1
                and all(pow(z, e, p) != 1 for e in range(1, n)))
    identity = [[int(i == j) for j in range(n)] for i in range(n)]
    diagonal = [[pow(root, i, p) if i == j else 0 for j in range(n)] for i in range(n)]
    shift = [[int(i == (j + 1) % n) for j in range(n)] for i in range(n)]
    mixed = [[pow(root, -i, p) * shift[i][j] % p for j in range(n)] for i in range(n)]

    def pencil(t):
        return [[[a[i][j] + t * mixed[i][j] for j in range(n)] for i in range(n)]
                for a in (identity, diagonal, shift)]

    assert koszul_det(pencil(0), p) != 0
    parameter = next(t for t in range(1, p) if koszul_det(pencil(t), p) != 0)
    slices = pencil(parameter)
    for x, y, z in product(range(p), repeat=3):
        evaluated = [[sum(e * a[i][j] for e, a in zip((x, y, z), slices)) for j in range(n)]
                     for i in range(n)]
        expected = (x ** n + (-1) ** (n - 1) * (y ** n + z ** n)
                    + (parameter * (x + y + z)) ** n) % p
        assert determinant(evaluated, p) == expected
    return p ** 3, parameter


def bracket_terms(face):
    for perm in permutations(range(3)):
        sign = (-1) ** sum(perm[i] > perm[j] for i in range(3) for j in range(i + 1, 3))
        exponent = [0] * 12
        for point, axis in zip(face, perm):
            exponent[3 * point + axis] = 1
        yield tuple(exponent), sign


def check_tetrahedron(n, p, t):
    points = ((1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1))
    weights = (1, (-1) ** (n - 1), (-1) ** (n - 1), pow(t, n, p))
    brackets = tuple(combinations(range(4), 3))
    coefficients = {(0,) * 12: 1}
    for face in brackets:
        for _ in range(n // 3):
            new_coefficients = {}
            for exponent, scalar in coefficients.items():
                for beta, sign in bracket_terms(face):
                    key = tuple(a + b for a, b in zip(exponent, beta))
                    new_coefficients[key] = (new_coefficients.get(key, 0) + sign * scalar) % p
            coefficients = {key: value for key, value in new_coefficients.items() if value}

    def apolar(exponent):
        return sum(weight * pow(point[0], exponent[0], p)
                   * pow(point[1], exponent[1], p) * pow(point[2], exponent[2], p)
                   for point, weight in zip(points, weights)) % p

    actual = 0
    for exponent, coefficient in coefficients.items():
        term = coefficient
        for j in range(0, 12, 3):
            term = term * apolar(exponent[j:j + 3]) % p
        actual = (actual + term) % p
    expected = factorial(4)
    for weight in weights:
        expected *= weight
    for face in brackets:
        expected *= pow(determinant([points[i] for i in face], p), n // 3, p)
    assert actual == expected % p and actual
    return len(coefficients), actual


if __name__ == "__main__":
    print("Scalar lattices checked:", check_scalar_lattice())
    for n, p in ((3, 7), (6, 13)):
        evaluations, parameter = check_weyl(n, p)
        print("Weyl determinant grid and joint-locus parameter:", n, evaluations, parameter)
        print("Expanded tetrahedral terms and value:", check_tetrahedron(n, p, parameter))
