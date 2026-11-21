"""Exact finite controls for the pencil slice-correction characters."""

from itertools import product
from math import comb


def matrix_product(left, right, p):
    return [
        [sum(a * b for a, b in zip(row, col)) % p for col in zip(*right)]
        for row in left
    ]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def determinant(matrix, p):
    work = [row[:] for row in matrix]
    det = 1
    for i in range(len(work)):
        pivot = next((j for j in range(i, len(work)) if work[j][i]), None)
        if pivot is None:
            return 0
        if i != pivot:
            work[i], work[pivot] = work[pivot], work[i]
            det = -det
        det = det * work[i][i] % p
        inverse = pow(work[i][i], -1, p)
        for j in range(i + 1, len(work)):
            factor = work[j][i] * inverse
            work[j] = [(a - factor * b) % p for a, b in zip(work[j], work[i])]
    return det


def inverse(matrix, p):
    n = len(matrix)
    work = [a + b for a, b in zip(matrix, identity(n))]
    for i in range(n):
        pivot = next(j for j in range(i, n) if work[j][i])
        work[pivot], work[i] = work[i], work[pivot]
        unit = pow(work[i][i], -1, p)
        work[i] = [v * unit % p for v in work[i]]
        for j in range(n):
            if j != i:
                factor = work[j][i]
                work[j] = [(a - factor * b) % p for a, b in zip(work[j], work[i])]
    return [row[n:] for row in work]


def jordan_control():
    p = 5
    number = 0
    for j in (1, 2, 3):
        J = [[int(k == i + 1) for k in range(j)] for i in range(j)]
        for a, d, b in product(range(1, p), range(1, p), range(p)):
            A = [[(a * (i == k) + b * J[i][k]) % p for k in range(j)] for i in range(j)]
            B = [[d * v % p for v in row] for row in J]
            ai = inverse(A, p)
            h = matrix_product(ai, B, p)
            column = [[int(i == j - 1)] for i in range(j)]
            columns = []
            for _ in range(j):
                columns.append([row[0] for row in column])
                column = matrix_product(h, column, p)
            T = [list(row) for row in zip(*reversed(columns))]
            L = matrix_product(inverse(T, p), ai, p)
            assert matrix_product(matrix_product(L, A, p), T, p) == identity(j)
            assert matrix_product(matrix_product(L, B, p), T, p) == J
            weight = j * (j - 1) // 2
            c = d * pow(a, -1, p) % p
            assert determinant(T, p) == pow(c, weight, p)
            assert determinant(L, p) == pow(a, -j, p) * pow(c, -weight, p) % p
            number += 1
    print(f"{number} rational Jordan-block corrections verified")


def symmetric_power(matrix, k, p):
    (a, b), (c, d) = matrix
    # Column i expands (a*x+c*y)^(k-i) * (b*x+d*y)^i.
    out = [[0] * (k + 1) for _ in range(k + 1)]
    for i in range(k + 1):
        for s, t in product(range(k - i + 1), range(i + 1)):
            coeff = comb(k - i, s) * a ** (k - i - s) * c**s
            coeff *= comb(i, t) * b ** (i - t) * d**t
            out[s + t][i] = (out[s + t][i] + coeff) % p
    return out


def multiplication_slice(k, x, y):
    return [
        [x if i == j else y if i == j + 1 else 0 for j in range(k)]
        for i in range(k + 1)
    ]


def singular_control():
    p = 3
    number = 0
    for a, b, c, d in product(range(p), repeat=4):
        matrix = [[a, b], [c, d]]
        delta = determinant(matrix, p)
        if not delta:
            continue
        for k in (1, 2, 3):
            large = symmetric_power(matrix, k, p)
            small = symmetric_power(matrix, k - 1, p)
            left = inverse(large, p)
            for (x, y), (u, v) in [((1, 0), (a, c)), ((0, 1), (b, d))]:
                restored = matrix_product(left, multiplication_slice(k, u, v), p)
                restored = matrix_product(restored, small, p)
                assert restored == multiplication_slice(k, x, y)
            assert determinant(left, p) == pow(delta, -k * (k + 1) // 2, p)
            assert determinant(small, p) == pow(delta, k * (k - 1) // 2, p)
            number += 1
    print(f"{number} singular-block symmetric-power corrections verified")


def quadratic_product(x, y):
    a, b = x
    c, d = y
    return ((a * c - b * d) % 3, (a * d + b * c) % 3)


def quadratic_power(x, exponent):
    if exponent < 0:
        exponent %= 8
    out = (1, 0)
    for _ in range(exponent):
        out = quadratic_product(out, x)
    return out


def quadratic_control():
    norms = set()
    cases = 0
    for a in product(range(3), repeat=2):
        if a == (0, 0):
            continue
        d = quadratic_power(a, 3)
        norm = quadratic_product(a, d)
        norms.add(norm)
        for j in (1, 2, 3, 4):
            ratio = quadratic_product(d, quadratic_power(a, -1))
            inverse_ratio = quadratic_power(ratio, -1)
            weight = j * (j - 1) // 2
            left1 = quadratic_product(quadratic_power(a, -j), quadratic_power(ratio, -weight))
            left2 = quadratic_product(quadratic_power(d, -j), quadratic_power(inverse_ratio, -weight))
            assert quadratic_power(left1, 3) == left2
            assert quadratic_product(left1, left2) == quadratic_power(norm, -j)
            right1 = quadratic_power(ratio, weight)
            right2 = quadratic_power(inverse_ratio, weight)
            assert quadratic_power(right1, 3) == right2
            assert quadratic_product(right1, right2) == (1, 0)
            cases += 1
    assert norms == {(1, 0), (2, 0)}
    print(f"{cases} quadratic conjugate-block norm products verified")


if __name__ == "__main__":
    jordan_control()
    singular_control()
    quadratic_control()

