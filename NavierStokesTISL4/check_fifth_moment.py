"""Exact controls for the fifth-correlation sign test."""

from collections import Counter
from itertools import product
from random import Random


ROWS = [(1, 0, 0, 2, 2), (1, 2, 1, 1, 0), (1, 2, 1, 0, 1),
        (1, 1, 0, 2, 0), (1, 2, 1, 1, 1), (1, 1, 1, 0, 1),
        (1, 0, 1, 2, 0), (1, 0, 2, 0, 1)]
EXPONENTS = (2, 2, 2, 2, 1, 2, 2, 1)
COUNTS = {-9: 4, -6: 14, -3: 68, 0: 75, 3: 58, 6: 22, 9: 2}
CHARACTER = (0, 1, -1)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True)) % 3


def pfaffian_function(point):
    value = 1
    for row, e in zip(ROWS, EXPONENTS, strict=True):
        value *= CHARACTER[dot(row, point)] ** e
    return value


def direct_moment():
    points = list(product(range(3), repeat=5))
    values = [pfaffian_function(x) for x in points]
    assert sum(values) == 0
    freq = Counter()
    for a in points:
        doubled = sum(value * (2 if dot(a, x) == 0 else -1)
                      for x, value in zip(points, values, strict=True))
        assert doubled % 2 == 0
        freq[doubled // 2] += 1
    assert freq == COUNTS
    assert sum(value ** 3 * count for value, count in freq.items()) == 0
    fifth = sum(value ** 5 * count for value, count in freq.items())
    assert fifth % len(points) == 0
    return fifth // len(points)


def multiply(a, b, c, d):
    return a * c - b * d, a * d + b * c - b * d


def projected_moment():
    relation = [
        l for l in product(range(3), repeat=len(ROWS))
        if all(not dot(l, col) for col in zip(*ROWS, strict=True))
    ]
    assert len(relation) == 27
    small = list(product(range(3), repeat=4))
    phase = [(1, 0), (0, 1), (-1, -1)]
    tables = {}
    for e in [1, 2]:
        table = {}
        weighted = [(x, 0 if 0 in x or sum(x) % 3 == 0 else
                     (CHARACTER[x[0]] * CHARACTER[x[1]] * CHARACTER[x[2]] *
                      CHARACTER[x[3]] * CHARACTER[sum(x) % 3]) ** e)
                    for x in small]
        for a in small:
            real = imag = 0
            for x, multiplicity in weighted:
                c, d = phase[dot(a, x)]
                real += c * multiplicity
                imag += d * multiplicity
            table[a] = (real, imag)
        tables[e] = table
    total_real = total_imag = 0
    select = [tables[e] for e in EXPONENTS]
    for r1, r2, r3, r4 in product(relation, repeat=4):
        a, b = 1, 0
        for i, k in enumerate(zip(r1, r2, r3, r4, strict=True)):
            c, d = select[i][k]
            if c == d == 0:
                a = b = 0
                break
            a, b = multiply(a, b, c, d)
        total_real += a
        total_imag += b
    scale = len(relation) ** 4
    assert total_imag == 0 and total_real % scale == 0
    return total_real // scale


def pfaffian_alt(matrix):
    rows = [[value % 3 for value in row] for row in matrix]
    size = len(rows)
    value = 1
    for i in range(0, size, 2):
        j = next((j for j in range(i + 1, size) if rows[i][j]), None)
        if j is None:
            return 0
        if j != i + 1:
            rows[i + 1], rows[j] = rows[j], rows[i + 1]
            for row in rows:
                row[i + 1], row[j] = row[j], row[i + 1]
            value = -value
        force = rows[i][i + 1]
        value = value * force % 3
        for k in range(i + 2, size):
            for l in range(k + 1, size):
                rows[k][l] = (rows[k][l] - force *
                              (rows[i][k] * rows[i + 1][l] -
                               rows[i][l] * rows[i + 1][k])) % 3
                rows[l][k] = -rows[k][l] % 3
    return value % 3


def pencil(rows, x, w, b, c):
    size = len(rows)
    entries = [[0] * (2 * size) for _ in range(2 * size)]

    def alt(i, j, value):
        entries[i][j], entries[j][i] = value % 3, -value % 3

    for i in range(size):
        alt(i, size + i, dot(rows[i], x))
    for i in range(size - 1):
        alt(i, size + i + 1, w)
    alt(size, size + 1, b)
    alt(size - 2, size - 1, c)
    return entries


def commutant_dimension(matrices):
    n = len(matrices[0])
    basis = {}
    for a in matrices:
        sparse_rows = [[(k, x) for k, x in enumerate(row) if x] for row in a]
        sparse_cols = [[(k, x) for k, x in enumerate(col) if x]
                       for col in zip(*a, strict=True)]
        for i, left in enumerate(sparse_rows):
            for j, right in enumerate(sparse_cols):
                row = {i * n + k: value for k, value in right}
                for k, value in left:
                    key = k * n + j
                    entry = (row.get(key, 0) - value) % 3
                    if entry:
                        row[key] = entry
                    else:
                        row.pop(key, None)
                while row:
                    pivot = min(row)
                    factor = row[pivot]
                    old = basis.get(pivot)
                    if old is None:
                        basis[pivot] = {k: v * factor % 3 for k, v in row.items()}
                        break
                    for k, v in old.items():
                        entry = (row.get(k, 0) - factor * v) % 3
                        if entry:
                            row[k] = entry
                        else:
                            row.pop(k, None)
    return n * n - len(basis)


def check_pencil(k):
    rank_labels = 5 + k
    padded = [r + (0,) * k for r in ROWS]
    ordered = [padded[4]]
    for i, row in enumerate(padded):
        if i not in (4, 7):
            ordered.extend([row, row])
    for j in range(5, 5 + k):
        row = tuple(int(i == j) for i in range(rank_labels))
        ordered.extend([row, row])
    ordered.append(padded[7])
    n = len(ordered)
    assert n == 14 + 2 * k
    good = next(x for x in product(range(3), repeat=5) if pfaffian_function(x))
    diag = [dot(row, good + (1,) * k) for row in ordered]
    assert all(diag)
    mats = []
    for j in range(rank_labels + 3):
        labels = [int(i == j) for i in range(rank_labels + 3)]
        m = pencil(ordered, labels[:rank_labels], *labels[-3:])
        mats.append([[(-diag[i] * x) % 3 for x in m[n+i]] for i in range(n)] +
                    [[(diag[i] * x) % 3 for x in m[i]] for i in range(n)])
    assert commutant_dimension(mats) == 1
    rand = Random(1120 + k)
    for _ in range(28):
        labels = [rand.randrange(3) for _ in range(rank_labels + 3)]
        x = labels[:rank_labels]
        m = pencil(ordered, x, *labels[-3:])
        expected = (-1) ** (n * (n - 1) // 2)
        for row in ordered:
            expected = expected * dot(row, x) % 3
        assert pfaffian_alt(m) == expected
        invert_aux = pencil(ordered, x, *((-a) % 3 for a in labels[-3:]))
        weights = [(-1) ** i % 3 for i in range(n)] * 2
        assert [[weights[i] * z * weights[j] % 3 for j, z in enumerate(row)]
                for i, row in enumerate(m)] == invert_aux
    return (2 * n, 2 * n, rank_labels + 3)


if __name__ == "__main__":
    assert __debug__
    a, b = direct_moment(), projected_moment()
    assert a == b == -240
    print(f"Zero mean. Fifth correlation {a} by direct and projected computations.")
    print([check_pencil(k) for k in (0, 2, 4)])
