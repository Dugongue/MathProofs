"""Exact finite controls for the norm-to-algebra construction."""

from itertools import combinations, product
from random import Random


def det(matrix, p):
    rows = [list(row) for row in matrix]
    determinant = 1
    for j in range(len(rows)):
        pivot = next((i for i in range(j, len(rows)) if rows[i][j] % p), None)
        if pivot is None:
            return 0
        if j != pivot:
            rows[j], rows[pivot] = rows[pivot], rows[j]
            determinant = -determinant
        value = rows[j][j] % p
        determinant = determinant * value % p
        for i in range(j + 1, len(rows)):
            scale = rows[i][j] * pow(value, -1, p) % p
            rows[i] = [(a - scale*b) % p for a, b in zip(rows[i], rows[j])]
    return determinant % p


def multiplication(element):
    matrix = [[0]*4 for _ in range(4)]
    for i, j in product(range(4), repeat=2):
        multiplier = 1
        if i & j & 1:
            multiplier *= -3
        if i & j & 2:
            multiplier *= 13
        matrix[i ^ j][j] += element[i] * multiplier
    return matrix


MASKS = tuple(sorted(range(1, 16), key=lambda m: (m.bit_count(), m)))
INDEX = {m: 3 + i for i, m in enumerate(MASKS)}
J = multiplication((0, 1, 1, 0))


def basis_product(i, j, c):
    if i == 0:
        return {j: 1}
    if j == 0:
        return {i: 1 + i if i < 3 else 3 + MASKS[i - 3].bit_count()}
    if i == j and i in (1, 2):
        return {i: 1}
    if (i, j) == (1, 2):
        return {INDEX[15]: c}
    if i == 1 and j >= 3 and MASKS[j - 3].bit_count() == 1:
        index = MASKS[j - 3].bit_length() - 1
        return {INDEX[1 << k]: J[k][index] for k in range(4)}
    if i < 3 or j < 3:
        return {}
    a, b = MASKS[i - 3], MASKS[j - 3]
    if a & b:
        return {}
    inversions = sum((a >> r) & (b >> s) & 1 for r in range(4) for s in range(r))
    return {INDEX[a | b]: (-1)**inversions}


def exterior_lift(g, p):
    columns = [{i: 1} for i in range(3)]
    for a in MASKS:
        col = [i for i in range(4) if a >> i & 1]
        values = {}
        for row in combinations(range(4), len(col)):
            minor = [[g[i][j] for j in col] for i in row]
            values[INDEX[sum(1 << i for i in row)]] = det(minor, p)
        columns.append(values)
    return columns


def audit_prime(p, rng):
    for _ in range(1024):
        element = [rng.randrange(p) for _ in range(4)]
        g = multiplication(element)
        if det(g, p) == 3:
            break
    else:
        raise AssertionError('No norm witness in the control budget')
    images = exterior_lift(g, p)
    for i, j in product(range(18), repeat=2):
        left, right = [0]*18, [0]*18
        for k, coefficient in basis_product(i, j, 1).items():
            for l, value in images[k].items():
                left[l] += coefficient * value
        for a, va in images[i].items():
            for b, vb in images[j].items():
                for l, value in basis_product(a, b, 3).items():
                    right[l] += va * vb * value
        assert all((a - b) % p == 0 for a, b in zip(left, right))


def main():
    rng = Random(20261115)
    for p in (11, 17, 19, 23, 29):
        audit_prime(p, rng)
    print('PASS: norm witnesses lift to D_1 -> D_3 on all 324 basis products in each of five fields')


if __name__ == '__main__':
    main()
