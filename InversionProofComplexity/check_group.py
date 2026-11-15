"""Exact finite controls for the special-group construction."""

from itertools import product
from random import Random


def rank_mod(matrix, p):
    rows = [list(row) for row in matrix]
    h = 0
    for j in range(len(rows[0])):
        pivot = next((i for i in range(h, len(rows)) if rows[i][j] % p), None)
        if pivot is None:
            continue
        rows[h], rows[pivot] = rows[pivot], rows[h]
        scale = pow(rows[h][j] % p, -1, p)
        rows[h] = [(a * scale) % p for a in rows[h]]
        for i in range(h + 1, len(rows)):
            factor = rows[i][j] % p
            rows[i] = [(a - factor*b) % p for a, b in zip(rows[i], rows[h])]
        h += 1
    return h


def alternating(pair_counts, coefficients):
    d = 2 * sum(pair_counts)
    matrix = [[0] * d for _ in range(d)]
    t = 0
    for count, coefficient in zip(pair_counts, coefficients):
        for _ in range(count):
            matrix[t][t + 1] = coefficient
            matrix[t + 1][t] = -coefficient
            t += 2
    return matrix


def pfaffian4(matrix, block):
    a, b, c, d = block
    return (matrix[a][b]*matrix[c][d]
            - matrix[a][c]*matrix[b][d] + matrix[a][d]*matrix[b][c])


def local_spectral_controls(p):
    pair_counts = (1, 3, 2, 2)
    selectors = tuple(range(p))
    for coefficients in product(selectors, repeat=len(pair_counts)):
        matrix = alternating(pair_counts, coefficients)
        expected = 2 * sum(c for a, c in zip(coefficients, pair_counts) if a)
        assert rank_mod(matrix, p) == expected
        if 0 < expected <= 2:
            assert coefficients[0] and not any(coefficients[1:])
        starts = (0, 2, 8, 12)
        for j in range(len(starts)):
            a = starts[j]
            if pair_counts[j] >= 2:
                assert pfaffian4(matrix, (a, a+1, a+2, a+3)) == coefficients[j]**2
            for k in range(j):
                b = starts[k]
                assert pfaffian4(matrix, (b, b+1, a, a+1)) == coefficients[k]*coefficients[j]


def alternating_identities(p, rng):
    for _ in range(250):
        u = [rng.randrange(p) for _ in range(4)]
        v = [rng.randrange(p) for _ in range(4)]
        matrix = [[u[i]*v[j] - v[i]*u[j] for j in range(4)] for i in range(4)]
        assert pfaffian4(matrix, range(4)) % p == 0


def main():
    rng = Random(117)
    for p in (2, 3, 5):
        local_spectral_controls(p)
        alternating_identities(p, rng)
    print('PASS: 722 block coefficient tuples and 750 decomposable Pfaffian evaluations')


if __name__ == '__main__':
    main()
