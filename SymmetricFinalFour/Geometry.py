"""Exact controls for the marker determinant and polynomial role projectors."""

from itertools import product
from random import Random

DIMS = (2, 2, 1)
N = sum(DIMS)
OWNERS = tuple(i for i, d in enumerate(DIMS) for _ in range(d))
OFFSETS = (0, 2, 4)


def combine(coefficients, matrices, p):
    return [[sum(a * matrix[i][j] for a, matrix in zip(coefficients, matrices)) % p
             for j in range(len(matrices[0]))] for i in range(len(matrices[0]))]


def multiply(left, right, p):
    return [[sum(a * b for a, b in zip(row, col)) % p
             for col in zip(*right)] for row in left]


def invert_and_det(matrix, p):
    n = len(matrix)
    rows = [list(row) + [int(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    determinant = 1
    for i in range(n):
        j = next((j for j in range(i, n) if rows[j][i] % p), None)
        if j is None:
            return None, 0
        if j != i:
            rows[j], rows[i] = rows[i], rows[j]
            determinant *= -1
        determinant = determinant * rows[i][i] % p
        inv = pow(rows[i][i] % p, -1, p)
        rows[i] = [x * inv % p for x in rows[i]]
        for j in range(n):
            if j != i:
                factor = rows[j][i]
                rows[j] = [(x - factor * y) % p for x, y in zip(rows[j], rows[i])]
    return [row[n:] for row in rows], determinant % p


def data_entry(i, j, k, weights):
    if len({OWNERS[i], OWNERS[j], OWNERS[k]}) != 3:
        return 0
    sorted_indices = {OWNERS[v]: v - OFFSETS[OWNERS[v]] for v in (i, j, k)}
    x, y = sorted_indices[0], sorted_indices[1]
    return weights[x] if x == y else 0


def slice_matrix(label, scalar, shift, weights, p):
    matrix = [[0] * (2 * N) for _ in range(2 * N)]
    for i in range(N):
        if OWNERS[i] == label:
            matrix[i][N + i] = matrix[N + i][i] = scalar
        for j in range(N):
            matrix[i][j] = sum(shift[k] * data_entry(i, j, k, weights)
                               for k in range(N)) % p
    return matrix


def check_marker_projectors():
    rng = Random(333)
    determinant_checks = projectors = recovered_entries = 0
    for p in (2, 3, 5):
        for weights in ((0, 0), (1, 0), (1, 1)):
            for _ in range(6):
                scales = [rng.randrange(1, p) for _ in DIMS]
                shifts = [[rng.randrange(p) for _ in range(N)] for _ in DIMS]
                matrices = [slice_matrix(i, scales[i], shifts[i], weights, p)
                            for i in range(3)]
                inverse, _ = invert_and_det(combine((1, 1, 1), matrices, p), p)
                assert inverse is not None
                recovered = []
                for i, matrix in enumerate(matrices):
                    a = multiply(inverse, matrix, p)
                    square = multiply(a, a, p)
                    cube = multiply(a, square, p)
                    role = combine((3, -2), (square, cube), p)
                    assert multiply(role, role, p) == role
                    for j, row in enumerate(role[:N]):
                        assert row == [int(j == k and OWNERS[j] == i) for k in range(2 * N)]
                    recovered.append(role[:N])
                    projectors += 1
                for i, j, k in product(range(N), repeat=3):
                    result = sum(recovered[0][x][i] * recovered[1][y][j] * recovered[2][z][k]
                                 * data_entry(x, y, z, weights)
                                 for x, y, z in product(range(N), repeat=3)) % p
                    expected = data_entry(i, j, k, weights) if (
                        OWNERS[i], OWNERS[j], OWNERS[k]) == (0, 1, 2) else 0
                    assert result == expected
                    recovered_entries += 1
                for alpha in product(range(p), repeat=3):
                    _, determinant = invert_and_det(combine(alpha, matrices, p), p)
                    expected = (-1) ** N
                    for value, scale, size in zip(alpha, scales, DIMS):
                        expected *= (value * scale) ** (2 * size)
                    assert determinant == expected % p
                    determinant_checks += 1
    return determinant_checks, projectors, recovered_entries


if __name__ == "__main__":
    print("Active block determinant, idempotent, and recovery checks:",
          check_marker_projectors())
