"""Independent parser and exact prime-field witness verification."""
from math import isqrt


def read_pair(path):
    values = list(map(int, path.read_text(encoding="utf-8-sig").split()))
    if len(values) < 4:
        raise ValueError("Missing input header")
    p, m, n, k = values[:4]
    if p < 2 or any(p % d == 0 for d in range(2, isqrt(p) + 1)):
        raise ValueError("Expected a prime field")
    if min(m, n, k) <= 0 or len(values) != 4 + 2 * m * n * k:
        raise ValueError("Format disagrees with the number of coefficients")
    if any(not 0 <= a < p for a in values[4:]):
        raise ValueError("Coefficient outside the prime field")
    def tensor(start):
        return [
            [values[start + (h * m + i) * n:start + (h * m + i + 1) * n] for i in range(m)]
            for h in range(k)
        ]
    return p, m, n, k, tensor(4), tensor(4 + m * n * k)


def rank(matrix, p):
    matrix = [row.copy() for row in matrix]
    rank = 0
    for col in range(len(matrix[0])):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][col]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][col], -1, p)
        matrix[rank] = [inverse * a % p for a in matrix[rank]]
        for i in range(rank + 1, len(matrix)):
            if matrix[i][col]:
                c = matrix[i][col]
                matrix[i] = [(a - c * b) % p for a, b in zip(matrix[i], matrix[rank])]
        rank += 1
        if rank == len(matrix):
            break
    return rank


def product(a, b, p):
    return [[sum(x * y for x, y in zip(row, col)) % p for col in zip(*b)] for row in a]


def verify(p, m, n, k, a, b, left, right, mixing):
    if [rank(left, p), rank(right, p), rank(mixing, p)] != [m, n, k]:
        return False
    for h in range(k):
        transformed = product(product(left, a[h], p), right, p)
        for i in range(m):
            for j in range(n):
                if transformed[i][j] != sum(mixing[h][s] * b[s][i][j] for s in range(k)) % p:
                    return False
    return True
