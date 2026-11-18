"""Finite checks of graph orientation witnesses over the field of three elements."""

from itertools import combinations, permutations
from random import Random


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def transpose(matrix):
    return list(zip(*matrix))


def product(left, right):
    return [[sum(a * b for a, b in zip(row, column)) % 3
             for column in transpose(right)] for row in left]


def determinant(matrix):
    rows = [list(row) for row in matrix]
    value = 1
    for i in range(len(rows)):
        pivot = next((j for j in range(i, len(rows)) if rows[j][i] % 3), None)
        if pivot is None:
            return 0
        if pivot != i:
            rows[i], rows[pivot] = rows[pivot], rows[i]
            value = -value
        value *= rows[i][i]
        for row in rows[i + 1:]:
            factor = row[i] * pow(rows[i][i] % 3, -1, 3)
            row[:] = [(x - factor * y) % 3 for x, y in zip(row, rows[i])]
    return value % 3


def pfaffian(matrix):
    if not matrix:
        return 1
    value = 0
    for j in range(1, len(matrix)):
        if matrix[0][j]:
            keep = [i for i in range(1, len(matrix)) if i != j]
            minor = [[matrix[x][y] for y in keep] for x in keep]
            value += (-1) ** (j + 1) * matrix[0][j] * pfaffian(minor)
    return value % 3


def volume(form, basis, corank):
    complement = [row[corank:] for row in basis]
    quotient = product(product(transpose(complement), form), complement)
    return determinant(basis) * pow(pfaffian(quotient), -1, 3) % 3


def test_volume():
    random = Random(126741)
    checks = 0
    for n in range(8):
        for k in range(n + 1):
            if (n - k) % 2:
                continue
            form = [[0] * n for _ in range(n)]
            for i in range(k, n, 2):
                form[i][i + 1], form[i + 1][i] = 1, 2
            for _ in range(3):
                perm = list(range(n))
                random.shuffle(perm)
                new_form = [[form[i][j] for j in perm] for i in perm]
                perm_matrix = [identity(n)[i] for i in perm]
                basis = [row[:] for row in perm_matrix]
                for row in basis:
                    if k < n:
                        row[k] = (2 * row[k] + (row[0] if k else 0)) % 3
                assert volume(new_form, basis, k) == determinant(perm_matrix) * volume(form, identity(n), k) % 3
                checks += 1
    return checks


def test_coronas():
    graphs = comparisons = 0
    for n in range(2, 6):
        pairs = list(combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = [edge for i, edge in enumerate(pairs) if mask & (1 << i)]
            if len({v for edge in edges for v in edge}) != n:
                continue
            adjacency = [[0] * (2 * n) for _ in range(2 * n)]
            for i, j in edges + [(v, n + v) for v in range(n)]:
                adjacency[i][j] = adjacency[j][i] = 1
            leaves = [int(sum(row) == 1) for row in adjacency]
            assert leaves == [0] * n + [1] * n
            form = [[(leaves[i] - leaves[j]) * a % 3 for j, a in enumerate(row)]
                    for i, row in enumerate(adjacency)]
            base_pf = pfaffian(form)
            assert base_pf and determinant(form) == base_pf ** 2 % 3
            graphs += 1
            for perm in permutations(range(n)):
                lifted = perm + tuple(n + i for i in perm)
                assert determinant([identity(n)[i] for i in perm]) ** 2 % 3 == 1
                assert all(form[u][v] == form[lifted[u]][lifted[v]]
                           for u, v in enumerate(range(n, 2 * n)))
                comparisons += 1
            # A swap of the displayed order changes the relative sign.
            order = [1, 0] + list(range(2, 2 * n))
            assert pfaffian([[form[i][j] for j in order] for i in order]) == -base_pf % 3
    return graphs, comparisons


if __name__ == "__main__":
    volume_cases = test_volume()
    corona_cases, lifted = test_coronas()
    print(f"PASS: {volume_cases} volume covariance checks, {corona_cases} coronas, "
          f"{lifted} lifted relabelings")
