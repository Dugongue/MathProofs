from itertools import combinations
from math import comb
from random import Random


def identity(side):
    return [[int(i == j) for j in range(side)] for i in range(side)]


def multiply(left, right, width):
    return [[sum(row[k] * right[k][j] for k in range(len(row)))
             for j in range(width)] for row in left]


def determinant(matrix):
    if len(matrix) == 0:
        return 1
    return sum((-1) ** j * entry * determinant(
        [row[:j] + row[j + 1:] for row in matrix[1:]])
        for j, entry in enumerate(matrix[0]) if entry != 0)


def principal_coefficient(matrix, order):
    return sum(determinant([[matrix[i][j] for j in indices] for i in indices])
               for indices in combinations(range(len(matrix)), order))


def check(s, r, t, generator):
    p = [[generator.randrange(-2, 3) for _ in range(r)] for _ in range(s)]
    q = [[generator.randrange(-2, 3) for _ in range(s)] for _ in range(r)]
    selected = generator.sample(range(r), t)
    free = [u for u in range(r) if u not in selected]
    pt = [[row[u] for u in selected] for row in p]
    qt = [q[u] for u in selected]
    pu = [[row[u] for u in free] for row in p]
    qu = [q[u] for u in free]
    w = multiply(pt, qt, s)
    m = multiply(pu, qu, s)
    reverse = multiply(qt, pt, t)
    complement = [[int(i == j) - w[i][j] for j in range(s)] for i in range(s)]
    square = [principal_coefficient(w, i) for i in range(s + 1)]
    assert square == [principal_coefficient(reverse, i) for i in range(s + 1)]
    for j in range(len(free) + 1, s + 1):
        assert principal_coefficient(m, j) == 0
        assert principal_coefficient(complement, j) == sum(
            (-1) ** i * comb(s - i, j - i) * square[i] for i in range(j + 1))
        assert sum((-1) ** i * comb(s - i, j - i) * comb(t, i)
                   for i in range(min(j, t) + 1)) == comb(s - t, j)

    pinned_rows = generator.sample(range(s), t)
    live_rows = [a for a in range(s) if a not in pinned_rows]
    for i in range(s):
        for u in range(r):
            if u in selected:
                p[i][u] = q[u][i] = int(i == pinned_rows[selected.index(u)])
            elif i in pinned_rows:
                p[i][u] = q[u][i] = 0
    assert multiply([[row[u] for u in selected] for row in p],
                    [q[u] for u in selected], s) == [
                        [int(i == j and i in pinned_rows) for j in range(s)]
                        for i in range(s)]
    assert multiply([q[u] for u in selected],
                    [[row[u] for u in selected] for row in p], t) == identity(t)
    expected = multiply([[p[i][u] for u in free] for i in live_rows],
                        [[q[u][j] for j in live_rows] for u in free], len(live_rows))
    forward = multiply(p, q, s)
    assert [[forward[i][j] for j in live_rows] for i in live_rows] == expected
    assert all(forward[i][j] == int(i == j) for i in range(s) for j in range(s)
               if i in pinned_rows or j in pinned_rows)


random = Random(20261121)
cases = 0
for s in range(2, 8):
    for r in range(1, s):
        for t in range(r + 1):
            for _ in range(4):
                check(s, r, t, random)
                cases += 1
print(f"Checked the partial-reverse coefficient identities and pinning in {cases} cases.")
