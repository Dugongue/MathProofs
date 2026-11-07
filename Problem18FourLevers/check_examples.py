"""Exact finite controls for the graph, carrier and exterior-form arguments."""
from itertools import combinations, permutations, product
from random import Random


def rank(matrix, p):
    rows = [[x % p for x in row] for row in matrix]
    pivot = 0
    for j in range(len(rows[0])):
        i = next((i for i in range(pivot, len(rows)) if rows[i][j]), None)
        if i is None:
            continue
        rows[pivot], rows[i] = rows[i], rows[pivot]
        leading = pow(rows[pivot][j], -1, p)
        rows[pivot] = [x * leading % p for x in rows[pivot]]
        for i in range(pivot + 1, len(rows)):
            coefficient = rows[i][j]
            if coefficient:
                rows[i] = [(x - coefficient * y) % p for x, y in zip(rows[i], rows[pivot])]
        pivot += 1
    return pivot


def graphs():
    vertices = list(product(range(4), repeat=2))
    rook = {v: {w for w in vertices if v != w and (v[0] == w[0] or v[1] == w[1])}
            for v in vertices}
    shifts = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
    shrikhande = {v: {w for w in vertices if ((w[0]-v[0]) % 4, (w[1]-v[1]) % 4) in shifts}
                  for v in vertices}
    for graph in (rook, shrikhande):
        assert all(len(neighbors) == 6 for neighbors in graph.values())
        assert all(len(graph[v] & graph[w]) == 2 for v, w in combinations(vertices, 2))
        a = [[int(w in graph[v]) for w in vertices] for v in vertices]
        for eigenvalue, multiplicity in ((6, 1), (2, 6), (-2, 9)):
            shifted = [[x - eigenvalue * (i == j) for j, x in enumerate(row)]
                       for i, row in enumerate(a)]
            assert rank(shifted, 5) == 16 - multiplicity

    def four_clique(graph):
        return any(all(w in graph[v] for v, w in combinations(group, 2))
                   for group in combinations(vertices, 4))

    assert four_clique(rook) and not four_clique(shrikhande)


def carrier(p, n, alpha):
    plane_count = 3 * n
    plane_count += plane_count % 2
    if p == 3 and (2 * plane_count) % p == 2:
        plane_count += 2
    d = 2 * plane_count
    special = (d + alpha**2) % p
    assert special not in (0, 2)
    dual = [i ^ 1 for i in range(d)] + [d]
    entries = {}
    for j in range(3):
        for i in range(d):
            key = [i, i, i]
            key[j] = d
            key[2 if j != 2 else 1] = dual[i]
            entries[tuple(key)] = 1
    entries[(d, d, d)] = alpha
    for a, b, c in product(range(n), repeat=3):
        entries[2*a, 2*(b+n), 2*(c+2*n)] = (a + 2*b + c + 1) % p
    for mode in range(3):
        marginal = [[0] * (d + 1) for _ in range(d + 1)]
        for x, tx in entries.items():
            for y, ty in entries.items():
                if all(x[j] == dual[y[j]] for j in range(3) if j != mode):
                    marginal[x[mode]][dual[y[mode]]] += tx * ty
        assert all(value % p == ((2 if i < d else special) if i == j else 0)
                   for i, row in enumerate(marginal) for j, value in enumerate(row))


def exterior_trace(p, n):
    random = Random(42 + p)
    basis = list(combinations(range(n), 3))
    index = {row: i for i, row in enumerate(basis)}
    coeff = [random.randrange(p) for _ in basis]

    def sign(row):
        return (-1)**sum(a > b for a, b in combinations(row, 2))

    entries = {w: sign(w) * value for row, value in zip(basis, coeff)
               for w in permutations(row)}
    gram = [[sum(entries.get((i,k,l),0) * entries.get((j,k,l),0)
                 for k, l in product(range(n), repeat=2)) % p
             for j in range(n)] for i in range(n)]
    if p == 3:
        assert sum(gram[i][i] for i in range(n)) % p == 0
    s = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            s[i][j] = s[j][i] = random.randrange(p)
    derivative = [[0] * len(basis) for _ in basis]
    for j, row in enumerate(basis):
        for k, source in enumerate(row):
            for target in range(n):
                replacement = row[:k] + (target,) + row[k+1:]
                if len(set(replacement)) == 3:
                    i = index[tuple(sorted(replacement))]
                    derivative[i][j] += sign(replacement) * s[target][source]
    trace = sum(s[i][j] * gram[j][i] for i, j in product(range(n), repeat=2))
    quadratic = sum(x * value * y for x, row in zip(coeff, derivative)
                    for value, y in zip(row, coeff))
    assert (trace - 2 * quadratic) % p == 0


if __name__ == "__main__":
    graphs()
    carrier(5, 2, 1)
    carrier(3, 2, 1)
    for field in (3, 5, 7):
        exterior_trace(field, 8)
    print("PASS: strongly regular collision, fixed Gram carrier, and exterior trace identity.")
