"""Replay small determinant-resolved cubic graph tensor examples.

The chord enumerator works in the prime field itself. The independent count
uses dense integer Smith operations and exponent coordinates over small fields.
The theorem's decision algorithm uses powering, so it needs no discrete logs.
"""
from collections import Counter
from itertools import product
from math import gcd, prod


def adjacency(size, edges):
    neighbors = [[None] * 3 for _ in range(size)]
    seen = set()
    for u, v, color in edges:
        key = tuple(sorted((u, v)))
        assert u != v and key not in seen
        assert neighbors[u][color] is None and neighbors[v][color] is None
        seen.add(key)
        neighbors[u][color] = v
        neighbors[v][color] = u
    assert all(None not in row for row in neighbors)
    for u in range(size):
        for a, b in product(neighbors[u], repeat=2):
            if a != b:
                assert set(neighbors[a]) & set(neighbors[b]) == {u}
    return neighbors


def spanning_tree(size, edges):
    neighbors = adjacency(size, edges)
    indices = {tuple(sorted((u, v))): i for i, (u, v, _) in enumerate(edges)}
    order = [0]
    parent = {0: (None, None)}
    for u in order:
        for v in neighbors[u]:
            if v not in parent:
                parent[v] = (u, indices[tuple(sorted((u, v)))])
                order.append(v)
    assert len(order) == size
    tree_edges = {index for _, index in parent.values()}
    chords = [i for i in range(len(edges)) if i not in tree_edges]
    return order, parent, chords


def dense_matrix(size, edges):
    matrix = [[0] * len(edges) for _ in range(size + 3)]
    for i, (u, v, color) in enumerate(edges):
        for row in (u, v, size + color):
            matrix[row][i] = 1
    return matrix


def smith(matrix, rhs=None):
    """Euclidean Smith operations for the small replay. Track the left rhs."""
    data = [list(row) for row in matrix]
    height, width = len(data), len(data[0])
    rhs = [0] * height if rhs is None else list(rhs)
    diagonal = []

    def swap_rows(a, b):
        data[a], data[b] = data[b], data[a]
        rhs[a], rhs[b] = rhs[b], rhs[a]

    def swap_columns(a, b):
        for row in data:
            row[a], row[b] = row[b], row[a]

    def subtract_row(i, j, multiple):
        data[i] = [x - multiple * y for x, y in zip(data[i], data[j], strict=True)]
        rhs[i] -= multiple * rhs[j]

    for k in range(min(height, width)):
        pivot = next(((i, j) for i in range(k, height) for j in range(k, width)
                      if data[i][j]), None)
        if pivot is None:
            break
        swap_rows(k, pivot[0])
        swap_columns(k, pivot[1])
        while True:
            for i in range(k + 1, height):
                quotient, remainder = divmod(data[i][k], data[k][k])
                if quotient:
                    subtract_row(i, k, quotient)
                if remainder:
                    swap_rows(i, k)
                    break
            else:
                for j in range(k + 1, width):
                    quotient, remainder = divmod(data[k][j], data[k][k])
                    if quotient:
                        for row in data:
                            row[j] -= quotient * row[k]
                    if remainder:
                        swap_columns(j, k)
                        break
                else:
                    bad_row = next((i for i in range(k + 1, height)
                                    if any(x % data[k][k] for x in data[i][k + 1:])), None)
                    if bad_row is None:
                        break
                    subtract_row(k, bad_row, -1)
        if data[k][k] < 0:
            data[k] = [-x for x in data[k]]
            rhs[k] = -rhs[k]
        diagonal.append(data[k][k])
    assert all(x == (diagonal[i] if i == j and i < len(diagonal) else 0)
               for i, row in enumerate(data) for j, x in enumerate(row))
    assert all(b % a == 0 for a, b in zip(diagonal, diagonal[1:]))
    return diagonal, rhs


def reduced_diagonal(size, edges):
    order, parent, chords = spanning_tree(size, edges)
    parity = {0: 1}
    alpha = {0: [0, 0, 0]}
    for v in order[1:]:
        u, e = parent[v]
        parity[v] = -parity[u]
        alpha[v] = [-x for x in alpha[u]]
        alpha[v][edges[e][2]] -= 1
        assert sum(alpha[v]) == (parity[v] - 1) // 2

    residual = []
    for i in chords:
        u, v, color = edges[i]
        a = [x + y + int(j == color) for j, (x, y) in enumerate(zip(alpha[u], alpha[v], strict=True))]
        beta = (parity[u] + parity[v]) // 2
        assert sum(a) == beta
        residual.append([a[0], a[1], beta])
    extra = next((row for row in residual if row[2]), None)
    if extra is not None:
        assert abs(extra[2]) == 1
        residual = [[row[j] - row[2] * extra[2] * extra[j] for j in range(2)] for row in residual]
    small, _ = smith(list(zip(*(row[:2] for row in residual), strict=True)))
    return [1] * (size - 1 + int(extra is not None)) + small


def permutation_sign(positions):
    inversions = sum(x > y for i, x in enumerate(positions) for y in positions[i + 1:])
    return (-1) ** inversions


def transport_signs(edges, target_edges, mapping):
    signs = []
    for color in range(3):
        ordered = [tuple(sorted((u, v))) for u, v, c in target_edges if c == color]
        index = {edge: i for i, edge in enumerate(ordered)}
        images = [index[tuple(sorted((mapping[u], mapping[v])))] for u, v, c in edges if c == color]
        signs.append(permutation_sign(images))
    return signs


def colored_maps(size, edges):
    neighbors = adjacency(size, edges)
    for image in range(size):
        roots = [0]
        found = {0: image}
        valid = True
        for v in roots:
            for u, w in zip(neighbors[v], neighbors[found[v]], strict=True):
                if u not in found:
                    found[u] = w
                    roots.append(u)
                elif found[u] != w:
                    valid = False
                    break
            if not valid:
                break
        if valid and len(set(found.values())) == size:
            yield [found[v] for v in range(size)]


def chord_counts(size, edges, demand, signs, p):
    order, parent, chords = spanning_tree(size, edges)
    counts = Counter()
    nonzero = range(1, p)
    inverses = [None, *(pow(x, -1, p) for x in nonzero)]
    for values in product(nonzero, repeat=len(chords)):
        remaining = list(demand)
        determinants = [s % p for s in signs]
        for i, value in zip(chords, values, strict=True):
            u, v, color = edges[i]
            inv = inverses[value]
            remaining[u] = remaining[u] * inv % p
            remaining[v] = remaining[v] * inv % p
            determinants[color] = determinants[color] * value % p
        for v in reversed(order[1:]):
            u, i = parent[v]
            color = edges[i][2]
            value = remaining[v]
            remaining[u] = remaining[u] * inverses[value] % p
            determinants[color] = determinants[color] * value % p
        if remaining[0] == 1:
            counts[tuple(determinants)] += 1
    return counts


def dense_count(matrix, demand, determinant, signs, p):
    order = p - 1
    generator = next(g for g in range(1, p) if len({pow(g, j, p) for j in range(order)}) == order)
    logs = {pow(generator, j, p): j for j in range(order)}
    targets = [*demand, *(d * s % p for d, s in zip(determinant, signs, strict=True))]
    diag, rhs = smith(matrix, [logs[value] for value in targets])
    counts = [gcd(order, d) for d in diag]
    if any(x % g for x, g in zip(rhs, counts)) or any(x % order for x in rhs[len(diag):]):
        return 0
    return order ** (len(matrix[0]) - len(diag)) * prod(counts)


def cyclic_graph(n):
    return 2 * n, [(i, n + (i + shift) % n, col)
                   for i in range(n) for col, shift in enumerate((0, 1, 3))]


def grid_graph(a, b):
    size = a * b
    edges = []
    for i, j in product(range(a), range(b)):
        vertex = i * b + j
        right = ((i + 1) % a) * b + j
        up = i * b + (j + 1) % b
        edges.extend([(vertex, size + right, 0), (vertex, size + up, 1), (vertex, size + vertex, 2)])
    return 2 * size, edges


def truncation_of_k4():
    k4 = [(0, 1, 0), (2, 3, 0), (0, 2, 1), (1, 3, 1), (0, 3, 2), (1, 2, 2)]
    edges = [(3 * u + c, 3 * v + c, c) for u, v, c in k4]
    edges.extend((3 * v + a, 3 * v + b, 3 - a - b)
                 for v in range(4) for a in range(3) for b in range(a + 1, 3))
    return 12, edges


def replay(size, edges, p):
    matrix = dense_matrix(size, edges)
    assert smith(matrix)[0] == reduced_diagonal(size, edges)
    assert sum(d > 1 for d in smith(matrix)[0]) <= 2
    relabelled = edges.copy()
    indices = [i for i, edge in enumerate(edges) if edge[2] == 0]
    a, b = indices[:2]
    relabelled[a], relabelled[b] = relabelled[b], relabelled[a]
    signs = transport_signs(edges, relabelled, list(range(size)))
    assert signs == [-1, 1, 1]
    u, v, _ = edges[0]
    demands = [[1] * size, [2 if i in (u, v) else 1 for i in range(size)],
               [2 if i == u else 1 for i in range(size)]]
    compared = 0
    for demand in demands:
        counts = chord_counts(size, edges, demand, signs, p)
        for determinant in product(range(1, p), repeat=3):
            actual = dense_count(matrix, demand, determinant, signs, p)
            assert actual == counts[determinant], (size, p, demand, determinant, actual, counts[determinant])
            compared += 1
    return compared


def main():
    compared = sum(replay(size, edges, p) for size, edges, p in (
        (*cyclic_graph(7), 3), (*cyclic_graph(7), 5), (*truncation_of_k4(), 5)))

    size, edges = cyclic_graph(7)
    u, v, color = edges[0]
    demand = [2 if i in (u, v) else 1 for i in range(size)]
    matrix = dense_matrix(size, edges)
    known_det = tuple(2 if c == color else 1 for c in range(3))
    assert dense_count(matrix, demand, known_det, [1, 1, 1], 5) > 0
    maps = list(colored_maps(size, edges))
    assert len(maps) == 14
    for mapping in maps:
        transported = [demand[mapping[v]] for v in range(size)]
        assert dense_count(matrix, transported, (1, 1, 1), transport_signs(edges, edges, mapping), 5) == 0

    size, edges = grid_graph(4, 4)
    matrix = dense_matrix(size, edges)
    dense, _ = smith(matrix)
    assert dense == reduced_diagonal(size, edges)
    assert dense[-2:] == [4, 4]
    assert dense_count(matrix, [1] * size, (1, 1, 1), [1, 1, 1], 5) > 0
    # Products remain one while exactly one ratio to the third colour is nontrivial.
    for target in ((4, 2, 2), (2, 4, 2)):
        assert prod(target) % 5 == 1
        assert dense_count(matrix, [1] * size, target, [1, 1, 1], 5) == 0
    print(f"Compared {compared} determinant counts. Checked {len(maps)} graph maps for the GL/SL separation and Smith factors 4, 4 for the grid.")


if __name__ == "__main__":
    main()
