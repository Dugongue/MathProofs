"""Exact prime-field checks for concrete cubic graph tensor instances."""
from collections import Counter
from itertools import combinations, product
import json
from math import gcd
from random import Random


def shifts(n):
    return [(i, n + (i + delta) % n, color)
            for color, delta in enumerate((0, 1, 3)) for i in range(n)]


def tetrahedron():
    return [(v, v ^ delta, delta - 1)
            for delta in range(1, 4) for v in range(4) if v < v ^ delta]


def truncate(graph, n):
    spokes = [(3 * u + c, 3 * v + c, c) for u, v, c in graph]
    triangles = [(3 * v + a, 3 * v + b, 3 - a - b)
                 for v in range(n) for a, b in combinations(range(3), 2)]
    return spokes + triangles


def has_square(edges, n):
    adjacency = [set() for _ in range(n)]
    for u, v, _ in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    return any(len(adjacency[u] & adjacency[v]) >= 2
               for u, v in combinations(range(n), 2))


def rank_mod(rows, p):
    rank = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        fixed = rows[rank]
        for row in rows[rank + 1:]:
            if row[col]:
                c = row[col] * pow(fixed[col], -1, p) % p
                for j in range(col, len(row)):
                    row[j] = (row[j] - c * fixed[j]) % p
        rank += 1
    return rank


def check_contractions(edges, n, p, exhaustive, rng):
    axes = [[None] * n for _ in range(3)]
    cardinality = [0] * 3
    for u, v, color in edges:
        assert axes[color][u] is None and axes[color][v] is None
        axes[color][u] = axes[color][v] = cardinality[color]
        cardinality[color] += 1
    assert all(all(i is not None for i in axis) for axis in axes)
    square = has_square(edges, n)
    count = 0
    witness = False
    for color in range(3):
        other = [i for i in range(3) if i != color]
        dim = cardinality[color]
        weights = [rng.randrange(1, p) for _ in range(n)]
        if exhaustive:
            vectors = product(range(p), repeat=dim)
        else:
            tests = (tuple(int(i in support) for i in range(dim))
                     for length in range(1, 4)
                     for support in combinations(range(dim), length))
            vectors = list(tests) + [tuple(rng.randrange(p) for _ in range(dim))
                                     for _ in range(600)]
        for x in vectors:
            selected = sum(a != 0 for a in x)
            if not selected:
                continue
            rows = [[0] * cardinality[other[1]] for _ in range(cardinality[other[0]])]
            for i, (a, b) in enumerate(zip(*(axes[k] for k in other))):
                assert rows[a][b] == 0
                rows[a][b] = x[axes[color][i]] * weights[i] % p
            rank = rank_mod(rows, p)
            if selected == 1:
                assert rank == 2
            elif rank <= 2:
                assert square, (n, p, color, x, rank)
                witness = True
            count += 1
    assert witness == square
    return count


def measure_lifts(edges, n, p, demands):
    neighbors = [[] for _ in range(n)]
    for i, (u, v, _) in enumerate(edges):
        neighbors[u].append((v, i))
        neighbors[v].append((u, i))
    order = [0]
    parent = {0: None}
    signs = {0: 1}
    tree = set()
    for u in order:
        for v, i in neighbors[u]:
            if v not in parent:
                order.append(v)
                parent[v] = (u, i)
                signs[v] = -signs[u]
                tree.add(i)
    assert len(order) == n
    chords = [i for i in range(len(edges)) if i not in tree]
    bip = all(signs[u] != signs[v] for u, v, _ in edges)
    signed = 1
    unsigned = 1
    for u, a in enumerate(demands):
        signed = signed * pow(a, signs[u], p) % p
        unsigned = unsigned * a % p
    if bip:
        expected = (p - 1) ** len(chords) if signed == 1 else 0
    else:
        square = any(a * a % p == unsigned for a in range(1, p))
        expected = gcd(2, p - 1) * (p - 1) ** (len(chords) - 1) if square else 0
    count = 0
    for gains in product(range(1, p), repeat=len(chords)):
        trial = [1] * len(edges)
        residual = list(demands)
        for i, a in zip(chords, gains):
            trial[i] = a
            u, v, _ = edges[i]
            inv = pow(a, -1, p)
            residual[u] = residual[u] * inv % p
            residual[v] = residual[v] * inv % p
        for v in reversed(order[1:]):
            u, i = parent[v]
            trial[i] = residual[v]
            residual[u] = residual[u] * pow(trial[i], -1, p) % p
        if residual[0] == 1:
            found = [1] * n
            for a, (u, v, _) in zip(trial, edges):
                found[u] = found[u] * a % p
                found[v] = found[v] * a % p
            assert found == demands
            count += 1
    assert count == expected
    return count


def main():
    rng = Random(190700309)
    cases = [("tetrahedron", tetrahedron(), 4), ("heawood", shifts(7), 14),
             ("cyclic-8", shifts(8), 16), ("truncated-tetrahedron", truncate(tetrahedron(), 4), 12)]
    contractions = {}
    lifts = {}
    for name, edges, n in cases:
        assert set(Counter(v for u, w, _ in edges for v in (u, w)).values()) == {3}
        for p in (2, 3, 5, 7):
            contractions[f"{name}/F{p}"] = check_contractions(
                edges, n, p, p <= 2 or (p == 3 and n <= 14), rng)
        for p in (3, 5):
            lifts[f"{name}/F{p}"] = [measure_lifts(edges, n, p, [a] + [1] * (n - 1))
                                    for a in range(1, p)]
    print(json.dumps({"contraction_count": sum(contractions.values()),
                      "contractions": contractions, "lift_counts": lifts}, indent=2))


if __name__ == "__main__":
    main()
