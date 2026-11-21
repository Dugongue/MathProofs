"""Exact controls for the edited terminal-profile theorem. Python 3.10+."""

from itertools import combinations, permutations
from math import inf
from random import Random


def graph_rows(n, edges):
    rows = [set() for _ in range(n)]
    for u, v in edges:
        rows[u].add(v)
        rows[v].add(u)
    return rows


def shortest_paths(n, edges, retained):
    dist = [[inf] * n for _ in range(n)]
    for u in retained:
        dist[u][u] = 0
    for (u, v), weight in edges.items():
        if u in retained and v in retained:
            dist[u][v] = dist[v][u] = min(dist[u][v], weight)
    for k in retained:
        for i in retained:
            for j in retained:
                dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j])
    return dist


def segment_lengths(rows, anchors):
    outside = set(range(len(rows))) - set(anchors)
    segments = {}
    for i, s in enumerate(anchors):
        length = 2
        count = {v: int(v in rows[s]) for v in outside}
        while length < len(rows):
            for j in range(i + 1, len(anchors)):
                t = anchors[j]
                if any(count[v] > 0 for v in outside & rows[t]):
                    segments.setdefault((i, j), length)
            count = {v: sum(count[w] for w in outside & rows[v]) for v in outside}
            length += 1
    return segments


def check_edits():
    rng = Random(21112603)
    for _ in range(240):
        n = rng.randrange(4, 12)
        r = rng.randrange(3, min(n, 6) + 1)
        original = {p: 1 for p in combinations(range(n), 2) if rng.randrange(3) == 0}
        anchors = rng.sample(range(n), r)
        keep = [i for i in range(r) if rng.randrange(4)]
        retained = set(range(n)) - {anchors[i] for i in range(r) if i not in keep}
        edits = {(i, j): rng.choice((None, 1, 2, 4, 9))
                 for i, j in combinations(range(r), 2) if rng.randrange(2)}
        actual_edges = original.copy()
        compressed = segment_lengths(graph_rows(n, original), anchors)
        for i, j in combinations(range(r), 2):
            endpoints = tuple(sorted((anchors[i], anchors[j])))
            if (i, j) in edits:
                actual_edges.pop(endpoints, None)
                if edits[i, j] is not None:
                    actual_edges[endpoints] = edits[i, j]
            if endpoints in actual_edges:
                compressed[i, j] = min(compressed.get((i, j), inf), actual_edges[endpoints])
        expected = shortest_paths(n, actual_edges, retained)
        actual = shortest_paths(r, compressed, keep)
        assert all(actual[i][j] == expected[anchors[i]][anchors[j]]
                   for i in keep for j in keep)
    print("240 edited shortest-path tables matched the full-host calculation.")


def parity_lift(r, twisted):
    vertices = [(v, mask) for v in range(r) for mask in range(1 << r)
                if not mask & (1 << v) and (mask.bit_count() % 2 == (twisted and v == 0))]
    return graph_rows(len(vertices) + 1, [
        (a, b) for a, b in combinations(range(len(vertices)), 2)
        if vertices[a][0] != vertices[b][0]
        and (vertices[a][1] >> vertices[b][0] & 1)
        == (vertices[b][1] >> vertices[a][0] & 1)
    ] + [(a, len(vertices)) for a in range(len(vertices))])


def count_cliques(rows, size):
    def extend(remaining, to_add):
        if to_add == 0:
            return 1
        total = 0
        for v in sorted(remaining):
            remaining.remove(v)
            total += extend(remaining & rows[v], to_add - 1)
        return total
    return extend(set(range(len(rows))), size)


def hamiltonian_vertex_sets(rows, size):
    result = set()

    def extend(root, last, mask, remaining):
        if remaining == 0:
            if root in rows[last]:
                result.add(mask)
            return
        for v in rows[last]:
            if v > root and not mask & (1 << v):
                extend(root, v, mask | (1 << v), remaining - 1)

    for root in range(len(rows)):
        extend(root, root, 1 << root, size - 1)
    return len(result)


def hamiltonian_top_coefficient(size):
    edge_index = {edge: i for i, edge in enumerate(combinations(range(size), 2))}
    cycles = set()
    for perm in permutations(range(1, size)):
        order = (0,) + perm
        cycles.add(sum(1 << edge_index[tuple(sorted((u, v)))]
                       for u, v in zip(order, perm + (0,))))
    coefficient = 0
    for mask in range(1 << len(edge_index)):
        if any(mask & cycle == cycle for cycle in cycles):
            coefficient += (-1) ** (len(edge_index) - mask.bit_count())
    return coefficient


def check_width_witnesses():
    for r in (3, 4, 5):
        edges = r * (r - 1) // 2
        multiplicity = 1 << (edges - r + 1)
        graphs = [parity_lift(r, twisted) for twisted in (False, True)]
        assert all(len(rows) == r * (1 << (r - 2)) + 1 for rows in graphs)
        complements = [[set(range(len(rows))) - {v} - row
                        for v, row in enumerate(rows)] for rows in graphs]
        a, b = [count_cliques(rows, r) for rows in complements]
        assert a - b == (-1) ** edges * multiplicity
        print(f"r={r}, most expensive bin difference {a - b}.")
        if r in (3, 5):
            coefficient = hamiltonian_top_coefficient(r)
            a, b = [hamiltonian_vertex_sets(rows, r) for rows in graphs]
            assert coefficient % r == (-1) ** (edges + 1) % r
            assert a - b == coefficient * multiplicity
            print(f"r={r}, cheapest bin difference {a - b}, coefficient {coefficient}.")


if __name__ == "__main__":
    check_edits()
    check_width_witnesses()
