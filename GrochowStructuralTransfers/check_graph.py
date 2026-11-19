"""Finite checks for the uncolored ladder examples. Standard-library Python."""

from itertools import product


def target(columns, modulus, charge):
    leaf = 2 * columns
    edges = [(2 * j, 2 * j + 1) for j in range(columns)]
    edges += [(i, i + 2) for i in range(leaf - 2)] + [(0, leaf)]
    incident = [[] for _ in range(leaf + 1)]
    for i, (v, w) in enumerate(edges):
        incident[v].append((i, 1))
        incident[w].append((i, -1))
    endpoints = [[[], []] for _ in edges]
    count = 0
    for v, items in enumerate(incident):
        for xs in product(range(modulus), repeat=len(items)):
            total = sum(sign * x for (_, sign), x in zip(items, xs))
            if total % modulus != (charge if v == 0 else 0):
                continue
            for (edge, sign), x in zip(items, xs):
                endpoints[edge][int(sign < 0)].append((count, x))
            count += 1
    adj = [set() for _ in range(count)]
    for left, right in endpoints:
        for v, x in left:
            for w, y in right:
                if x == y:
                    adj[v].add(w)
                    adj[w].add(v)
    seen = {0}
    stack = [0]
    while stack:
        for w in adj[stack.pop()] - seen:
            seen.add(w)
            stack.append(w)
    assert len(seen) == count
    assert max(map(len, adj)) <= 3 * modulus
    return adj


def ladder_hom(columns, adj):
    # The source's first column has a leaf attached at its upper vertex.
    counts = {(v, w): len(ns) for v, ns in enumerate(adj) for w in ns}
    for _ in range(columns - 1):
        counts = {
            (v, w): sum(counts.get((a, b), 0) for a in adj[v] for b in adj[w])
            for v, w in counts
        }
    return sum(counts.values())


if __name__ == "__main__":
    for modulus in (2, 3, 6):
        for columns in (3, 4, 5, 6):
            left = target(columns, modulus, 0)
            right = target(columns, modulus, 1)
            assert len(left) == len(right)
            difference = ladder_hom(columns, left) - ladder_hom(columns, right)
            assert difference == modulus ** (columns - 1)
            print(modulus, columns, len(left), difference)
