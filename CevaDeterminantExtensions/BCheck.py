from itertools import combinations, product
from math import inf
from random import Random


def thresholds(modulus, target):
    active = []
    n = modulus
    for p in range(2, modulus + 1):
        extent = 1
        while n % p == 0:
            n //= p
            extent *= p
        if extent == 1 or target % extent == 0:
            continue
        q = p
        while target % q == 0:
            q *= p
        active.append(q)
    return active


def assignment_min(modulus, target, charges, edges):
    best = inf
    for rest in product(range(modulus), repeat=len(charges) - 1):
        labels = (0, *rest)
        if sum(v*b for v, b in zip(labels, charges)) % modulus != target:
            continue
        crossing = [(c, available) for u, v, c, available in edges if labels[u] != labels[v]]
        if all(available for _, available in crossing):
            best = min(best, sum(c for c, _ in crossing))
    return best


def component_charges(charges, edges, deleted):
    parent = list(range(len(charges)))

    def find(u):
        while parent[u] != u:
            u = parent[u]
        return u

    for i, (u, v, _, _) in enumerate(edges):
        if i not in deleted:
            parent[find(u)] = find(v)
    values = [0] * len(charges)
    for v, b in enumerate(charges):
        values[find(v)] += b
    return values


def deletion_min(charges, edges, active):
    eligible = [i for i, (_, _, _, yes) in enumerate(edges) if yes]
    best = inf
    for selected in product((False, True), repeat=len(eligible)):
        deleted = {i for i, use in zip(eligible, selected) if use}
        charge = component_charges(charges, edges, deleted)
        if all(any(b % q for b in charge) for q in active):
            best = min(best, sum(edges[i][2] for i in deleted))
    return best


def binary_min(charges, edges, active):
    best = inf
    for rest in product((0, 1), repeat=len(charges) - 1):
        labels = (0, *rest)
        charge = sum(v*b for v, b in zip(labels, charges))
        if not all(charge % q for q in active):
            continue
        crossing = [(c, available) for u, v, c, available in edges if labels[u] != labels[v]]
        if all(available for _, available in crossing):
            best = min(best, sum(c for c, _ in crossing))
    return best


def multiway_min(n, edges):
    best = inf
    for rest in product(range(3), repeat=n - 3):
        labels = (0, 1, 2, *rest)
        best = min(best, sum(c for u, v, c, _ in edges if labels[u] != labels[v]))
    return best


def test_general(rng):
    cases = 0
    for modulus, target in ((4, 1), (8, 4), (9, 3), (6, 1), (12, 2), (18, 3), (30, 1)):
        active = thresholds(modulus, target)
        for _ in range(18):
            n = rng.choice((3, 4))
            graph = {(i, i + 1) for i in range(n - 1)}
            graph |= {e for e in combinations(range(n), 2) if rng.randrange(2)}
            edges = [(u, v, rng.randrange(6), rng.randrange(4) != 0) for u, v in sorted(graph)]
            charges = [rng.randrange(-20, 21) for _ in range(n - 1)]
            charges.append(-sum(charges))
            value = assignment_min(modulus, target, charges, edges)
            assert value == deletion_min(charges, edges, active)
            if len(active) <= 2:
                assert value == binary_min(charges, edges, active)
            cases += 1
    return cases


def test_threeway():
    assert len({pow(3, e, 31) for e in range(30)}) == 30
    assert (25 - 34*6) % 30 == 1
    for a, b, c in product(range(30), repeat=3):
        if (9*a + 25*b - 34*c) % 30 == 1:
            assert len({a, b, c}) == 3

    charges = [9, 25, -34, 0]
    pairs = list(combinations(range(4), 2))
    cases = 0
    for weights in product((0, 1), repeat=len(pairs)):
        edges = [(u, v, w, True) for (u, v), w in zip(pairs, weights)]
        assert multiway_min(4, edges) == deletion_min(charges, edges, [2, 3, 5])
        cases += 1
    return cases


if __name__ == '__main__':
    print(f'{test_general(Random(31030))} label/deletion comparisons passed')
    print(f'{test_threeway()} multiway cut comparisons and all terminal residues passed')
