"""Exact finite controls for two-prime inversion and all-place graph trades."""

from itertools import combinations, permutations
from math import isqrt


def character(u, g):
    return (-1) ** ((u & g).bit_count() % 2)


def check_fourier():
    group = range(16)
    checked = 0
    for mapping in permutations(range(4)):
        if len({x ^ mapping[x] for x in range(4)}) != 4:
            continue
        planes = {frozenset((4+x, 8+y, (4+x) ^ (8+y))) for x, y in enumerate(mapping)}
        split = [[all(character(u, g) == 1 for u in plane) for g in group] for plane in planes]
        table = {(g, h): sum(4 * row[g] * row[h] for row in split) for g in group for h in group}
        for u, v in combinations(range(1, 16), 2):
            coefficient = sum(value * character(u, g) * character(v, h)
                              for (g, h), value in table.items())
            assert 4 * coefficient == 256 * (frozenset((u, v, u ^ v)) in planes)
        checked += 1
    assert checked == 8
    return checked


def check_graphs():
    vertices = range(5)
    edges = list(combinations(vertices, 2))
    checked = 0
    for mask in range(1 << len(edges)):
        chosen = [edge for i, edge in enumerate(edges) if mask & (1 << i)]
        primes = []
        for v in vertices:
            p = 17
            while (p in primes or any(p % k == 0 for k in range(2, isqrt(p) + 1))
                   or any(pow(p % primes[u], (primes[u] - 1) // 2, primes[u]) != 1
                          for u in range(v) if (u, v) in chosen)):
                p += 8
            primes.append(p)
        for triple in combinations(chosen, 3):
            support = {v for edge in triple for v in edge}
            product = 1
            for u, v in triple:
                product *= primes[u] * primes[v]
            assert (isqrt(product) ** 2 == product) == (len(support) == 3)
            if len(support) == 3:
                for v in support:
                    u, w = next(edge for edge in triple if v not in edge)
                    assert pow(primes[u] * primes[w], (primes[v] - 1) // 2, primes[v]) == 1
        checked += 1
    return checked


if __name__ == "__main__":
    print(f"Verified exact Fourier inversion for {check_fourier()} distinct algebras.")
    print(f"Verified triangle squareclasses and ramified local tests on {check_graphs()} graphs.")
