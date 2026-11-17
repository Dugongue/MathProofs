"""Finite checks of degree calculations and the Vertex Cover gap."""
from itertools import combinations
from math import gcd, lcm, prod


def valuation(value, prime):
    power = 0
    while value % prime == 0:
        power += 1
        value //= prime
    return power


degree_checks = 0
direct_checks = 0
for q in (2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 25):
    for prime in (3, 5, 7, 11, 13, 17, 19):
        if q % prime == 0:
            continue
        e = next(j for j in range(1, prime) if pow(q, j, prime) == 1)
        v = valuation(q**e - 1, prime)
        for degree in range(1, 26):
            order = q**lcm(e, degree) - 1
            target_exponent = order // prime**v
            assert valuation(order, prime) == v + valuation(degree, prime)
            for k in range(1, 4):
                exponent = prime**k
                feasible = target_exponent % gcd(order, exponent) == 0
                assert feasible == (degree % exponent == 0)
                degree_checks += 1
                if order <= 1024:
                    brute = any(exponent * x % order == target_exponent
                                for x in range(order))
                    assert feasible == brute
                    direct_checks += 1

gap_checks = 0
for n in range(2, 6):
    edges = tuple(combinations(range(n), 2))
    primes = (3, 5, 7, 11, 13)[:n]
    cap = max(primes)
    floor = 2 ** (n * n + n * cap.bit_length() + 1)
    costs = []
    for prime in primes:
        weight = 1
        while weight < floor:
            weight *= prime
        costs.append(weight)
    coverings = [sum(1 << i for i in selected)
                 for t in range(n + 1) for selected in combinations(range(n), t)]
    for mask in range(1 << len(edges)):
        graph = [edge for i, edge in enumerate(edges) if mask >> i & 1]
        candidates = [cover for cover in coverings
                      if all(cover & (1 << i | 1 << j) for i, j in graph)]
        size = min(cover.bit_count() for cover in candidates)
        minimum = min(prod(cost for i, cost in enumerate(costs) if cover >> i & 1)
                      for cover in candidates)
        if size > 0:
            negative_threshold = (cap * floor) ** (size - 1)
            assert minimum > negative_threshold * 2**(n*n)
        assert minimum <= (cap * floor) ** size
        gap_checks += 1

print(f"{degree_checks} degree tests, including {direct_checks} exhaustive power maps")
print(f"{gap_checks} labelled graph gap checks")
