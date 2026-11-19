"""Direct uncolored Hom counts for the coset-port construction on a theta base.

Two sites share three distinct edges. After subdivision the probe is a simple
graph of three internally disjoint paths of the same length. No dependencies.
"""

from itertools import product
from math import prod


def make_target(primes, charge):
    r = prod(primes)
    moduli = [r]
    for prime in primes:
        moduli.append(moduli[-1] // prime)
    names = {}
    adj = []

    def vertex(name):
        if name not in names:
            names[name] = len(adj)
            adj.append(set())
        return names[name]

    def link(left, right):
        v, w = vertex(left), vertex(right)
        adj[v].add(w)
        adj[w].add(v)

    for v in range(2):
        for a, b in product(range(r), repeat=2):
            c = ((charge if v == 0 else 0) - a - b) % r
            values = (a, b, c)
            for e in range(3):
                link((v, "row", a, b), (v, e, 0, values[e], values[(e + 1) % 3]))
        for e, x in product(range(3), range(r)):
            for j, m in enumerate(moduli[:-1]):
                for y in range(m):
                    link((v, e, j, x, y), (v, e, j + 1, x, y % moduli[j + 1]))
    for e, x in product(range(3), range(r)):
        link((0, e, len(primes), x, 0), (1, e, len(primes), x, 0))
    return adj


def theta_count(adj, length):
    total = 0
    for start in range(len(adj)):
        ways = {start: 1}
        for _ in range(length):
            following = {}
            for v, count in ways.items():
                for w in adj[v]:
                    following[w] = following.get(w, 0) + count
            ways = following
        total += sum(x**3 for x in ways.values())
    return total


if __name__ == "__main__":
    for primes in ((2,), (3,), (5,), (2, 3), (3, 2)):
        left, right = (make_target(primes, charge) for charge in (0, 1))
        assert len(left) == len(right)
        for graph in (left, right):
            assert max(map(len, graph)) == 1 + max(primes)
            seen, stack = {0}, [0]
            while stack:
                new = graph[stack.pop()] - seen
                seen.update(new)
                stack.extend(new)
            assert len(seen) == len(graph)
        length = 2 * len(primes) + 3
        difference = theta_count(left, length) - theta_count(right, length)
        assert difference > 0 and difference % prod(primes)**2 == 0
        print(primes, len(left), max(map(len, left)), difference)
