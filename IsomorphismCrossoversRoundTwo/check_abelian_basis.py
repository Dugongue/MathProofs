"""Exact checks of the order-filtered greedy basis under relabeling."""

from itertools import product
from math import lcm, prod
from random import Random


def verify_type(p, powers, rng):
    moduli = tuple(p**power for power in powers)
    elements = list(product(*(range(m) for m in moduli)))

    def add(x, y):
        return tuple((a + b) % m for a, b, m in zip(x, y, moduli))

    def scale(k, x):
        return tuple(k * a % m for a, m in zip(x, moduli))

    def order(x):
        from math import gcd
        return lcm(*(m // gcd(m, a) for m, a in zip(moduli, x)))

    rng.shuffle(elements)
    ordered = sorted(elements, key=order)  # stable on randomly assigned labels
    subgroup = {scale(p, x) for x in elements}
    selected = []
    for x in ordered:
        if x in subgroup:
            continue
        selected.append(x)
        old = subgroup
        subgroup = {add(y, scale(j, x)) for y in old for j in range(p)}
    orders = tuple(map(order, selected))
    assert orders == moduli
    sums = {tuple(0 for _ in moduli)}
    for x, d in zip(selected, orders):
        sums = {add(y, scale(j, x)) for y in sums for j in range(d)}
    assert sums == set(elements) and len(sums) == prod(orders)


if __name__ == '__main__':
    rng = Random(487)
    types = ((2, (1, 1, 2)), (2, (1, 2, 3)), (2, (1, 1, 1, 3)),
             (2, (2, 2, 2)), (2, (1, 2, 4)), (3, (1, 1, 2)),
             (3, (1, 2)), (5, (1, 2)))
    for p, powers in types:
        for _ in range(10):
            verify_type(p, powers, rng)
    print('PASS: 80 order-filtered greedy basis and relabeling controls')
