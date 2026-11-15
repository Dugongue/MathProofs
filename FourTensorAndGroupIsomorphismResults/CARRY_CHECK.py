"""Finite checks for the quadratic augmentation quotient in JETS.md."""

from itertools import product
from math import comb


def monomials(orders):
    return [term for term in product(*(range(order) for order in orders)) if sum(term) <= 2]


def basis_expansion(exponents):
    return [
        powers
        for powers in product(*(range(exponent + 1) for exponent in exponents))
        if all(comb(exponent, power) % 2 for exponent, power in zip(exponents, powers))
    ]


def check(orders):
    basis = monomials(orders)
    pairs = [(a, b) for a, b in product(basis, repeat=2) if sum(a) + sum(b) <= 2]
    exponent_index = {exp: index for index, exp in enumerate(basis)}

    def point(group_element):
        return sum(
            1 << index
            for index, exponents in enumerate(basis)
            if all(comb(x, exponent) % 2 for x, exponent in zip(group_element, exponents))
        )

    def has_monomial(vector, exponent):
        return vector >> exponent_index[exponent] & 1

    def product_quotient(left, right):
        return sum(
            1 << index
            for index, (a, b) in enumerate(pairs)
            if has_monomial(left, a) and has_monomial(right, b)
        )

    def multiply(left, right):
        result = 0
        for a, b in product(basis, repeat=2):
            if has_monomial(left, a) and has_monomial(right, b):
                exponents = tuple(x + y for x, y in zip(a, b))
                if exponents in exponent_index:
                    result ^= 1 << exponent_index[exponents]
        return result

    diagonal = []
    for exponents in basis:
        entry = 0
        for group_element in basis_expansion(exponents):
            y = point(group_element)
            entry ^= product_quotient(y, y)
        diagonal.append(entry)

    def diagonal_value(vector):
        result = 0
        for index, value in enumerate(diagonal):
            if vector >> index & 1:
                result ^= value
        return result

    points = {x: point(x) for x in product(*(range(order) for order in orders))}
    assert len(set(points.values())) == len(points)
    elements = range(1, 1 << len(basis), 2)
    group_likes = {u for u in elements if diagonal_value(u) == product_quotient(u, u)}
    assert group_likes == set(points.values())
    for (x, u), (y, v) in product(points.items(), repeat=2):
        group_sum = tuple((a + b) % order for a, b, order in zip(x, y, orders))
        assert multiply(u, v) == points[group_sum]
    return len(elements), len(points), len(points)**2


if __name__ == "__main__":
    totals = [0, 0, 0]
    for count in range(4):
        for order_four in range(count + 1):
            orders = (2,) * (count - order_four) + (4,) * order_four
            result = check(orders)
            print(orders, result)
            totals = [old + new for old, new in zip(totals, result)]
    print("Totals (augmentation-one elements, group elements, ordered addition pairs)", totals)
