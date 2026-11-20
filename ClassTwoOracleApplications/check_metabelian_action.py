"""Finite exact controls for operator and point markings and group extension records."""

from itertools import product
from math import gcd
from random import Random


def check_exact_tag_products():
    checked = 0
    for modulus in (4, 8, 9, 16, 27):
        rng = Random(modulus)
        for rank in range(1, 9):
            count = 1 + 2 * rank
            zero = (0,) * count
            operators = [rng.randrange(modulus) for _ in range(rank)]
            relators = [[rng.randrange(modulus) if i <= j else 0
                         for i in range(rank)] for j in range(rank)]
            tags = [tuple(int(i == j) for i in range(count)) for j in range(count)]

            def multiply(left, right):
                x, a = left
                y, b = right
                data = sum(a[1 + j] * op * y for j, op in enumerate(operators))
                data += sum(a[1 + j] * b[1 + rank + i] * relators[j][i]
                            for j, i in product(range(rank), repeat=2))
                return data % modulus, tuple(u * v % modulus for u, v in zip(a, b))

            for t in tags:
                assert multiply((0, t), (0, t)) == (0, t)
                for unit in range(1, modulus):
                    if gcd(unit, modulus) == 1:
                        scaled = (0, tuple(unit * v for v in t))
                        assert (multiply(scaled, scaled) == scaled) == (unit == 1)
                        checked += 1
            for j, i in product(range(rank), repeat=2):
                assert multiply((0, tags[1 + j]), (0, tags[1 + rank + i])) == (
                    relators[j][i], zero
                )
                checked += 1
            for j, op in enumerate(operators):
                for scalar in range(modulus):
                    assert multiply((0, tags[1 + j]), (scalar, zero)) == (
                        op * scalar % modulus, zero
                    )
                    checked += 1
            for _ in range(32):
                x = rng.randrange(modulus)
                a = tuple(rng.randrange(modulus) for _ in range(count))
                for state in ((x, a), (x, zero)):
                    assert (all(multiply(state, (0, tag)) == (0, zero) for tag in tags)
                            == (state[1] == zero))
                    checked += 1
    return checked

def check_normalization():
    checked = 0
    for modulus in (4, 8, 9, 25):
        units = [i for i in range(1, modulus) if gcd(i, modulus) == 1]
        rng = Random(modulus)
        for _ in range(700):
            u, v, w = (rng.choice(units) for _ in range(3))
            a, b, z = (rng.choice(units) for _ in range(3))
            x = z * pow(a, -1, modulus) % modulus
            y = z * pow(b, -1, modulus) % modulus
            gauged_x = u * pow(v, -1, modulus) * x % modulus
            gauged_y = v * pow(w, -1, modulus) * y % modulus
            gauged_z = u * pow(w, -1, modulus) * z % modulus
            gauged_a = gauged_z * pow(gauged_x, -1, modulus) % modulus
            gauged_b = gauged_z * pow(gauged_y, -1, modulus) % modulus
            assert gauged_z * pow(gauged_a * gauged_b, -1, modulus) % modulus == (
                z * pow(a * b, -1, modulus) % modulus
            )
            checked += 1
    return checked


def table_cyclic_extension(modulus, degree, action, power):
    """Return a split or nonsplit extension on ordered pairs (kernel, quotient)."""
    assert pow(action, degree, modulus) == 1
    assert action * power % modulus == power

    def mul(x, y):
        a, i = x
        b, j = y
        return (
            (a + pow(action, i, modulus) * b + ((i + j) // degree) * power) % modulus,
            (i + j) % degree,
        )

    def pow_element(x, n):
        result = (0, 0)
        while n:
            if n & 1:
                result = mul(result, x)
            x = mul(x, x)
            n //= 2
        return result

    return mul, pow_element


def check_isomorphism_partitions():
    modulus, degree, action = 8, 2, -1
    elements = list(product(range(modulus), range(degree)))
    checked, comparisons = 0, {}
    for source_power, target_power in product((0, 4), repeat=2):
        source_mul, _ = table_cyclic_extension(modulus, degree, action, source_power)
        target_mul, target_pow = table_cyclic_extension(modulus, degree, action, target_power)
        accepted = 0
        for unit in (1, 3, 5, 7):
            for translate in range(modulus):
                image_lift = (translate, 1)
                kernel = lambda a: (unit * a % modulus, 0)

                def candidate(point):
                    a, i = point
                    return target_mul(kernel(a), target_pow(image_lift, i))

                from_records = (
                    target_pow(image_lift, degree) == kernel(source_power)
                    and all(
                        target_mul(image_lift, kernel(a)) ==
                        target_mul(kernel(action * a % modulus), image_lift)
                        for a in range(modulus)
                    )
                )
                from_table = all(
                    target_mul(candidate(x), candidate(y)) == candidate(source_mul(x, y))
                    for x, y in product(elements, repeat=2)
                )
                assert from_records == from_table
                checked += 1
                accepted += from_records
        comparisons[source_power, target_power] = accepted
    assert comparisons == {(0, 0): 32, (0, 4): 0, (4, 0): 0, (4, 4): 32}
    return checked


def check_unbounded_class_examples():
    checked = 0
    for p in (3, 5, 7):
        for m in range(2, 9):
            modulus = p**m
            action = 1 + p
            exact_order = p ** (m - 1)
            exact_order_on_derived = p ** (m - 2)
            assert pow(action, exact_order, modulus) == 1
            assert pow(action, exact_order // p, modulus) != 1
            assert p * (pow(action, exact_order_on_derived, modulus) - 1) % modulus == 0
            if m > 2:
                assert p * (pow(action, exact_order_on_derived // p, modulus) - 1) % modulus != 0
            commutator_step = action - 1
            assert pow(commutator_step, m, modulus) == 0
            assert pow(commutator_step, m - 1, modulus) != 0
            checked += 1
    return checked


if __name__ == "__main__":
    print("Exact tag products and idempotents:", check_exact_tag_products())
    print("Diagonal gauge normalizations:", check_normalization())
    print("Lift records against complete tables:", check_isomorphism_partitions())
    print("Class and faithful-action examples:", check_unbounded_class_examples())
