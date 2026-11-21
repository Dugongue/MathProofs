"""Finite exact control for prescribed-residue tensor transporters."""

from collections import Counter
from itertools import product


# R = Z/8, first mode R + R/4, other two modes R.
IDENTITY = (1, 0, 0, 1, 1, 1)
MODULI = (8, 8, 4, 4, 8, 8)
COORDINATES = tuple(
    (bit, index)
    for bit in (1, 2)
    for index, modulus in enumerate(MODULI)
    if (1 << bit) < modulus
)


def multiply(left, right):
    a, b, c, d, u, v = left
    aa, bb, cc, dd, uu, vv = right
    return (
        (a * aa + b * cc) % 8,
        (a * bb + b * dd) % 8,
        (c * aa + d * cc) % 4,
        (c * bb + d * dd) % 4,
        u * uu % 8,
        v * vv % 8,
    )


def power(element, exponent):
    result = IDENTITY
    while exponent:
        if exponent & 1:
            result = multiply(result, element)
        element = multiply(element, element)
        exponent >>= 1
    return result


def inverse(element):
    return power(element, (1 << len(COORDINATES)) - 1)


def act(element, tensor):
    a, b, c, d, u, v = element
    x, y = tensor
    return u * v * (a * x + b * y) % 8, u * v * (c * x + d * y) % 4


def sift(element, pivots):
    for slot, (bit, index) in enumerate(COORDINATES):
        digit = ((element[index] - IDENTITY[index]) >> bit) & 1
        if not digit:
            continue
        if slot not in pivots:
            return slot, element
        element = multiply(inverse(pivots[slot]), element)
    assert element == IDENTITY
    return None


def collect(generators):
    pivots = {}
    while True:
        basis = tuple(pivots.values())
        tests = list(generators) + [multiply(b, b) for b in basis]
        for i, b in enumerate(basis):
            for c in basis[i + 1:]:
                tests.append(multiply(multiply(b, c), inverse(multiply(c, b))))
        for test in tests:
            result = sift(test, pivots)
            if result is not None:
                slot, element = result
                pivots[slot] = element
                break
        else:
            return tuple(pivots[slot] for slot in sorted(pivots))


def kernel(basis, character):
    a = next((b for b in basis if character(b)), None)
    if a is None:
        return basis
    a_inverse = inverse(a)
    generators = [multiply(a, a)]
    generators.extend(multiply(a_inverse, b) if character(b) else b for b in basis)
    current = collect(generators)
    while True:
        conjugates = [multiply(multiply(a, b), a_inverse) for b in current]
        enlarged = collect(current + tuple(conjugates))
        if len(enlarged) == len(current):
            return current
        current = enlarged


def solve_characters(basis, constraints):
    witness = IDENTITY
    for character, target in constraints:
        discrepancy = target ^ character(witness)
        a = next((b for b in basis if character(b)), None)
        if discrepancy and a is None:
            return None
        if discrepancy:
            witness = multiply(a, witness)
        basis = kernel(basis, character)
    return witness, basis


def lift(source, target, basis, restrict_scalar_determinants=False):
    if tuple(value % 2 for value in source) != tuple(value % 2 for value in target):
        return None
    witness = IDENTITY
    point = source
    for bit in (1, 2):
        mask = 1 << bit
        constraints = []
        for i in range(2):
            if mask >= (8, 4)[i]:
                continue
            origin = point
            def character(element, index=i, base=origin, shift=bit):
                return ((act(element, base)[index] - base[index]) >> shift) & 1
            desired = ((target[i] - point[i]) >> bit) & 1
            constraints.append((character, desired))
        solved = solve_characters(basis, constraints)
        if solved is None:
            return None
        correction, basis = solved
        point = act(correction, point)
        witness = multiply(correction, witness)
    assert point == target
    if restrict_scalar_determinants:
        for bit in (1, 2):
            constraints = []
            for i in (4, 5):
                def character(element, index=i, shift=bit):
                    return ((element[index] - 1) >> shift) & 1
                desired = ((1 - witness[i]) >> bit) & 1
                constraints.append((character, desired))
            solved = solve_characters(basis, constraints)
            if solved is None:
                return None
            correction, basis = solved
            witness = multiply(correction, witness)
        assert witness[4:] == (1, 1)
    assert act(witness, source) == target
    return witness, 1 << len(basis)


def main():
    generators = []
    for bit, index in COORDINATES:
        element = list(IDENTITY)
        element[index] += 1 << bit
        generators.append(tuple(element))
    basis = collect(generators)
    group = tuple(product(range(1, 8, 2), range(0, 8, 2), range(0, 4, 2),
                          range(1, 4, 2), range(1, 8, 2), range(1, 8, 2)))
    assert len(group) == 1 << len(basis) == 1024
    points = tuple(product(range(8), range(4)))
    cases = 0
    for constrained in (False, True):
        allowed = [g for g in group if not constrained or g[4:] == (1, 1)]
        for source in points:
            expected = Counter(act(g, source) for g in allowed)
            for target in points:
                lift_result = lift(source, target, basis, constrained)
                count = 0 if lift_result is None else lift_result[1]
                assert count == expected[target], (source, target, constrained)
                cases += 1
    assert lift((2, 2), (6, 2), basis)[1] == 512
    assert lift((2, 2), (6, 2), basis, True)[1] == 32
    assert lift((2, 2), (2, 0), basis) is None
    print(f"{cases} exact lift/count comparisons passed; example counts 512, 32, 0")


if __name__ == "__main__":
    main()
