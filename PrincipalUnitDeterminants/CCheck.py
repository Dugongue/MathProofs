"""Verify substitution determinants by direct products over small commutative rings."""

from functools import cache
from itertools import permutations, product
from math import comb


class Ring:
    def __init__(self, name, size, add, mul, residue_prime=None, residue=None):
        self.name = name
        self.size = size
        self.add = [[add(i, j) for j in range(size)] for i in range(size)]
        self.mul = [[mul(i, j) for j in range(size)] for i in range(size)]
        self.neg = [row.index(0) for row in self.add]
        self.units = {i for i, row in enumerate(self.mul) if 1 in row}
        self.p = residue_prime
        self.residue = residue

    def power(self, a, exponent):
        value = 1
        while exponent:
            if exponent & 1:
                value = self.mul[value][a]
            a = self.mul[a][a]
            exponent >>= 1
        return value


def modular(n, p=None):
    return Ring(
        f"Z/{n}", n, lambda a, b: (a + b) % n,
        lambda a, b: a * b % n, p, (lambda a: a % p) if p else None,
    )


def truncated_field(p, degree):
    size = p**degree
    digits = [tuple(a // p**i % p for i in range(degree)) for a in range(size)]

    def add(a, b):
        return sum((x + y) % p * p**i for i, (x, y) in
                   enumerate(zip(digits[a], digits[b], strict=True)))

    def mul(a, b):
        return sum(
            sum(digits[a][j] * digits[b][i-j] for j in range(i+1)) % p * p**i
            for i in range(degree)
        )

    return Ring(f"F{p}[e]/(e^{degree})", size, add, mul, p, lambda a: a % p)


def multiply_columns(ring, left, right):
    degree = len(left)
    return tuple(
        ring_sum(ring, (ring.mul[left[i]][right[k-i]] for i in range(k+1)))
        for k in range(degree)
    )


def ring_sum(ring, values):
    total = 0
    for value in values:
        total = ring.add[total][value]
    return total


@cache
def determinant_terms(degree):
    return tuple(
        (permutation, sum(a > b for i, a in enumerate(permutation)
                          for b in permutation[i+1:]) % 2)
        for permutation in permutations(range(degree))
    )


def determinant(ring, columns):
    degree = len(columns)
    total = 0
    for permutation, odd in determinant_terms(degree):
        value = 1
        for column, row in enumerate(permutation):
            value = ring.mul[value][columns[column][row]]
            if not value:
                break
        if odd:
            value = ring.neg[value]
        total = ring.add[total][value]
    return total


def check(ring, degree):
    exponent = comb(degree, 2)
    powers = [ring.power(a, exponent) for a in range(ring.size)]
    images = set()
    unit_images = set()
    translations = 0
    substitutions = 0
    one = (1,) + (0,) * (degree - 1)
    zero = (0,) * degree
    basis = [
        (0,) * i + (1,) + (0,) * (degree - 1 - i) for i in range(degree)
    ]
    for f in product(range(ring.size), repeat=degree):
        columns = [one]
        for _ in range(degree):
            columns.append(multiply_columns(ring, columns[-1], f))
        det = determinant(ring, columns[:-1])
        assert det == powers[f[1]], (ring.name, degree, f)
        substitutions += 1
        if columns[-1] == zero and det in ring.units:
            images.add(det)
            translations += f[0] != 0
        if f[0] in ring.units:
            mul_columns = [multiply_columns(ring, f, basis_vector)
                           for basis_vector in basis]
            unit_images.add(determinant(ring, mul_columns))
    assert images == {ring.power(a, exponent) for a in ring.units}
    assert unit_images == {ring.power(a, degree) for a in ring.units}
    order = len(ring.units)
    count = ((order // len(unit_images)) ** 2) * (order // len(images))
    return substitutions, translations, count


def check_principal_probes(ring):
    p = ring.p
    principal = {u for u in ring.units if ring.residue(u) == 1}
    distinct_images = set()
    for j in range(6):
        degree = 1 + 2 * (p - 1) * p**j
        assert {ring.power(u, degree) for u in ring.units} == ring.units
        image = {ring.power(u, comb(degree, 2)) for u in ring.units}
        assert image == {ring.power(u, p**j) for u in principal}
        torsion = sum(ring.power(u, p**j) == 1 for u in principal)
        assert len(ring.units) // len(image) == (p - 1) * torsion
        frozen_image = frozenset(image)
        if len(principal) > 1 and frozen_image not in distinct_images:
            for shorter in range(2, degree):
                unit_image = {ring.power(u, shorter) for u in ring.units}
                if unit_image == ring.units:
                    assert {ring.power(u, comb(shorter, 2)) for u in ring.units} != image
            distinct_images.add(frozen_image)
    return len(distinct_images)


def main():
    rings = (
        modular(4, 2), modular(8, 2), modular(9, 3), modular(6),
        truncated_field(2, 2), truncated_field(2, 3), truncated_field(2, 4),
        truncated_field(3, 2),
    )
    substitutions = translations = count = sharp = 0
    for ring in rings:
        if ring.p:
            sharp += check_principal_probes(ring)
        degrees = (2, 3) if ring.size > 9 else (2, 3, 4)
        for degree in degrees:
            n, t, orbit_count = check(ring, degree)
            substitutions += n
            translations += t
            count += 1
            print(f"{ring.name}, d={degree}: {orbit_count} determinant-one classes")
    print(f"{count} cases, {substitutions} substitutions, {translations} invertible "
          f"substitutions with nonzero constant term, 42 principal subgroup tests, and {sharp} sharp lengths.")


if __name__ == "__main__":
    main()
