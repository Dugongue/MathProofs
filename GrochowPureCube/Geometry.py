"""Finite controls for the characteristic-three pure-cube geometry note."""

from itertools import product


def add(left, right):
    terms = dict(left)
    for exponent, coefficient in right.items():
        value = (terms.get(exponent, 0) + coefficient) % 3
        if value:
            terms[exponent] = value
        elif exponent in terms:
            del terms[exponent]
    return terms


def multiply(left, right):
    terms = {}
    for u, a in left.items():
        for v, b in right.items():
            exponent = tuple(x + y for x, y in zip(u, v))
            terms = add(terms, {exponent: a * b})
    return terms


def scaled(polynomial, coefficient):
    return {exponent: coefficient * value % 3
            for exponent, value in polynomial.items() if coefficient * value % 3}


def determinant(matrix):
    (a, b, c), (d, e, f), (g, h, i) = matrix
    return (a * (e * i - f * h) - b * (d * i - f * g)
            + c * (d * h - e * g)) % 3


X, Y, Z = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
CUBES = ((3, 0, 0), (0, 3, 0), (0, 0, 3))
POLAR = {(2, 1, 0): 1}


def linear(row):
    return {monomial: coefficient for monomial, coefficient in zip((X, Y, Z), row)
            if coefficient}


def pure_tuple(polynomial):
    return tuple(polynomial.get(exponent, 0) for exponent in CUBES)


def mixed_terms(polynomial):
    return {exponent: coefficient for exponent, coefficient in polynomial.items()
            if exponent not in CUBES}


def orbit_control():
    split_fiber = set()
    nonsplit_fiber = set()
    invertible = 0
    for entries in product(range(3), repeat=9):
        matrix = tuple(entries[offset:offset + 3] for offset in range(0, 9, 3))
        if determinant(matrix) == 0:
            continue
        invertible += 1
        x, y, z = (linear(row) for row in matrix)
        base = multiply(multiply(x, x), y)
        if mixed_terms(base) != POLAR:
            continue
        split_fiber.add(pure_tuple(base))
        z_cube = {exponent: coefficient for exponent, coefficient in zip(CUBES, matrix[2])
                  if coefficient}
        nonsplit_fiber.add(pure_tuple(add(base, z_cube)))
    assert invertible == 11232
    assert split_fiber == {(a, 0, 0) for a in range(3)}
    assert nonsplit_fiber == set(product(range(3), range(3), (1, 2)))
    return invertible, len(split_fiber), len(nonsplit_fiber)


def dual_number_control():
    cubic, polar, relative = 0, 0, 0
    for entries in product(range(3), repeat=9):
        # The first-order term of (x + eps*a)^2 (y + eps*b) is
        # 2*x*y*a + x^2*b. Every pure cube kills the eps term.
        a, b = linear(entries[:3]), linear(entries[3:6])
        first_order = add(scaled(multiply({(1, 1, 0): 1}, a), 2),
                          multiply({(2, 0, 0): 1}, b))
        if not mixed_terms(first_order):
            polar += 1
        if not first_order:
            cubic += 1
            if not any(entries[:6]):
                relative += 1
    assert (cubic, polar, relative) == (81, 243, 27)
    return cubic, polar, relative


def plane_control():
    # There are four lines in x=0, and each gives an x^3 quotient.
    lines = {(0, a, b) for a, b in product(range(3), repeat=2)
             if (a, b) != (0, 0) and (a == 1 or (a == 0 and b == 1))}
    assert len(lines) == 4
    for _, a, b in lines:
        complementary = (0, 1) if a else (1, 0)
        assert (a * complementary[1] - b * complementary[0]) % 3
    return len(lines)


if __name__ == "__main__":
    print("Invertible substitutions and fixed-polarization fiber sizes:", orbit_control())
    print("Dual-number lifts for the cubic, polarization, and fixed quotient:",
          dual_number_control())
    print("Rational lines in the zero-branch incidence control:", plane_control())
