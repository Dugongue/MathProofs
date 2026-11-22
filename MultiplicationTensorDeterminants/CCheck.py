"""Direct prime-field controls for determinant images of pure-power quotients."""

from itertools import product
from math import comb, gcd, prod


def determinant(columns, p):
    """Return the determinant of the matrix whose columns are supplied."""
    matrix = [list(row) for row in zip(*columns, strict=True)]
    value = 1
    for column in range(len(matrix)):
        pivot = next((row for row in range(column, len(matrix))
                      if matrix[row][column] % p), None)
        if pivot is None:
            return 0
        if pivot != column:
            matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
            value = -value
        entry = matrix[column][column] % p
        value = value * entry % p
        inverse = pow(entry, -1, p)
        for row in range(column + 1, len(matrix)):
            factor = matrix[row][column] * inverse % p
            if factor:
                for index in range(column + 1, len(matrix)):
                    matrix[row][index] = (
                        matrix[row][index] - factor * matrix[column][index]
                    ) % p
    return value % p


class Quotient:
    def __init__(self, prime, degrees):
        self.p = prime
        self.degrees = degrees
        self.basis = list(product(*(range(d) for d in degrees)))
        self.one = {(0,) * len(degrees): 1}
        self.directions = [tuple(int(i == j) for i in range(len(degrees)))
                           for j in range(len(degrees))]

    def multiply(self, x, y):
        result = {}
        for i, a in x.items():
            for j, b in y.items():
                ij = tuple(u + v for u, v in zip(i, j, strict=True))
                if all(r < d for r, d in zip(ij, self.degrees, strict=True)):
                    result[ij] = (result.get(ij, 0) + a * b) % self.p
        return {e: c for e, c in result.items() if c}

    def vector(self, polynomial):
        return [polynomial.get(exponents, 0) for exponents in self.basis]

    def powers(self, polynomial, end):
        rows = [self.one]
        for _ in range(end):
            rows.append(self.multiply(rows[-1], polynomial))
        return rows

    def substitution_determinant(self, values):
        rows = [self.powers(value, degree - 1)
                for value, degree in zip(values, self.degrees, strict=True)]
        columns = []
        for exponents in self.basis:
            polynomial = self.one
            for row, exponent in zip(rows, exponents, strict=True):
                polynomial = self.multiply(polynomial, row[exponent])
            columns.append(self.vector(polynomial))
        return determinant(columns, self.p)

    def digit_test(self, values, degree):
        """Test for a surviving admissible multinomial without polynomial products."""
        for exponents in self.basis:
            if sum(exponents) != degree:
                continue
            if any(e and not c for e, c in zip(exponents, values, strict=True)):
                continue
            remainder = degree
            digits = exponents
            while remainder:
                if remainder % self.p != sum(e % self.p for e in digits):
                    break
                remainder //= self.p
                digits = tuple(e // self.p for e in digits)
            else:
                return False
        return True


def subgroup(generators, prime):
    values = {1}
    for g in generators:
        generated = values.copy()
        power = g
        while power != 1:
            generated.update(value * power % prime for value in values)
            power = power * g % prime
        values = generated
    return values


def predicted(prime, degrees):
    dimension = prod(degrees)
    exponents = [dimension * (d - 1) // 2 for d in degrees]
    generators = [pow(a, e, prime) for a in range(1, prime) for e in exponents]
    swap_signs = [pow(-1, dimension // (d * d) * comb(d, 2), prime)
                  for d in set(degrees) if degrees.count(d) >= 2]
    group = subgroup(generators + swap_signs, prime)
    expected_index = gcd(prime - 1, *exponents)
    evens = [d for d in degrees if d % 2 == 0]
    if (prime % 4 == 3 and len(evens) == 2 and
            evens[0] == evens[1] and evens[0] % 4 == 2):
        expected_index //= 2
    assert expected_index * len(group) == prime - 1
    return group


def check(prime, degrees):
    quotient = Quotient(prime, degrees)
    columns = []
    all_linear_vectors = list(product(range(prime), repeat=len(degrees)))
    comparisons = 0
    for degree in degrees:
        accepted = []
        for column in all_linear_vectors:
            image = {e: c for e, c in zip(quotient.directions, column, strict=True) if c}
            vanishes = not quotient.powers(image, degree)[-1]
            assert vanishes == quotient.digit_test(column, degree), (prime, degrees, column)
            comparisons += 1
            if vanishes and image:
                accepted.append((column, image))
        columns.append(accepted)
    determinants = set()
    linear_count = 0
    nonlinear_count = 0
    for selection in product(*columns):
        vectors, images = zip(*selection, strict=True)
        if determinant(vectors, prime) == 0:
            continue
        computed = quotient.substitution_determinant(images)
        assert computed, (prime, degrees, vectors)
        determinants.add(computed)
        linear_count += 1
        # In this quotient xy is the only higher-degree monomial.
        if degrees == (2, 2):
            for left, right in product(range(prime), repeat=2):
                lifts = [image.copy() for image in images]
                lifts[0][(1, 1)] = left
                lifts[1][(1, 1)] = right
                assert all(not quotient.powers(lift, 2)[-1] for lift in lifts)
                assert quotient.substitution_determinant(lifts) == computed
                nonlinear_count += 1
    assert determinants == predicted(prime, degrees), (prime, degrees, determinants)
    exponent = prod(degrees)
    orbit_count = gcd(exponent, prime - 1) ** 2 * ((prime - 1) // len(determinants))
    return comparisons, linear_count, nonlinear_count, orbit_count


def main():
    cases = (
        (2, (2, 2)), (2, (2, 2, 2)), (2, (2, 4)), (2, (4, 4)),
        (2, (3, 6)), (2, (6, 6)), (3, (2, 2)), (3, (2, 3)),
        (3, (3, 3)), (3, (3, 6)), (3, (6, 6)), (3, (2, 3, 3)),
        (5, (2, 2)), (5, (3, 3)), (5, (5, 5)), (7, (2, 2)),
        (7, (2, 2, 3)), (7, (3, 3)), (7, (6, 6)), (11, (2, 4)),
    )
    totals = [0, 0, 0]
    for prime, degrees in cases:
        probes, linear, nonlinear, orbits = check(prime, degrees)
        totals = [x + y for x, y in zip(totals, (probes, linear, nonlinear), strict=True)]
        print(f"F_{prime} {degrees}: {linear} graded automorphisms, {orbits} SL orbit classes")
    print(f"{len(cases)} cases, {totals[0]} digit tests, {totals[1]} graded determinants, "
          f"{totals[2]} full lift determinants.")


if __name__ == "__main__":
    main()
