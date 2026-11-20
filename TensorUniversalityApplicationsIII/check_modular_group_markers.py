from itertools import product
from math import comb, gcd


def generator_rank(matrix, prime, exponent):
    modulus = prime ** exponent
    matrix = [[value % modulus for value in row] for row in matrix]
    rows, cols = len(matrix), len(matrix[0])

    def valuation(value):
        if not value:
            return exponent
        power = 0
        while value % prime == 0:
            power += 1
            value //= prime
        return power

    for k in range(min(rows, cols)):
        power, i, j = min((valuation(matrix[i][j]), i, j)
                          for i in range(k, rows) for j in range(k, cols))
        if power == exponent:
            return k
        matrix[i], matrix[k] = matrix[k], matrix[i]
        for row in matrix:
            row[j], row[k] = row[k], row[j]
        pivot = prime ** power
        inverse = pow(matrix[k][k] // pivot, -1, modulus)
        matrix[k] = [value * inverse % modulus for value in matrix[k]]
        for i in range(k + 1, rows):
            factor = matrix[i][k] // pivot
            matrix[i] = [(a - factor * b) % modulus for a, b in zip(matrix[i], matrix[k])]
        # Clearing the pivot row by column operations leaves the lower submatrix unchanged.
    return min(rows, cols)


def image(matrix, modulus):
    columns = [column for column in zip(*matrix) if any(column)]
    return {tuple(sum(λ * value for λ, value in zip(coefficients, row)) % modulus
                  for row in zip(*columns))
            for coefficients in product(range(modulus), repeat=len(columns))} if columns else {
                (0,) * len(matrix)
            }


def core_slice(data, markers, modulus):
    coordinates = [[0] * 6 for _ in range(6)]
    for i, j, value in [(0, 1, data), (0, 2, markers[0]), (0, 3, markers[1]),
                        (1, 4, markers[2]), (1, 5, markers[3])]:
        coordinates[i][j] = value % modulus
        coordinates[j][i] = -value % modulus
    return coordinates


def local_controls():
    rank_checks = 0
    for prime, exponent in [(2, 1), (2, 2), (3, 2)]:
        modulus = prime ** exponent
        for a, b, c, d in product(range(modulus), repeat=4):
            matrix = ((a, b), (c, d))
            torsion = sum(all(prime * v % modulus == 0 for v in w) for w in image(matrix, modulus))
            assert torsion == prime ** generator_rank(matrix, prime, exponent)
            rank_checks += 1

    band_checks = 0
    core_dim = 6
    weights = [2 * (6 + i) * (core_dim + 1) for i in range(4)]
    for prime, exponent in [(2, 1), (2, 2), (2, 3), (3, 2)]:
        modulus = prime ** exponent
        for coefficient in range(modulus):
            rank = generator_rank(((0, coefficient), (-coefficient, 0)), prime, exponent)
            assert rank == 2 * bool(coefficient)
        coefficients = sorted({0, 1, prime % modulus, modulus - 1})
        for data, *markers in product(coefficients, repeat=5):
            rank = generator_rank(core_slice(data, markers, modulus), prime, exponent)
            score = rank + sum(weight for weight, value in zip(weights, markers) if value)
            support = {i for i, value in enumerate(markers) if value}
            assert (score <= core_dim) == (not support)
            for i, weight in enumerate(weights):
                assert (weight <= score <= weight + core_dim) == (support == {i})
            band_checks += 1
    return rank_checks, band_checks


def paired_intersection_controls():
    checks = 0
    for modulus in (2, 3, 4, 6, 8, 9):
        units = [c for c in range(modulus) if gcd(c, modulus) == 1]
        coefficients = sorted({0, 1, modulus // 2, modulus - 1})
        for i in (0, 2):
            good = {tuple(value if coordinate == i // 2 else 0 for coordinate in range(6))
                    for value in range(modulus)}
            first = {(data, unit): image(core_slice(data, [unit if j == i else 0 for j in range(4)],
                                                  modulus), modulus)
                     for data, unit in product(coefficients, units)}
            second = {(data, unit): image(core_slice(data, [unit if j == i+1 else 0 for j in range(4)],
                                                   modulus), modulus)
                      for data, unit in product(coefficients, units)}
            for left, right in product(first.values(), second.values()):
                assert left & right == good
                checks += 1
    return checks


def group_controls():
    checks = 0
    for modulus in (2, 3, 4, 6, 8, 9, 10, 12):
        scale = 1 if modulus % 2 else 2
        central_modulus = scale * modulus

        def multiply(a, b):
            x, y, z = a
            u, v, w = b
            return (x + u) % modulus, (y + v) % modulus, (z + w + scale*x*v) % central_modulus

        def inverse(a):
            x, y, z = a
            return -x % modulus, -y % modulus, (-z + scale*x*y) % central_modulus

        identity = (0, 0, 0)
        for x, y in product(range(modulus), repeat=2):
            lift = (x, y, 0)
            assert multiply(lift, inverse(lift)) == identity
            for vector in ((1, 0, 0), (0, 1, 0)):
                bracket = multiply(multiply(multiply(inverse(lift), inverse(vector)), lift), vector)
                expected = scale * (x * vector[1] - y * vector[0])
                assert bracket == (0, 0, expected % central_modulus)
            uncorrected_carry = comb(modulus, 2) * scale*x*y
            assert uncorrected_carry % modulus == 0
            first = (x, y, -(uncorrected_carry // modulus) % central_modulus)
            power = identity
            for _ in range(modulus):
                power = multiply(power, first)
            assert power == identity
            checks += 1
    return checks


if __name__ == '__main__':
    ranks, bands = local_controls()
    intersections = paired_intersection_controls()
    lifts = group_controls()
    print(f'PASS: {ranks} image ranks, {bands} rank bands, '
          f'{intersections} paired intersections and {lifts} central power adjustments')
