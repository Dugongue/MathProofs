"""Exact linear algebra controls for the bundle reconstruction."""

from itertools import combinations, product
from random import Random


def add_scaled(row, source, scale, prime):
    for key, value in source.items():
        coefficient = (row.get(key, 0) + scale * value) % prime
        if coefficient:
            row[key] = coefficient
        else:
            row.pop(key, None)


def sparse_rank(rows, prime):
    pivots = {}
    for source in rows:
        row = {key: value % prime for key, value in source.items() if value % prime}
        while row:
            key = min(row)
            if key in pivots:
                add_scaled(row, pivots[key], -row[key], prime)
                continue
            inverse = pow(row[key], -1, prime)
            pivots[key] = {j: value * inverse % prime for j, value in row.items()}
            break
    return len(pivots)


def monomial(left, right):
    return min(left, right), max(left, right)


def multiply(left, right, prime):
    row = {}
    for i, a in left.items():
        for j, b in right.items():
            key = monomial(i, j)
            coefficient = (row.get(key, 0) + a * b) % prime
            if coefficient:
                row[key] = coefficient
            else:
                row.pop(key, None)
    return row


def diagonal_input_space(height, parameter):
    dimension = 4
    repetitions = height + 1
    left_width = dimension * repetitions
    x_anchor, y_anchor, data = {}, {}, {}
    for copy in range(repetitions):
        x_start = copy * dimension
        y_start = left_width + copy * 2 * dimension
        for index in range(dimension):
            x_anchor[x_start + index, y_start + index] = 1
            y_anchor[x_start + index, y_start + dimension + index] = 1
        data[x_start + 2, y_start] = 1
        data[x_start + 3, y_start + 1] = parameter
    return left_width * 3, (x_anchor, y_anchor, data)


def polar_rows(quadric, dimension, prime):
    rows = [dict() for _ in range(dimension)]
    for (i, j), value in quadric.items():
        if i == j:
            rows[i][i] = 2 * value % prime
        else:
            rows[i][j] = value % prime
            rows[j][i] = value % prime
    return rows


def independent_vectors(dimension, count, prime, random):
    vectors = []
    while len(vectors) < count:
        candidate = {i: random.randrange(prime) for i in range(dimension)}
        if sparse_rank([*vectors, candidate], prime) > len(vectors):
            vectors.append(candidate)
    return vectors


def restriction_controls():
    rank_checks = intersection_checks = family_checks = 0
    random = Random(20261121)
    for prime in (2, 3):
        for height in (1, 2):
            for parameter in range(prime):
                dimension, space = diagonal_input_space(height, parameter)
                assert sparse_rank(space, prime) == 3
                assert sparse_rank([{0: 1}, {1: parameter}], prime) == (
                    2 if parameter else 1
                )
                family_checks += 1
                for coefficients in product(range(prime), repeat=3):
                    if not any(coefficients):
                        continue
                    combination = {}
                    for scale, quadric in zip(coefficients, space):
                        add_scaled(combination, quadric, scale, prime)
                    assert sparse_rank(polar_rows(combination, dimension, prime), prime) >= (
                        2 * (height + 1)
                    )
                    rank_checks += 1
                for count in range(1, height + 1):
                    for _ in range(3):
                        basis = independent_vectors(dimension, count, prime, random)
                        products = [
                            multiply(vector, {i: 1}, prime)
                            for vector in basis
                            for i in range(dimension)
                        ]
                        expected_rank = count * dimension - count * (count - 1) // 2
                        assert sparse_rank(products, prime) == expected_rank
                        assert sparse_rank([*space, *products], prime) == expected_rank + 3
                        intersection_checks += 1
    return rank_checks, intersection_checks, family_checks


def scalar_rigidity_controls():
    checks = 0
    for prime in (2, 3, 5):
        for dimension in (4, 6):
            quadric = {(i, i + 1): 1 for i in range(0, dimension, 2)}
            assert sparse_rank(polar_rows(quadric, dimension, prime), prime) == dimension
            equations = []
            for i, j in combinations(range(dimension), 2):
                coordinates = {}
                for k in range(dimension):
                    for variable, scalar, product_key in (
                        (k * dimension + j, 1, monomial(i, k)),
                        (k * dimension + i, -1, monomial(j, k)),
                    ):
                        remainder = {product_key: scalar}
                        add_scaled(remainder, quadric, -remainder.get((0, 1), 0), prime)
                        for key, value in remainder.items():
                            row = coordinates.setdefault(key, {})
                            row[variable] = value
                equations.extend(coordinates.values())
            assert sparse_rank(equations, prime) == dimension * dimension - 1
            checks += 1
    return checks


if __name__ == "__main__":
    print("Polar ranks, small restrictions, smooth-family generators:",
          restriction_controls())
    print("Scalar rigidity checks:", scalar_rigidity_controls())
