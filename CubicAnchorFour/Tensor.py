"""Exact controls for the mixed lift count and its universal coefficient module."""

from itertools import combinations, combinations_with_replacement, product
from math import comb


P = 3


def compositions(parts, degree):
    if parts == 1:
        return [(degree,)]
    return [(first,) + tail for first in range(degree + 1)
            for tail in compositions(parts - 1, degree - first)]


def add(first, second):
    return tuple(a + b for a, b in zip(first, second))


def rank(vectors):
    pivots = {}
    for vector in vectors:
        vector = [value % P for value in vector]
        for i in range(len(vector)):
            value = vector[i]
            if not value:
                continue
            if i not in pivots:
                inverse = pow(value, -1, P)
                pivots[i] = [entry * inverse % P for entry in vector]
                break
            vector = [(a - value * b) % P for a, b in zip(vector, pivots[i])]
    return len(pivots)


def universal_control(n, degree):
    units = [tuple(int(i == j) for j in range(n)) for i in range(n)]
    coefficients = compositions(n, degree)
    relations = [
        [(i, alpha, 1)] for i in range(n) for alpha in coefficients if not alpha[i]
    ]
    relations += [
        [(i, add(beta, units[i]), 1), (0, add(beta, units[0]), -1)]
        for i in range(1, n) for beta in compositions(n, degree - 1)
    ]

    observed = []
    for ell_degree in range(1, degree + 2):
        monomials = list(product(compositions(n, ell_degree), coefficients))
        indices = {entry: i for i, entry in enumerate(monomials)}
        rows = []
        for shift in compositions(n, ell_degree - 1):
            for relation in relations:
                row = [0] * len(monomials)
                for i, alpha, value in relation:
                    row[indices[add(shift, units[i]), alpha]] += value
                rows.append(row)
        observed.append(len(monomials) - rank(rows))
    expected = [comb(n + degree - ell_degree - 1, degree - ell_degree)
                for ell_degree in range(1, degree + 1)] + [0]
    assert observed == expected

    mixed = list(product(range(n), combinations_with_replacement(coefficients, 2)))
    indices = {entry: i for i, entry in enumerate(mixed)}
    rows = []
    for coefficient in coefficients:
        for relation in relations:
            row = [0] * len(mixed)
            for i, alpha, value in relation:
                row[indices[i, tuple(sorted((alpha, coefficient)))]] += value
            rows.append(row)
    assert rank(rows) == len(mixed)
    return observed


def short_ring_control():
    ring_basis = list(product(range(2), repeat=2))
    binary_quadratics = compositions(2, 2)
    binary_cubics = compositions(2, 3)
    unknowns = list(product(range(len(binary_quadratics) + 2), ring_basis))
    equations = list(product(range(2), binary_cubics, ring_basis))
    eq_idx = {key: i for i, key in enumerate(equations)}
    units = [(1, 0), (0, 1)]

    def lift_count(form):
        columns = []
        for variable, ring_monomial in unknowns:
            col = [0] * len(equations)
            if variable < len(binary_quadratics):
                for i, unit in enumerate(units):
                    col[eq_idx[i, add(binary_quadratics[variable], unit), ring_monomial]] = 1
            else:
                i = variable - len(binary_quadratics)
                for polynomial_monomial, ring_coefficient in form:
                    multiplied = add(ring_monomial, ring_coefficient)
                    if multiplied in ring_basis:
                        col[eq_idx[i, polynomial_monomial, multiplied]] += 1
            columns.append(col)
        return P ** (len(unknowns) - rank(columns))

    f0 = [((3, 0), (1, 0)), ((0, 3), (0, 1))]
    f1 = [((3, 0), (1, 0)), ((2, 1), (0, 1))]
    assert (lift_count(f0), lift_count(f1)) == (9, 27)


def mixed_characteristic_control():
    quadratics = compositions(2, 2)
    ideal = list(product(range(0, 27, 3), range(3)))
    socle = [(value, 0) for value in (0, 9, 18)]

    def multiply_ring(first, second):
        a, b = first
        c, d = second
        return (a * c + 9 * b * d) % 27, (a * d + b * c) % 3

    def nonzero_products(polynomial, coefficient):
        return {
            key: product_ for key, scalar in polynomial.items()
            if (product_ := multiply_ring(scalar, coefficient)) != (0, 0)
        }

    def count(form):
        targets = [nonzero_products(form, coefficient) for coefficient in ideal]
        total = 0
        for data in product(socle, repeat=len(quadratics)):
            multiplicity = 1
            for unit in ((1, 0), (0, 1)):
                negative_xb = {
                    add(exponent, unit): ((-scalar[0]) % 27, 0)
                    for exponent, scalar in zip(quadratics, data) if scalar != (0, 0)
                }
                multiplicity *= targets.count(negative_xb)
            total += multiplicity
        return total

    f0 = {(3, 0): (3, 0), (0, 3): (0, 1)}
    f1 = {(3, 0): (3, 0), (2, 1): (0, 1)}
    assert (count(f0), count(f1)) == (9, 27)


def grassmann_control():
    cubics = compositions(2, 3)
    quadratics = compositions(2, 2)
    multiples = []
    for coeffs in product(range(P), repeat=3):
        multiples.append([
            [sum(coeffs[i] for i, exponent in enumerate(quadratics)
                 if add(exponent, unit) == alpha) for alpha in cubics]
            for unit in ((1, 0), (0, 1))
        ])
    totals = []
    maxima = []
    for w in range(5):
        total = 0
        max_dim = 0
        for pivots in combinations(range(4), w):
            free = [(i, j) for i, pivot in enumerate(pivots)
                    for j in range(pivot + 1, 4) if j not in pivots]
            for values in product(range(P), repeat=len(free)):
                rows = [[int(j == pivot) for j in range(4)] for pivot in pivots]
                for (i, j), value in zip(free, values):
                    rows[i][j] = value

                def contains(vector):
                    return all(
                        (vector[j] - sum(vector[pivot] * rows[i][j]
                                         for i, pivot in enumerate(pivots))) % P == 0
                        for j in range(4)
                    )

                count = sum(all(contains(vector) for vector in pair) for pair in multiples)
                dimension = next(i for i in range(4) if P**i == count)
                max_dim = max(max_dim, dimension)
                total += 1
        totals.append(total)
        maxima.append(max_dim)
    assert totals == [1, 40, 130, 40, 1]
    assert maxima == [0, 0, 1, 2, 3]
    return sum(totals)


for test in ((2, 3), (2, 4), (3, 4)):
    print(f"Universal bidegree profile {test}: {universal_control(*test)}")
short_ring_control()
mixed_characteristic_control()
print("Mixed lift counts in both characteristics: 9 and 27.")
print(f"Checked sharp maxima across {grassmann_control()} subspaces over F3.")
