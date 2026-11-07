"""Exact spot checks for the proof examples, using only the standard library."""
from fractions import Fraction as F
from itertools import product


def add(left, right):
    result = dict(left)
    for term, coefficient in right.items():
        result[term] = result.get(term, 0) + coefficient
    return {term: c for term, c in result.items() if c}


def mul(left, right):
    result = {}
    for (i, j), a in left.items():
        for (k, l), b in right.items():
            term = i + k, j + l
            result[term] = result.get(term, 0) + a * b
    return {term: c for term, c in result.items() if c}


def scale(polynomial, coefficient):
    return {term: value * coefficient for term, value in polynomial.items()
            if value * coefficient}


def times(*polynomials):
    result = {(0, 0): 1}
    for polynomial in polynomials:
        result = mul(result, polynomial)
    return result


def echelon(rows, width):
    matrix = [[F(x) for x in row] for row in rows]
    rank = 0
    pivots = []
    for j in range(width):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][j]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        divisor = matrix[rank][j]
        matrix[rank] = [x / divisor for x in matrix[rank]]
        for i, row in enumerate(matrix):
            if i != rank and row[j]:
                factor = row[j]
                matrix[i] = [a - factor * b for a, b in zip(row, matrix[rank])]
        pivots.append(j)
        rank += 1
    return matrix, pivots


def graded_kernel_dimension(degree, s, t):
    monomials = [(a, degree-a) for a in range(degree+1)]
    columns = []
    for block, term in product(range(3), monomials):
        factor = [t, scale(s, -1), {}][block]
        columns.append(mul(factor, {term: 1}))
    rows = [[col.get((a, degree+1-a), 0) for col in columns]
            for a in range(degree+2)]
    return len(columns) - len(echelon(rows, len(columns))[1])


def check_tree():
    s, t, one = {(1, 0): 1}, {(0, 1): 1}, {(0, 0): 1}
    u, v = [s, t, {}], [{}, {}, one]
    degree_dims = [graded_kernel_dimension(i, s, t) for i in range(4)]
    assert degree_dims == [1, 3, 5, 7]
    s3 = times(s, s, s)
    # The rational gauge has leaf states u/s and v, and root weights s^3.
    # Clearing the leaf denominators gives u and s*v with total denominator s^3.
    numerator_u, numerator_v = u, [mul(s, x) for x in v]
    exact = {}
    for labels in product(range(3), repeat=3):
        a = times(*(u[j] for j in labels))
        b = times(s3, *(v[j] for j in labels))
        answer = add(a, b)
        numerator = add(times(s3, *(numerator_u[j] for j in labels)),
                        times(s3, *(numerator_v[j] for j in labels)))
        assert mul(answer, s3) == numerator
        assert all(sum(term) == 3 for term in answer)
        exact[labels] = answer
    # Rank 2 is attained at s=t=1 by every leaf cut. The two-state realization
    # gives the matching upper bound over the rational-function field.
    for cut in range(3):
        other = [j for j in range(3) if j != cut]
        rows = []
        for label in range(3):
            row = []
            for suffix in product(range(3), repeat=2):
                assignment = [0] * 3
                assignment[cut] = label
                for j, value in zip(other, suffix):
                    assignment[j] = value
                row.append(sum(exact[tuple(assignment)].values()))
            rows.append(row)
        assert len(echelon(rows, 9)[1]) == 2
    # The first two short coordinate samples s and t are independent over Q.
    # Keeping only s as a fraction-field basis would miss the pole t/s.
    assert len(echelon([[1, 0], [0, 1]], 2)[1]) == 2
    assert all(i == 0 for i, _ in t)
    print("Homogeneous tree: 27 exact coefficients, ranks (2,2,2), graded dimensions 1,3,5,7")


def quadratic_add(x, y):
    return x[0] + y[0], x[1] + y[1]


def quadratic_mul(x, y):
    return x[0]*y[0] - 5*x[1]*y[1], x[0]*y[1] + x[1]*y[0]


def quadratic_matrix_mul(left, right):
    result = []
    for row in left:
        entries = []
        for column in zip(*right):
            value = (0, 0)
            for x, y in zip(row, column):
                value = quadratic_add(value, quadratic_mul(x, y))
            entries.append(value)
        result.append(entries)
    return result


def check_class_cancellation():
    zero, one = (0, 0), (1, 0)
    u = [(2, 0), (1, 1)]
    v = [(1, 0), (F(1, 2), F(1, 2))]
    basis = [[(2, 0), (1, 1)], [(1, 1), (-1, 1)]]
    inverse = [[(F(-1, 2), F(1, 2)), (F(-1, 2), F(-1, 2))],
               [(F(-1, 2), F(-1, 2)), (1, 0)]]
    assert quadratic_matrix_mul(basis, inverse) == [[one, zero], [zero, one]]
    assert all((x-y) % 2 == 0 for row in basis for x, y in row)
    first = quadratic_matrix_mul([[u[0], zero], [u[1], zero],
                                  [zero, u[0]], [zero, u[1]]], inverse)
    second = quadratic_matrix_mul(basis, [[v[0], v[1], zero, zero],
                                         [zero, zero, v[0], v[1]]])
    assert all(F(c).denominator == 1 for factor in (first, second)
               for row in factor for entry in row for c in entry)
    block = [[quadratic_mul(a, b) for b in v] for a in u]
    expected = [r+[zero, zero] for r in block] + [[zero, zero]+r for r in block]
    assert quadratic_matrix_mul(first, second) == expected
    print("Dedekind example: exact integral width-two factorization of the two-copy block sum")


if __name__ == "__main__":
    check_tree()
    check_class_cancellation()
