"""Exact F3 checks of the triangular four-class sign formulas."""

from itertools import product
from random import Random


def det(matrix):
    rows = [list(row) for row in matrix]
    value = 1
    for j in range(len(rows)):
        pivot = next((i for i in range(j, len(rows)) if rows[i][j] % 3), None)
        if pivot is None:
            return 0
        if pivot != j:
            rows[pivot], rows[j] = rows[j], rows[pivot]
            value = -value
        diagonal = rows[j][j] % 3
        value = (value * diagonal) % 3
        for i in range(j + 1, len(rows)):
            multiplier = rows[i][j] * diagonal % 3
            if multiplier:
                rows[i][j:] = [(left - multiplier * right) % 3
                               for left, right in zip(rows[i][j:], rows[j][j:], strict=True)]
    return value % 3


def vector(length, index):
    return tuple(int(k == index) for k in range(length))


def multiply(left, right):
    length = len(left)
    return tuple(sum(left[j] * right[i-j] for j in range(i + 1)) % 3
                 for i in range(length))


def add(left, right):
    return tuple((x + y) % 3 for x, y in zip(left, right, strict=True))


def random_polynomial(rng, length, constant=None):
    coefficients = [rng.randrange(3) for _ in range(length)]
    if constant is not None:
        coefficients[0] = constant
    return tuple(coefficients)


def invertible_random(rng, dim):
    while True:
        matrix = [[rng.randrange(3) for _ in range(dim)] for _ in range(dim)]
        if det(matrix):
            return matrix


def lifted_matrix(rng, length, rank):
    return [[random_polynomial(rng, length, c) for c in row]
            for row in invertible_random(rng, rank)]


def eval_polynomial_matrix(matrix, vector_list):
    n = len(vector_list[0])
    result = []
    for row in matrix:
        value = (0,) * n
        for coefficient, operand in zip(row, vector_list, strict=True):
            value = add(value, multiply(coefficient, operand))
        result.append(value)
    return result


def flatten(vector_list):
    return tuple(sum((list(entry) for entry in vector_list), []))


def matrix_of(transform, blocks, length):
    columns = [flatten(transform([vector(length, j) if k == which else (0,) * length
                                 for k in range(blocks)]))
               for which in range(blocks) for j in range(length)]
    return list(zip(*columns, strict=True))


def check_grade_actions(rng, length):
    check_count = 0
    for _ in range(10):
        lift = lifted_matrix(rng, length, 2)
        field_matrix = [[entry[0] for entry in row] for row in lift]
        actual = matrix_of(lambda values: eval_polynomial_matrix(lift, values), 2, length)
        assert det(actual) == pow(det(field_matrix), length, 3) == 1
        check_count += 1

        scalar = rng.choice([1, 2])
        top = invertible_random(rng, 3)
        rows = [top, top]
        off_diagonal = [[random_polynomial(rng, length) for _ in range(2)] for _ in range(8)]

        def act(values):
            result = [tuple(scalar * value % 3 for value in values[j]) for j in range(2)]
            for copy, top_matrix in enumerate(rows):
                for row in top_matrix:
                    result.append(tuple(sum(a * values[2 + 3 * copy + j][i]
                                            for j, a in enumerate(row)) % 3
                                        for i in range(length)))
            from_bottom = eval_polynomial_matrix(off_diagonal, values[8:])
            result = [add(a, b) for a, b in zip(result, from_bottom, strict=True)]
            result.extend(eval_polynomial_matrix(lift, values[8:]))
            return result

        actual = matrix_of(act, 10, length)
        assert det(actual) == 1
        check_count += 1

        # A local algebra isomorphism is repeated on an even number of module copies.
        generator = list(random_polynomial(rng, length, 0))
        generator[1] = rng.choice([1, 2])
        image_powers = [vector(length, 0)]
        for i in range(1, length):
            image_powers.append(multiply(image_powers[-1], generator))
        corner = tuple(zip(*image_powers, strict=True))
        assert det(corner) in (1, 2)
        diagonal_copy = matrix_of(
            lambda xs: [tuple(sum(row[i] * x[i] for i in range(length)) % 3
                              for row in corner) for x in xs], 10, length
        )
        assert det(diagonal_copy) == 1
        check_count += 1

    # The negative top unit scales exactly the first diagonal slot and its
    # two off-diagonal B-valued rows of width two, leaving every other role.
    odd_label_block = 1 + 4 * length
    assert pow(2, odd_label_block, 3) == 2
    assert pow(2, 2 * length, 3) == 1
    return check_count


def check_profiles():
    twists = list(product((0, 1), repeat=3))
    stabilizer = {(0, 0, 0), (1, 0, 0)}
    partners = 0
    for a, b in product(twists, repeat=2):
        displacement = tuple(x ^ y for x, y in zip(a, b, strict=True))
        profile = {tuple(x ^ y for x, y in zip(displacement, k, strict=True))
                   for k in stabilizer}
        assert ((0, 0, 0) in profile) == (a[1:] == b[1:])
        partners += (0, 0, 0) in profile
    assert partners == 16
    return len({a[1:] for a in twists})


if __name__ == "__main__":
    assert __debug__
    rng = Random(20261120)
    tests = sum(check_grade_actions(rng, n) for n in (2, 4, 6, 8))
    classes = check_profiles()
    print(f"{tests} matrix determinant controls passed. Checked all 64 frame pairs and {classes} retained-sign classes.")
