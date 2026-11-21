"""Exact small controls for the determinant-coset and projective-frame proofs."""

from itertools import permutations, product


def determinant(matrix, p):
    d = len(matrix)
    value = 0
    for perm in permutations(range(d)):
        inversions = sum(perm[i] > perm[j] for i in range(d) for j in range(i + 1, d))
        term = (-1) ** inversions
        for i, j in enumerate(perm):
            term *= matrix[i][j]
        value += term
    return value % p


def square_matrices(d, p):
    for flat in product(range(p), repeat=d * d):
        yield tuple(flat[i:i + d] for i in range(0, d * d, d))


def multiply(left, right, p):
    return tuple(tuple(sum(a * b for a, b in zip(row, column)) % p
                       for column in zip(*right)) for row in left)


def check_norm():
    p = 5
    companion = ((0, 2), (1, 0))  # x^2 - 2 is irreducible over F_5.
    values = set()
    units = 0
    for matrix in square_matrices(2, p):
        det = determinant(matrix, p)
        if det and multiply(matrix, companion, p) == multiply(companion, matrix, p):
            units += 1
            values.add((det, det))
    assert units == 24
    assert values == {(u, u) for u in range(1, p)}
    return units, len(values)


def check_projective_coset():
    p = 5
    actual = set()
    for a, scalar in product(range(1, p), repeat=2):
        for b in square_matrices(2, p):
            # The two slices are the coordinate columns of F_5^2.
            if b[0][0] == b[1][1] == scalar * a % p and b[0][1] == b[1][0] == 0:
                actual.add((a, determinant(b, p), scalar ** 2 % p))
    predicted = {(u, (u * t) ** 2 % p, t ** 2 % p)
                 for u, t in product(range(1, p), repeat=2)}
    assert actual == predicted and len(actual) == 8
    return len(actual)


def check_frame():
    p = 3
    target = ((1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1))
    witness = ((1, 1, 0), (0, 1, 1), (0, 0, 2))
    source = tuple(multiply((row,), witness, p)[0] for row in target)

    def canonical(line):
        first = next(x for x in line if x)
        return tuple(x * pow(first, -1, p) % p for x in line)

    matches = []
    count = 0
    for matrix in square_matrices(3, p):
        det = determinant(matrix, p)
        if det == 0:
            continue
        count += 1
        if all(canonical(multiply((row,), matrix, p)[0]) == canonical(match)
               for row, match in zip(target, source)):
            matches.append(matrix)
    expected = {tuple(tuple(scalar * entry % p for entry in row) for row in witness)
                for scalar in range(1, p)}
    assert count == 11232 and set(matches) == expected
    return count, len(matches)


def poly_multiply(left, right, p):
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] = (result[i + j] + a * b) % p
    return result


def reciprocal_charpoly(matrix, p):
    d = len(matrix)
    out = [0] * (d + 1)
    for perm in permutations(range(d)):
        inversions = sum(perm[i] > perm[j] for i in range(d) for j in range(i + 1, d))
        term = [(-1) ** inversions]
        for i, j in enumerate(perm):
            term = poly_multiply(term, [int(i == j), -matrix[i][j]], p)
        out = [(a + b) % p for a, b in zip(out, term)]
    return out


def check_radical_trace():
    checks = 0
    for p in (2, 3):
        # Regular representation of F_p x F_p[e]/(e^p).
        for value in product(range(p), repeat=p + 1):
            a, b, *tail = value
            local = (b, *tail)
            matrix = tuple(tuple(a if i == j == 0 else local[i - j]
                                 if i >= j >= 1 else 0
                                 for j in range(p + 1))
                           for i in range(p + 1))
            coefficients = reciprocal_charpoly(matrix, p)
            assert coefficients[1] == (-a) % p
            if a == 0:
                assert coefficients[p] == (-b) % p
                assert (coefficients == [1] + [0] * (p + 1)) == (b == 0)
            checks += 1
    return checks


if __name__ == "__main__":
    print("Quadratic norm example, units and determinant pairs:", check_norm())
    print("Rectangular projective example, determinant triples:", check_projective_coset())
    print("Projective frame example, invertible matrices and lifts:", check_frame())
    print("Modular regular trace controls:", check_radical_trace())
