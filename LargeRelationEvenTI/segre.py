"""Even conjugators for frame-certified two-factor minor relations over F3.

An endpoint consists of a dense Sym^2 quotient table and an invertible matrix
whose columns are a proposed product frame in the displayed tangent basis.
The frame is verified and may be chosen independently at each endpoint.
"""
from itertools import combinations_with_replacement
from random import Random


def pairs(n):
    return list(combinations_with_replacement(range(n), 2))


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def mul(a, b):
    cols = list(zip(*b))
    return [[sum(x * y for x, y in zip(row, col)) % 3 for col in cols]
            for row in a]


def det(rows):
    n = len(rows)
    if any(len(row) != n for row in rows):
        raise ValueError("determinant requires a square matrix")
    a = [[v % 3 for v in row] for row in rows]
    value = 1
    for j in range(n):
        p = next((i for i in range(j, n) if a[i][j]), None)
        if p is None:
            return 0
        if p != j:
            a[p], a[j] = a[j], a[p]
            value = -value
        pivot = a[j][j]
        value = value * pivot % 3
        for i in range(j + 1, n):
            factor = a[i][j] * pivot % 3
            if factor:
                a[i] = [(x - factor * y) % 3 for x, y in zip(a[i], a[j])]
    return value


def sym_square(frame):
    monomials = pairs(len(frame))
    return [[(frame[i][k] * frame[j][l] +
              (i != j) * frame[j][k] * frame[i][l]) % 3
             for k, l in monomials] for i, j in monomials]


def column_labels(a, b):
    for x, y in pairs(a * b):
        i, j = divmod(x, b)
        k, l = divmod(y, b)
        yield min(i, k), max(i, k), min(j, l), max(j, l)


def reference_table(a, b):
    labels = list(column_labels(a, b))
    return [[int(label == key) for label in labels] for key in sorted(set(labels))]


def endpoint_sign(a, b, table, frame):
    if a < 2 or b < 2 or a % 4 != 2 or b % 4 != 1:
        raise ValueError("requires factor sizes a = 2 mod 4, b = 1 mod 4")
    n = a * b
    labels = list(column_labels(a, b))
    keys = sorted(set(labels))
    if len(frame) != n or any(len(row) != n for row in frame):
        raise ValueError("wrong product frame dimension")
    if len(table) != len(keys) or any(len(row) != len(labels) for row in table):
        raise ValueError("wrong dense quotient table dimension")
    ds = det(frame)
    if not ds:
        raise ValueError("singular frame")
    adapted = list(zip(*mul(table, sym_square(frame))))
    columns = {}
    for key, col in zip(labels, adapted):
        if key in columns and columns[key] != col:
            raise ValueError("the frame does not satisfy the minor relations")
        columns[key] = col
    # Transposition does not change the determinant.
    dz = det([columns[key] for key in keys])
    if not dz:
        raise ValueError("straightened images do not form an output basis")
    return ds * dz % 3


ONE = (((1,),),)
ZERO = (((0,),),)


def compile_even(a, b, source_table, source_frame, target_table, target_frame):
    left = endpoint_sign(a, b, source_table, source_frame)
    right = endpoint_sign(a, b, target_table, target_frame)
    return ONE, ONE if left == right else ZERO


def scramble(n, sign, rng):
    matrix = identity(n)
    inverse = identity(n)
    for _ in range(3 * n):
        i, j = rng.sample(range(n), 2)
        s = rng.choice((1, 2))
        matrix[i] = [(x + s * y) % 3 for x, y in zip(matrix[i], matrix[j])]
        for row in inverse:
            row[j] = (row[j] - s * row[i]) % 3
    if sign == 2:
        matrix[0] = [-x % 3 for x in matrix[0]]
        for row in inverse:
            row[0] = -row[0] % 3
    return matrix, inverse


def tensor_matrix(p, q):
    return [[x * y % 3 for x in row for y in subrow]
            for row in p for subrow in q]


def controls():
    rng = Random(314159)
    a, b = 2, 5
    n = a * b
    table = reference_table(a, b)
    answers = {True: 0, False: 0}
    for input_sign in (1, 2):
        for output_sign in (1, 2):
            g, gi = scramble(n, input_sign, rng)
            h, _ = scramble(len(table), output_sign, rng)
            target = mul(mul(h, table), sym_square(gi))
            for extra_input_sign in (1, 2):
                p, _ = scramble(a, extra_input_sign, rng)
                q, _ = scramble(b, 2, rng)
                target_frame = mul(g, tensor_matrix(p, q))
                left, right = compile_even(a, b, table, identity(n),
                                            target, target_frame)
                answer = left == right
                assert answer == (input_sign == output_sign)
                answers[answer] += 1
    damaged = [row[:] for row in table]
    labels = list(column_labels(a, b))
    duplicate = next(i for i, key in enumerate(labels) if key in labels[:i])
    damaged[0][duplicate] = (damaged[0][duplicate] + 1) % 3
    try:
        endpoint_sign(a, b, damaged, identity(n))
    except ValueError:
        pass
    else:
        raise AssertionError("invalid product frame was accepted")
    print(f"Hidden-factor controls: {answers[True]} even, {answers[False]} odd-only, "
          "one invalid certificate rejected.")


if __name__ == "__main__":
    controls()
