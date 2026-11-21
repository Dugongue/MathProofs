"""Exact finite checks for local charts and their represented modules."""

from functools import reduce
from itertools import permutations, product
from operator import xor


def one(n):
    return tuple(1 << i for i in range(n))


def matrix_unit(n, i, j):
    return tuple(1 << j if a == i else 0 for a in range(n))


def matrix_add(a, b):
    return tuple(x ^ y for x, y in zip(a, b))


def matrix_mul(a, b):
    return tuple(reduce(xor, (b[i] for i in range(len(b)) if row & (1 << i)), 0)
                 for row in a)


def rank(a):
    basis = {}
    for row in a:
        while row:
            pivot = row.bit_length()
            if pivot not in basis:
                basis[pivot] = row
                break
            row ^= basis[pivot]
    return len(basis)


def simultaneous(a, b, change):
    return all(matrix_mul(change, x) == matrix_mul(y, change) for x, y in zip(a, b))


def square_zero_control():
    identity = one(3)
    x, y = matrix_unit(3, 0, 1), matrix_unit(3, 0, 2)
    x_dual, y_dual = matrix_unit(3, 1, 0), matrix_unit(3, 2, 0)
    swap = (4, 2, 1)
    source = (identity, matrix_add(identity, x), matrix_add(identity, y))
    positive = tuple(matrix_mul(swap, matrix_mul(a, swap)) for a in source)
    negative = (identity, matrix_add(identity, x_dual), matrix_add(identity, y_dual))
    gl = [a for a in product(range(8), repeat=3) if rank(a) == 3]
    assert len(gl) == 168
    assert [rank(a) for a in (x, y, matrix_add(x, y))] == [1, 1, 1]
    assert [rank(a) for a in (x_dual, y_dual, matrix_add(x_dual, y_dual))] == [1, 1, 1]
    assert all(matrix_mul(a, a) == identity for a in source + positive + negative)
    # A part-preserving K_{2,3} alignment permutes paths and may swap the
    # two left vertices. All path gains are involutions in these fixtures.
    totals = []
    for target in (positive, negative):
        hits = 0
        for order in permutations(range(3)):
            reference, a, b = (target[i] for i in order)
            rooted = (matrix_mul(reference, a), matrix_mul(reference, b))
            hits += 2 * sum(simultaneous(source[1:], rooted, c) for c in gl)
        totals.append(hits)
    assert totals[0] > 0 and totals[1] == 0
    print(f"Square-zero pair: {totals[0]} positive and {totals[1]} negative "
          "alignment-switch matches over 12 × 168 checks per pair.")


def truncated_mul(a, b, m):
    return reduce(xor, ((b << i) for i in range(m) if a & (1 << i)), 0) & ((1 << m) - 1)


def columns_to_matrix(columns):
    return tuple(sum((1 << j) for j, col in enumerate(columns) if col & (1 << i))
                 for i in range(len(columns)))


def power(a, k, m):
    value = 1
    for _ in range(k):
        value = truncated_mul(value, a, m)
    return value


def multiplication(a, m):
    return columns_to_matrix([truncated_mul(a, 1 << j, m) for j in range(m)])


def power_ranks(matrix):
    a = matrix
    result = []
    for _ in matrix:
        result.append(rank(a))
        a = matrix_mul(a, matrix)
    return result


def depth_control():
    m = 5
    t, t_squared, t_cubed = 2, 4, 8
    identity = one(m)
    parameter = t ^ t_squared
    change = columns_to_matrix([power(parameter, j, m) for j in range(m)])
    assert rank(change) == m
    source = [multiplication(1 ^ t, m), multiplication(1 ^ t_squared, m)]
    positive = [multiplication(1 ^ parameter, m),
                multiplication(1 ^ truncated_mul(parameter, parameter, m), m)]
    negative = [source[0], multiplication(1 ^ t_squared ^ t_cubed, m)]
    assert simultaneous(source, positive, change)
    assert power_ranks(matrix_add(source[1], identity)) == power_ranks(
        matrix_add(negative[1], identity)
    )
    mark = matrix_add(source[0], identity)
    assert matrix_mul(mark, mark) == matrix_add(source[1], identity)
    assert matrix_mul(mark, mark) != matrix_add(negative[1], identity)
    # The eighth power is the intrinsic residue projection on this ring.
    assert all(power(a, 8, m) == (a & 1) for a in range(1 << m))
    print("Depth five: chart substitution passes, a same-rank mutant fails, "
          "and all 32 Frobenius residue checks pass.")


if __name__ == "__main__":
    square_zero_control()
    depth_control()
