"""Exact finite-field controls for the tensor covariant initializer."""

from itertools import combinations, product
from random import Random
import json


def eliminate(matrix, prime, rhs=None):
    size = len(matrix)
    rows = [list(row) for row in matrix]
    if rhs is not None:
        for row, extra in zip(rows, rhs):
            row.extend(extra)
    determinant = 1
    for column in range(size):
        pivot = next((i for i in range(column, size) if rows[i][column]), None)
        if pivot is None:
            return 0, None
        if pivot != column:
            rows[column], rows[pivot] = rows[pivot], rows[column]
            determinant = -determinant
        value = rows[column][column]
        determinant = determinant * value % prime
        inverse = pow(value, -1, prime)
        if rhs is not None:
            rows[column] = [a * inverse % prime for a in rows[column]]
        indices = range(size) if rhs is not None else range(column + 1, size)
        for i in indices:
            if i == column or not rows[i][column]:
                continue
            factor = rows[i][column]
            if rhs is None:
                factor = factor * inverse % prime
            for j in range(column, len(rows[i])):
                rows[i][j] = (rows[i][j] - factor * rows[column][j]) % prime
    return determinant % prime, [row[size:] for row in rows] if rhs is not None else None


def matrix_product(left, right, prime):
    return [
        [sum(a * b for a, b in zip(row, column)) % prime for column in zip(*right)]
        for row in left
    ]


def characteristic_polynomial(matrix, prime):
    size = len(matrix)
    coefficients = [1]
    for order in range(1, size + 1):
        value = 0
        for indices in combinations(range(size), order):
            minor = [[matrix[i][j] for j in indices] for i in indices]
            value += eliminate(minor, prime)[0]
        coefficients.append((-1) ** order * value % prime)
    return coefficients


def trim(poly):
    while poly and not poly[0]:
        poly.pop(0)
    return poly


def squarefree(poly, prime):
    degree = len(poly) - 1
    derivative = trim([(degree - i) * x % prime for i, x in enumerate(poly[:-1])])
    while derivative:
        residual = list(poly)
        inverse = pow(derivative[0], -1, prime)
        while len(residual) >= len(derivative):
            factor = residual[0] * inverse % prime
            for j, coefficient in enumerate(derivative):
                residual[j] = (residual[j] - factor * coefficient) % prime
            trim(residual)
        poly, derivative = derivative, residual
    return len(poly) == 1


def xorshift_coefficients(seed, count, prime):
    state = seed
    mask = (1 << 32) - 1
    for _ in range(count):
        state ^= (state << 13) & mask
        state ^= state >> 17
        state ^= (state << 5) & mask
        yield state % prime


def lcg_coefficients(seed, count, prime):
    state = seed
    for _ in range(count):
        state = (1664525 * state + 1013904223) % (1 << 32)
        yield state % prime


def check(size, prime, method, seed, trial):
    indices = list(product(range(size), repeat=4))
    pairs = list(product(range(size), repeat=2))
    count = size ** 4
    if method == "xorshift32":
        coefficients = list(xorshift_coefficients(seed, count * trial, prime))
    elif method == "lcg32":
        coefficients = list(lcg_coefficients(seed, count * trial, prime))
    else:
        random = Random(seed)
        coefficients = [random.randrange(prime) for _ in range(count * trial)]
    tensor = dict(zip(indices, coefficients[-count:]))
    flat12 = [[tensor[a, b, c, d] for c, d in pairs] for a, b in pairs]
    flat13 = [[tensor[a, b, c, d] for b, d in pairs] for a, c in pairs]
    flat14 = [[tensor[a, b, c, d] for b, c in pairs] for a, d in pairs]
    identity = [[int(i == j) for j in range(size * size)] for i in range(size * size)]
    det13, inverse = eliminate(flat13, prime, identity)
    assert det13
    dual = [[inverse[b * size + d][a * size + c] for c, d in pairs] for a, b in pairs]
    end12 = matrix_product(flat12, list(zip(*dual)), prime)
    end34 = matrix_product(list(zip(*flat12)), dual, prime)
    covariants = []
    for endomorphism in (end12, end34):
        square = matrix_product(endomorphism, endomorphism, prime)
        covariants.append([
            [sum(square[i * size + a][j * size + a] for a in range(size)) % prime
             for j in range(size)] for i in range(size)
        ])
        covariants.append([
            [sum(square[a * size + i][a * size + j] for a in range(size)) % prime
             for j in range(size)] for i in range(size)
        ])
    polynomials = [characteristic_polynomial(matrix, prime) for matrix in covariants]
    assert all(squarefree(poly, prime) for poly in polynomials)

    columns = [tensor]
    for mode, matrix in enumerate(covariants):
        extended = []
        for current in columns:
            for _ in range(size):
                extended.append(current)
                acted = {}
                for key in indices:
                    acted[key] = sum(
                        matrix[key[mode]][j] * current[key[:mode] + (j,) + key[mode + 1:]]
                        for j in range(size)
                    ) % prime
                current = acted
        columns = extended
    determinant, _ = eliminate([[column[key] for column in columns] for key in indices], prime)
    assert determinant
    roots = []
    for poly in polynomials:
        root_set = []
        for x in range(prime):
            value = 0
            for coefficient in poly:
                value = (value * x + coefficient) % prime
            if value == 0:
                root_set.append(x)
        roots.append(root_set)
    return {
        "n": size,
        "prime": prime,
        "generator": method,
        "seed": seed,
        "trial": trial,
        "pair_flattening_determinants": {
            "12|34": eliminate(flat12, prime)[0],
            "13|24": det13,
            "14|23": eliminate(flat14, prime)[0],
        },
        "covariant_charpolys": polynomials,
        "base_roots": roots,
        "joint_cyclic_determinant": determinant,
    }


def check_order_five(size, seed):
    prime = 101
    arity = 5
    indices = list(product(range(size), repeat=arity))
    tensor = dict(zip(indices, xorshift_coefficients(seed, len(indices), prime)))
    swaps = [bits for bits in product(range(2), repeat=arity) if not bits[0]]
    matrix = []
    for x in indices:
        row = []
        for y in indices:
            value = 0
            for bits in swaps:
                u = tuple(x[i] if bits[i] else y[i] for i in range(arity))
                v = tuple(y[i] if bits[i] else x[i] for i in range(arity))
                value += tensor[u] * tensor[v]
            row.append(value % prime)
        matrix.append(row)
    det, solved = eliminate(matrix, prime, [[tensor[x]] for x in indices])
    assert det
    dual = {key: solution[0] for key, solution in zip(indices, solved)}

    def local_covariants(pair):
        remaining = [i for i in range(arity) if i not in pair]
        pair_indices = list(product(range(size), repeat=2))

        def merge(pair_key, rest_key):
            key = [0] * arity
            for i, entry in zip(pair, pair_key):
                key[i] = entry
            for i, entry in zip(remaining, rest_key):
                key[i] = entry
            return tuple(key)

        rest = list(product(range(size), repeat=arity - 2))
        contraction = [
            [sum(tensor[merge(x, z)] * dual[merge(y, z)] for z in rest) % prime
             for y in pair_indices]
            for x in pair_indices
        ]
        squared = matrix_product(contraction, contraction, prime)
        return (
            [[sum(squared[a * size + k][b * size + k] for k in range(size)) % prime
              for b in range(size)] for a in range(size)],
            [[sum(squared[k * size + a][k * size + b] for k in range(size)) % prime
              for b in range(size)] for a in range(size)],
        )

    covariants = (*local_covariants((0, 1)), *local_covariants((2, 3)), local_covariants((0, 4))[1])
    polynomials = [characteristic_polynomial(a, prime) for a in covariants]
    assert all(squarefree(poly, prime) for poly in polynomials)
    columns = [tensor]
    for mode, operator in enumerate(covariants):
        expanded = []
        for column in columns:
            for _ in range(size):
                expanded.append(column)
                column = {
                    key: sum(
                        operator[key[mode]][j] * column[key[:mode] + (j,) + key[mode + 1:]]
                        for j in range(size)
                    ) % prime
                    for key in indices
                }
        columns = expanded
    joint_det, _ = eliminate([[column[key] for column in columns] for key in indices], prime)
    assert joint_det
    print(json.dumps({"arity": arity, "n": size, "prime": prime, "seed": seed,
                      "B_determinant": det, "covariant_charpolys": polynomials,
                      "joint_cyclic_determinant": joint_det}))


if __name__ == "__main__":
    samples = [
        (3, 2, "xorshift32", 20261172, 482),
        (3, 2, "xorshift32", 20261172, 9704),
        (3, 3, "xorshift32", 20261203, 16),
        (3, 101, "python_mt", 20261110, 2),
        (4, 101, "python_mt", 20261111, 1),
        (3, 101, "lcg32", 20261110, 3),
        (4, 101, "lcg32", 20261111, 3),
    ]
    for sample in samples:
        print(json.dumps(check(*sample)))
    check_order_five(2, 20261146)
    check_order_five(3, 20261163)
