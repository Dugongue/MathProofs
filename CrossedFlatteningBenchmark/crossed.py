"""Exact matched four-way TI by crossed flattenings over Q or a prime field.

Index order is (left_1, left_2, right_1, right_2), with the last
coordinate varying fastest. The right Kronecker matrix acts transposed.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import prod
import argparse
import json
from pathlib import Path


def parse(field, entries):
    if field == "Q":
        return [Fraction(value) for value in entries]
    return [int(value) % field for value in entries]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def rows(entries, width):
    return [entries[i:i + width] for i in range(0, len(entries), width)]


def flatten(matrix):
    return [x for row in matrix for x in row]


def reduce_rows(equations, columns, p):
    """Reduced row form, pivoting only in the indicated coefficient columns."""
    matrix = [list(row) for row in equations]
    pivots = []
    for col in range(columns):
        index = len(pivots)
        pivot = next((i for i in range(index, len(matrix)) if matrix[i][col]), None)
        if pivot is None:
            continue
        matrix[index], matrix[pivot] = matrix[pivot], matrix[index]
        vector = matrix[index]
        if p is None:
            divisor = Fraction(vector[col])
            vector = [value / divisor for value in vector]
        else:
            reciprocal = pow(vector[col], -1, p)
            vector = [value * reciprocal % p for value in vector]
        matrix[index] = vector
        for i, row in enumerate(matrix):
            factor = row[col]
            if i == index or not factor:
                continue
            if p is None:
                matrix[i] = [x - factor * y for x, y in zip(row, vector)]
            else:
                matrix[i] = [(x - factor * y) % p for x, y in zip(row, vector)]
        pivots.append(col)
        if len(pivots) == len(matrix):
            break
    return matrix, pivots


def inverse_and_rank(matrix, p):
    size = len(matrix)
    reduced, pivots = reduce_rows([a + b for a, b in zip(matrix, identity(size))], size, p)
    return (None if len(pivots) < size else [row[size:] for row in reduced], len(pivots))


def nullspace(equations, columns, p):
    form, pivots = reduce_rows(equations, columns, p)
    answer = []
    for free in sorted(set(range(columns)) - set(pivots)):
        vec = [0] * columns
        vec[free] = 1
        for i, pivot in enumerate(pivots):
            value = -form[i][free]
            vec[pivot] = value if p is None else value % p
        answer.append(vec)
    return answer


def matmul(a, b, p):
    columns = list(zip(*b))
    output = [[sum(x * y for x, y in zip(row, col) if x and y) for col in columns] for row in a]
    if p is not None:
        return [[value % p for value in row] for row in output]
    return output


def transpose(a):
    return [list(col) for col in zip(*a)]


def kronecker(a, b, p):
    output = [[x * y for x in aa for y in bb] for aa in a for bb in b]
    if p is not None:
        return [[value % p for value in row] for row in output]
    return output


def crossing(a, left, right):
    return [[a[i * right + ell][k * right + j]
             for k, ell in product(range(left), range(right))]
            for i, j in product(range(left), range(right))]


def partial_traces(a, left, right, p):
    first = [[sum(a[i * right + j][k * right + j] for j in range(right))
              for k in range(left)] for i in range(left)]
    second = [[sum(a[i * right + j][i * right + ell] for i in range(left))
               for ell in range(right)] for j in range(right)]
    if p is not None:
        first = [[x % p for x in row] for row in first]
        second = [[x % p for x in row] for row in second]
    return first, second


def intertwiner_system(source, target, p):
    size = len(source[0])
    result = []
    for a, b in zip(source, target):
        for i in range(size):
            for j in range(size):
                equation = [0] * (size * size)
                for k in range(size):
                    equation[i * size + k] += a[k][j]
                    equation[k * size + j] -= b[i][k]
                result.append(equation if p is None else [value % p for value in equation])
    return result


@dataclass
class Profile:
    ranks: tuple
    commutants: tuple | None = None
    covariants: tuple | None = None
    inverse: list | None = None

    @property
    def supported(self):
        return self.commutants == (1, 1)


def profile(entries, sizes, p):
    left, right = sizes
    size = left * right
    matrix = rows(entries, size)
    inv, r1 = inverse_and_rank(matrix, p)
    inv_cross, r2 = inverse_and_rank(crossing(matrix, left, right), p)
    result = Profile((r1, r2))
    if inv is None or inv_cross is None:
        return result
    mixed = matmul(matrix, crossing(inv_cross, left, right), p)
    for i in range(size):
        mixed[i][i] -= 1
        if p is not None:
            mixed[i][i] %= p
    square = matmul(mixed, mixed, p)
    cube = matmul(square, mixed, p)
    covariants = tuple(zip(partial_traces(square, left, right, p),
                           partial_traces(cube, left, right, p)))
    dimensions = []
    for local, n in zip(covariants, sizes):
        _, pivots = reduce_rows(intertwiner_system(local, local, p), n * n, p)
        dimensions.append(n * n - len(pivots))
    return Profile((r1, r2), tuple(dimensions), covariants, inv)


def rank_certificate(entries, sizes, p):
    """Coverage only. A good prime can certify full cuts and scalar commutants over Q."""
    if p is not None:
        return profile(entries, sizes, p), False
    prime = 65521
    if all(value.denominator % prime for value in entries):
        images = [(value.numerator * pow(value.denominator, -1, prime)) % prime for value in entries]
        screen = profile(images, sizes, prime)
        if screen.supported:
            return screen, True
    return profile(entries, sizes, None), False


def factor_kronecker(matrix, sizes, p):
    left, right = sizes
    blocks = [[[
        matrix[i * right + j][k * right:(k + 1) * right]
        for j in range(right)
    ] for k in range(left)] for i in range(left)]
    candidate = next((block for row in blocks for block in row if any(map(any, block))), None)
    if candidate is None:
        return None
    j, ell = next((j, ell) for j in range(right) for ell in range(right) if candidate[j][ell])
    pivot = candidate[j][ell]
    reciprocal = Fraction(1, pivot) if p is None else pow(pivot, -1, p)
    first = [[block[j][ell] * reciprocal for block in row] for row in blocks]
    if p is not None:
        first = [[value % p for value in row] for row in first]
    return (first, candidate) if kronecker(first, candidate, p) == matrix else None


def apply(entries, sizes, witness, p):
    a, b, c, d = witness
    source = rows(entries, prod(sizes))
    return flatten(matmul(matmul(kronecker(a, b, p), source, p), transpose(kronecker(c, d, p)), p))


def verify(source, target, sizes, witness, p):
    return all(inverse_and_rank(m, p)[0] is not None for m in witness) and apply(
        source, sizes, witness, p
    ) == target


def solve_prepared(source, target, sizes, p, a, b):
    if a.ranks != b.ranks or a.commutants != b.commutants:
        return "no", None, "invariant mismatch"
    if not a.supported or not b.supported:
        return "unknown", None, "outside scalar-commutant class"
    factors = []
    for left, right, n in zip(a.covariants, b.covariants, sizes):
        basis = nullspace(intertwiner_system(left, right, p), n * n, p)
        if len(basis) != 1:
            return "no", None, "local intertwiners"
        g = rows(basis[0], n)
        if inverse_and_rank(g, p)[0] is None:
            return "no", None, "singular local intertwiner"
        factors.append(g)
    linv = inverse_and_rank(kronecker(*factors, p), p)[0]
    recovered_right = transpose(matmul(matmul(a.inverse, linv, p), rows(target, prod(sizes)), p))
    right_factors = factor_kronecker(recovered_right, sizes, p)
    if right_factors is None:
        return "no", None, "right Kronecker test"
    witness = factors + list(right_factors)
    if not verify(source, target, sizes, witness, p):
        raise ArithmeticError("Constructed witness did not verify.")
    return "yes", witness, "verified"


def solve(pair):
    field, dims = pair["field"], pair["dims"]
    if len(dims) != 4 or list(dims[:2]) != list(dims[2:]) or min(dims) < 2:
        return {"status": "unknown", "reason": "unsupported format"}
    sizes = tuple(dims[:2])
    p = None if field == "Q" else field
    source, target = (parse(field, pair[key]) for key in ("src", "dst"))
    if len(source) != prod(dims) or len(target) != prod(dims):
        raise ValueError("Wrong number of tensor entries.")
    a = profile(source, sizes, p)
    b = profile(target, sizes, p)
    status, witness, reason = solve_prepared(source, target, sizes, p, a, b)
    result = {"status": status, "reason": reason, "ranks": [a.ranks, b.ranks],
              "commutants": [a.commutants, b.commutants]}
    if witness is not None:
        result["witness"] = witness
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pair", type=Path)
    args = parser.parse_args()
    print(json.dumps(solve(json.loads(args.pair.read_text(encoding="utf-8"))), default=str))


if __name__ == "__main__":
    main()
