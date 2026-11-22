"""Exact controls for bounded matrix substitutions and the first separating size."""

from random import Random


def add_scaled(row, other, scalar, modulus):
    for j, coefficient in other.items():
        value = (row.get(j, 0) + scalar * coefficient) % modulus
        if value:
            row[j] = value
        else:
            row.pop(j, None)


def echelon(rows, p):
    pivots = {}
    for given in rows:
        row = {j: value % p for j, value in given.items() if value % p}
        while row:
            j = min(row)
            if j not in pivots:
                reciprocal = pow(row[j], -1, p)
                pivots[j] = {i: value * reciprocal % p for i, value in row.items()}
                break
            add_scaled(row, pivots[j], -row[j], p)
    return pivots


def smith_signature(rows, p, exponent):
    if exponent == 1:
        return len(echelon(rows, p)), 0
    active = [row.copy() for row in rows if row]
    modulus = p**exponent
    units = 0
    while True:
        pivot = next(((i, j) for i, row in enumerate(active)
                      for j, value in row.items() if value % p), None)
        if pivot is None:
            break
        i, j = pivot
        row = active.pop(i)
        reciprocal = pow(row[j], -1, modulus)
        row = {k: value * reciprocal % modulus for k, value in row.items()}
        for other in active:
            if j in other:
                add_scaled(other, row, -other[j], modulus)
        units += 1
    assert exponent == 2
    divided = [{j: value // p for j, value in row.items()} for row in active]
    return units, len(echelon(divided, p))


def quotient_pivots(repetitions, full_rank, monomials, p):
    xsize = 4 * repetitions
    first, second, data = {}, {}, {}
    for i in range(repetitions):
        for j in range(4):
            first[monomials[4 * i + j, xsize + 8 * i + j]] = 1
            second[monomials[4 * i + j, xsize + 8 * i + 4 + j]] = 1
        data[monomials[4 * i + 2, xsize + 8 * i]] = 1
        if full_rank:
            data[monomials[4 * i + 3, xsize + 8 * i + 1]] = 1
    return echelon([first, second, data], p)


def beta(u, j, monomials, pivots, p):
    row = {monomials[min(i, j), max(i, j)]: value % p
           for i, value in u.items() if value % p}
    for pivot in sorted(pivots):
        if pivot in row:
            add_scaled(row, pivots[pivot], -row[pivot], p)
    return row


def evaluate(y0, directions, dim, monomials, pivots, p, exponent):
    q = len(y0)
    n = dim + len(monomials)
    s = p ** (exponent - 1)
    modulus = p**exponent
    rows = [{} for _ in range(q * n)]
    for i in range(q):
        for j in range(q):
            scalar = y0[i][j] % modulus
            if scalar:
                for a in range(n):
                    rows[i * n + a][j * n + a] = scalar
            for a in range(dim):
                product = beta(directions[i][j], a, monomials, pivots, p)
                for output, coefficient in product.items():
                    rows[i * n + dim + output][j * n + a] = s * coefficient
    return rows


def matmul(a, b, modulus):
    result = []
    for row in a:
        output = {}
        for k, coefficient in row.items():
            add_scaled(output, b[k], coefficient, modulus)
        result.append(output)
    return result


def subtract_identity(matrix, modulus):
    result = [row.copy() for row in matrix]
    for i, row in enumerate(result):
        add_scaled(row, {i: 1}, -1, modulus)
    return result


def main():
    rng = Random(6205)
    h, repetitions = 2, 3
    dim = 12 * repetitions + 1
    monomials = {(i, j): index for index, (i, j) in enumerate(
        (i, j) for i in range(dim) for j in range(i, dim)
    )}
    checks = 0
    for p, exponent in ((2, 1), (2, 2), (3, 1), (3, 2)):
        modulus = p**exponent
        pivots = [quotient_pivots(repetitions, full_rank, monomials, p)
                  for full_rank in (False, True)]
        for y0 in ([[0, 1], [0, 0]], [[p, 1], [0, 0]], [[p, 0], [0, p]], [[1, 1], [0, 1]]):
            directions = [
                [{i: rng.randrange(modulus) for i in rng.sample(range(dim), 4)}
                 for _ in range(h)] for _ in range(h)
            ]
            pair = [evaluate(y0, directions, dim, monomials, kernel, p, exponent)
                    for kernel in pivots]
            for shifted in (False, True):
                versions = ([subtract_identity(t, modulus) for t in pair]
                            if shifted else pair)
                original = versions
                for _ in range(2):
                    assert len({smith_signature(t, p, exponent) for t in versions}) == 1
                    versions = [matmul(t, u, modulus) for t, u in zip(versions, original)]
                    checks += 1
        directions = [[{} for _ in range(repetitions)] for _ in range(repetitions)]
        directions[0] = [{4 * i + 2: 1} for i in range(repetitions)]
        zero = [[0] * repetitions for _ in range(repetitions)]
        signatures = [
            smith_signature(evaluate(zero, directions, dim, monomials, kernel, p, exponent),
                            p, exponent)
            for kernel in pivots
        ]
        assert sum(signatures[1]) - sum(signatures[0]) == 1
    print(f"{checks} matching polynomial Smith signatures at size 2; "
          "4 separating signatures at size 3")


if __name__ == "__main__":
    main()
