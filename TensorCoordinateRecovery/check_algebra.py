"""Exact controls for the subspace search and the rectangular amplification formula."""

from itertools import product


def reduce_rows(rows, width, p):
    pivots = {}
    for row in rows:
        row = [a % p for a in row]
        for j in range(width):
            if not row[j]:
                continue
            if j in pivots:
                scale = row[j]
                row = [(a - scale * b) % p for a, b in zip(row, pivots[j])]
            else:
                inverse = pow(row[j], -1, p)
                pivots[j] = [inverse * a % p for a in row]
                break
    return pivots


def nullspace(rows, width, p):
    pivots = reduce_rows(rows, width, p)
    basis = []
    for f in range(width):
        if f in pivots:
            continue
        v = [0] * width
        v[f] = 1
        for j in sorted(pivots, reverse=True):
            v[j] = -sum(a * b for a, b in zip(pivots[j], v)) % p
        basis.append(v)
    return basis


def identity(d):
    return [[int(i == j) for j in range(d)] for i in range(d)]


def apply(x, v, p):
    return [sum(a * b for a, b in zip(row, v)) % p for row in x]


def preserve(subspaces, d, p):
    equations = (
        [left[i] * v[j] for i in range(d) for j in range(d)]
        for basis in subspaces
        for left in nullspace(basis, d, p)
        for v in basis
    )
    return nullspace(equations, d * d, p)


def rigidity_test(k, p):
    unit = identity(k)
    zero = [0] * k
    shift = [zero] + unit[:-1]
    projection = [unit[0]] + [zero] * (k - 1)
    spaces = [[v + zero for v in unit], [zero + v for v in unit]]
    spaces += [[u + v for u, v in zip(unit, b)] for b in (unit, shift, projection)]

    # Independently change the common coordinates by invertible shears.
    change = identity(2 * k)
    for j in range(1, 2 * k):
        change[j] = [(x + y) % p for x, y in zip(change[j], change[j - 1])]
    for j in range(1, 2 * k):
        change[0] = [(x + 2 * j * y) % p for x, y in zip(change[0], change[j])]
    assert len(reduce_rows(change, 2 * k, p)) == 2 * k
    conjugated = [[apply(change, v, p) for v in basis] for basis in spaces]
    assert len(preserve(spaces, 2 * k, p)) == len(preserve(conjugated, 2 * k, p)) == 1


def normalized(v, p):
    scalar = next(x for x in v if x)
    return tuple(x * pow(scalar, -1, p) % p for x in v)


def quotient_test(p):
    d = 3
    directions = identity(d)
    algebra = preserve([directions[:1]], d, p)
    assert len(algebra) == 7
    all_columns = list(product(range(p), repeat=d))
    tagged_columns = list(product(range(p), range(1), range(1)))
    exact_classes, units = set(), 0
    for columns in product(tagged_columns, all_columns, all_columns):
        if len(reduce_rows(columns, d, p)) == d:
            units += 1
            exact_classes.add(tuple(normalized(v, p) for v in columns))
    assert units == len(exact_classes) * (p - 1) ** d

    block_basis = []
    for j in range(d):
        block_basis.append({normalized(v, p) for v in (tagged_columns if j == 0 else all_columns) if any(v)})
    enumerated = {columns for columns in product(*block_basis) if len(reduce_rows(columns, d, p)) == d}
    assert enumerated == exact_classes
    candidate_count = len(block_basis[0]) * len(block_basis[1]) * len(block_basis[2])
    assert candidate_count <= (p + 1) ** (len(algebra) - d)
    return units, len(exact_classes), candidate_count


def endomorphism_dimension(slices, p):
    m, n = len(slices[0]), len(slices[0][0])
    width = m * m + n * n
    equations = []
    for a in slices:
        for i in range(m):
            for j in range(n):
                row = [0] * width
                for k in range(m):
                    row[i * m + k] = a[k][j]
                for k in range(n):
                    row[m * m + k * n + j] = -a[i][k]
                equations.append(row)
    return width - len(reduce_rows(equations, width, p))


def rectangular_amplification_test(p):
    slices = [identity(2), [[0, 1], [0, 0]]]
    e, f = 2, 3
    amplified = [
        [[a[i % 2][j % 2] if i // 2 == h and j // 2 == k else 0
          for j in range(2 * f)] for i in range(2 * e)]
        for a in slices
        for h in range(e)
        for k in range(f)
    ]
    assert endomorphism_dimension(slices, p) == endomorphism_dimension(amplified, p) == 2


if __name__ == "__main__":
    for prime in (2, 3, 5):
        for dimension in range(2, 7):
            rigidity_test(dimension, prime)
        rectangular_amplification_test(prime)
        units, classes, candidates = quotient_test(prime)
        print(f"F_{prime}: five-support and amplification checks passed, {units} units, "
              f"{classes} distinct classes, {candidates} candidates before invertibility")
