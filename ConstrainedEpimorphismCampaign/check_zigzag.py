"""Exhaustive checks of six small marked zigzag instances."""

from itertools import product
from math import prod


def rank(matrix, q):
    """Rank over the prime field of order q."""
    if not matrix:
        return 0
    rows = [list(row) for row in matrix]
    out = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(out, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[out], rows[pivot] = rows[pivot], rows[out]
        scale = pow(rows[out][col], -1, q)
        rows[out] = [value * scale % q for value in rows[out]]
        for i in range(out + 1, len(rows)):
            factor = rows[i][col]
            if factor:
                rows[i] = [
                    (value - factor * base) % q
                    for value, base in zip(rows[i], rows[out])
                ]
        out += 1
        if out == len(rows):
            break
    return out


def affine_solutions(equations, nvars, q):
    """Enumerate all solutions of the augmented raw matrix equations."""
    rows = [list(row) for row in equations]
    pivots = []
    for col in range(nvars):
        top = len(pivots)
        pivot = next((i for i in range(top, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[top], rows[pivot] = rows[pivot], rows[top]
        scale = pow(rows[top][col], -1, q)
        rows[top] = [value * scale % q for value in rows[top]]
        for i, row in enumerate(rows):
            if i == top:
                continue
            factor = row[col]
            if factor:
                rows[i] = [
                    (value - factor * base) % q
                    for value, base in zip(row, rows[top])
                ]
        pivots.append(col)
        if len(pivots) == len(rows):
            break

    if any(row[-1] for row in rows[len(pivots):]):
        return
    pivot_set = set(pivots)
    free = [j for j in range(nvars) if j not in pivot_set]
    pivot_rows = [
        ([row[j] for j in free], row[-1]) for row in rows[:len(pivots)]
    ]

    for values in product(range(q), repeat=len(free)):
        vector = [0] * nvars
        for j, value in zip(free, values):
            vector[j] = value
        for j, (coefficients, rhs) in zip(pivots, pivot_rows):
            vector[j] = (
                rhs - sum(a * b for a, b in zip(coefficients, values))
            ) % q
        yield vector


def check(q, d, spaces):
    """Count epimorphisms using all commutation and marking equations."""
    nvertices = 4 * len(spaces) + 1
    bars = [(0, nvertices - 1, None)]
    target_dims = [d] * nvertices
    for i, basis in enumerate(spaces):
        start = 4 * i
        mark_dim = len(basis)
        codim = d - mark_dim
        target_dims[start + 3] += mark_dim
        bars.extend((start, start + 3, j) for j in range(mark_dim))
        bars.extend((start, start + 2, None) for _ in range(codim - 1))
        bars.extend((start + 2, start + 4, None) for _ in range(d - 1))

    active = [
        [j for j, (left, right, _) in enumerate(bars) if left <= v <= right]
        for v in range(nvertices)
    ]
    offsets = []
    nvars = 0
    for dim, active_bars in zip(target_dims, active):
        offsets.append(nvars)
        nvars += dim * len(active_bars)

    def entry(v, i, j):
        return offsets[v] + i * len(active[v]) + j

    equations = []

    def add(terms, rhs):
        row = [0] * (nvars + 1)
        for col, coefficient in terms:
            row[col] = (row[col] + coefficient) % q
        row[-1] = rhs
        equations.append(row)

    for v, active_bars in enumerate(active):
        if v % 4 == 3:
            for i in range(d, target_dims[v]):
                for j, bar in enumerate(active_bars):
                    add([(entry(v, i, j), 1)], int(bars[bar][2] == i - d))
        if v % 2 == 0:
            continue
        for u in (v - 1, v + 1):
            dest_positions = {bar: j for j, bar in enumerate(active[u])}
            for i in range(d):
                for j, bar in enumerate(active_bars):
                    terms = [(entry(v, i, j), 1)]
                    if v % 4 == 3 and u == v - 1:
                        basis = spaces[(v - 3) // 4]
                        terms.extend(
                            (entry(v, d + h, j), vector[i])
                            for h, vector in enumerate(basis)
                        )
                    if bar in dest_positions:
                        terms.append((entry(u, i, dest_positions[bar]), -1))
                    add(terms, 0)

    count = 0
    for solution in affine_solutions(equations, nvars, q):
        for v, target_dim in enumerate(target_dims):
            source_dim = len(active[v])
            matrix = [
                solution[entry(v, i, 0):entry(v, i, 0) + source_dim]
                for i in range(target_dim)
            ]
            if rank(matrix, q) != target_dim:
                break
        else:
            count += 1

    good = sum(
        all(rank([*basis, vector], q) == len(basis) + 1 for basis in spaces)
        for vector in product(range(q), repeat=d)
    )
    beta = prod(q ** d - q ** j for j in range(1, d))
    expected = good * beta ** len(spaces)
    for basis in spaces:
        codim = d - len(basis)
        expected *= q ** (len(basis) * (codim - 1))
        expected *= prod(q ** codim - q ** j for j in range(1, codim))
    assert count == expected, (q, d, spaces, count, expected)
    return count


def main():
    cases = [
        (2, 1, [[]], 1),
        (2, 2, [[[1, 0]]], 4),
        (2, 2, [[[1, 1]], [[0, 1]]], 4),
        (2, 2, [[], [[1, 0]]], 16),
        (3, 2, [[[1, 2]], []], 1296),
        (2, 3, [[]], 4032),
    ]
    for number, (q, d, spaces, expected) in enumerate(cases, start=1):
        actual = check(q, d, spaces)
        assert actual == expected, (number, actual, expected)
        print(f"Case {number}: q={q}, d={d}, checks={len(spaces)}, count={actual}")


if __name__ == "__main__":
    main()
