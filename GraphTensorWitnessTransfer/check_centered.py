"""Check the quadratic decoder for a centered K4 incidence tensor over three fields.

Run with Python 3.8 or later. The check uses exact sparse linear algebra
and changes bases independently in all three modes.
"""

from itertools import combinations, product


def accumulate(row, index, value, prime):
    value = (row.get(index, 0) + value) % prime
    if value:
        row[index] = value
    else:
        row.pop(index, None)


def add_scaled(row, other, scale, prime):
    for index, value in other.items():
        accumulate(row, index, scale * value, prime)


def pivots(rows, prime):
    basis = {}
    for initial in rows:
        row = initial.copy()
        while row:
            column = min(row)
            if column in basis:
                add_scaled(row, basis[column], -row[column], prime)
            else:
                inverse = pow(row[column], -1, prime)
                basis[column] = {
                    i: value * inverse % prime for i, value in row.items()
                }
                break
    return basis


def nullspace(equations, dimension, prime):
    echelon = pivots(equations, prime)
    vectors = []
    for free in sorted(set(range(dimension)) - echelon.keys()):
        vector = {free: 1}
        for i in sorted(echelon, reverse=True):
            row = echelon[i]
            value = -sum(a * vector.get(j, 0) for j, a in row.items()) % prime
            if value:
                vector[i] = value
        vectors.append(vector)
    return vectors


def tensor_pair(x, y, prime):
    return {(i, j): a * b % prime for i, a in x.items() for j, b in y.items()}


def hidden_frame(dimension, prime):
    # Unitriangular columns followed by a cyclic change of coordinate order.
    columns = []
    for i in range(dimension):
        vector = {(i + 1) % dimension: 1}
        if i:
            vector[i % dimension] = prime - 1
        columns.append(vector)
    return columns


def centered_slices(edges, left, right, prime):
    units = [tensor_pair(left[v], right[e], prime)
             for e, endpoints in enumerate(edges) for v in endpoints]
    slices = []
    for unit in units[1:]:
        difference = unit.copy()
        add_scaled(difference, units[0], -1, prime)
        slices.append(difference)
    # Change the basis of the flattening domain as well.
    result = []
    for column in hidden_frame(len(slices), prime):
        vector = {}
        for j, coefficient in column.items():
            add_scaled(vector, slices[j], coefficient, prime)
        result.append(vector)
    return result


def quadratic_decoder(slices, left_dim, right_dim, prime):
    # For each ambient coordinate, its linear functional on S tensor S.
    values = {}
    for s, first in enumerate(slices):
        for t, second in enumerate(slices):
            column = s * len(slices) + t
            for (i, e), a in first.items():
                for (j, f), b in second.items():
                    row = values.setdefault((i, j, e, f), {})
                    accumulate(row, column, a * b, prime)

    equations = []
    for i, j, e, f in product(range(left_dim), range(left_dim),
                               range(right_dim), range(right_dim)):
        row = values.get((i, j, e, f), {})
        if i < j:
            difference = row.copy()
            add_scaled(difference, values.get((j, i, e, f), {}), -1, prime)
            equations.append(difference)
        if e < f:
            total = row.copy()
            add_scaled(total, values.get((i, j, f, e), {}), 1, prime)
            equations.append(total)
        if e == f:
            equations.append(row)

    kernel = nullspace(equations, len(slices) ** 2, prime)
    contractions = []
    for element in kernel:
        by_column_pair = {}
        for (i, j, e, f), row in values.items():
            value = sum(a * element.get(t, 0) for t, a in row.items()) % prime
            if value:
                by_column_pair.setdefault((e, f), {})[i, j] = value
        contractions.extend(by_column_pair.values())
    return len(kernel), contractions


def check(prime):
    edges = list(combinations(range(4), 2))
    left = hidden_frame(4, prime)
    right = hidden_frame(6, prime)
    slices = centered_slices(edges, left, right, prime)
    assert len(pivots(slices, prime)) == 11
    dim_k, contractions = quadratic_decoder(slices, 4, 6, prime)
    squares = [tensor_pair(v, v, prime) for v in left]
    assert dim_k == 4
    assert len(pivots(contractions, prime)) == 4
    assert len(pivots(contractions + squares, prime)) == 4

    # Enumerate all projective points solely as an independent check of the
    # four row axes. For each recovered axis use the dual basis to compute
    # its row projection. The edge lines are intersections of these spaces.
    hits = []
    decoded = list(pivots(contractions, prime).values())
    for coords in product(range(prime), repeat=4):
        if next((a for a in coords if a), 0) != 1:
            continue
        vector = {i: a for i, a in enumerate(coords) if a}
        square = tensor_pair(vector, vector, prime)
        if len(pivots(decoded + [square], prime)) == 4:
            hits.append(vector)
    assert len(hits) == 4
    # Match the recovered points with truth only to order the test assertions.
    ordered = []
    for expected in left:
        matching = [pt for pt in hits if len(pivots([expected, pt], prime)) == 1]
        recovered, = matching
        ordered.append(recovered)
    projections = []
    for v in range(4):
        # Annuls the other three row axes.
        dual, = nullspace([other for i, other in enumerate(ordered) if i != v], 4, prime)
        projected = []
        for section in slices:
            row = {}
            for (i, e), value in section.items():
                accumulate(row, e, dual.get(i, 0) * value, prime)
            projected.append(row)
        assert len(pivots(projected, prime)) == 3
        projections.append(projected)
    for e, (v, w) in enumerate(edges):
        both = projections[v] + projections[w]
        assert len(pivots(both, prime)) == 5
        assert len(pivots(projections[v] + [right[e]], prime)) == 3
        assert len(pivots(projections[w] + [right[e]], prime)) == 3
    print(f"F_{prime}: dim S=11, dim K=4, dim D=4, 4 row and 6 edge lines verified")


if __name__ == "__main__":
    for characteristic in (2, 3, 5):
        check(characteristic)
