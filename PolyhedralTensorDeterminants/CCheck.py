
"""Independent combinatorial checks for the Platonic interval determinants."""

from collections import Counter
from itertools import combinations, product
from math import gcd


def tetrahedron():
    return 4, list(combinations(range(4), 2)), list(combinations(range(4), 3)), (1, 0, 2, 3)


def cube():
    edges = [(i, i ^ (1 << d)) for i in range(8) for d in range(3) if not i & (1 << d)]
    faces = [tuple(i for i in range(8) if (i >> d) & 1 == b)
             for d, b in product(range(3), range(2))]
    return 8, sorted(edges), faces, tuple(i ^ 7 for i in range(8))


def icosahedron():
    # A pair (a,b) represents a + b*phi, where phi^2 = phi + 1.
    vertices = []
    for a, b, d in product((-1, 1), (-1, 1), range(3)):
        v = ((0, 0), (a, 0), (0, b))
        vertices.append(v[d:] + v[:d])

    def distance_squared(v, w):
        coordinates = [(a - c, b - d) for (a, b), (c, d) in zip(v, w)]
        return (sum(a * a + b * b for a, b in coordinates),
                sum(2 * a * b + b * b for a, b in coordinates))

    edges = [edge for edge in combinations(range(12), 2)
             if distance_squared(*(vertices[i] for i in edge)) == (4, 0)]
    edge_set = set(edges)
    faces = [tri for tri in combinations(range(12), 3)
             if all(edge in edge_set for edge in combinations(tri, 2))]
    opposite = tuple(vertices.index(tuple((-a, -b) for a, b in v)) for v in vertices)
    assert (len(edges), len(faces)) == (30, 20)
    return 12, edges, faces, opposite


def induced(cells, permutation):
    index = {cell: i for i, cell in enumerate(cells)}
    return tuple(index[tuple(sorted(permutation[v] for v in cell))] for cell in cells)


def dual(polyhedron):
    n, edges, faces, permutation = polyhedron
    dual_edges = [tuple(i for i, face in enumerate(faces) if set(edge) <= set(face))
                  for edge in edges]
    assert all(len(edge) == 2 for edge in dual_edges)
    dual_faces = [tuple(i for i, face in enumerate(faces) if v in face) for v in range(n)]
    return len(faces), dual_edges, dual_faces, induced(faces, permutation)


def parity(items, permutation):
    index = {item: i for i, item in enumerate(items)}
    sequence = [index[permutation(item)] for item in items]
    assert len(set(sequence)) == len(items)
    return (-1) ** sum(i > j for i, j in combinations(sequence, 2))


def matrix_rank(rows, prime):
    matrix = [[c % prime for c in row] for row in rows]
    rank = 0
    for column in range(len(rows[0])):
        pivot = next((r for r in range(rank, len(rows)) if matrix[r][column]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][column], -1, prime)
        for r in range(rank + 1, len(rows)):
            scale = matrix[r][column] * inverse % prime
            if scale:
                matrix[r] = [(a - scale * b) % prime for a, b in zip(matrix[r], matrix[rank])]
        rank += 1
        if rank == len(rows):
            break
    return rank


def count_cells(polyhedron):
    n, edges, faces, on_vertices = polyhedron
    permutations = on_vertices, induced(edges, on_vertices), induced(faces, on_vertices)
    points = [(r, i) for r, size in enumerate((n, len(edges), len(faces))) for i in range(size)]

    def on_point(point):
        rank, i = point
        return rank, permutations[rank][i]

    ve = [((0, v), (1, e)) for e, edge in enumerate(edges) for v in edge]
    ef = [((1, e), (2, f)) for f, face in enumerate(faces)
          for e, edge in enumerate(edges) if set(edge) <= set(face)]
    vf = [((0, v), (2, f)) for f, face in enumerate(faces) for v in face]
    strict = ve + ef + vf
    intervals = [(p, p) for p in points] + strict
    assert len(ve) == len(ef) == len(vf) == 2 * len(edges)
    sign = parity(intervals, lambda interval: tuple(on_point(p) for p in interval))

    exponents = Counter()
    for a, b in strict:
        exponents[a] -= 1
        exponents[b] += 1
    exponent_gcd = gcd(*exponents.values())

    flags = [(a, b, c) for a, b in ve for d, c in ef if b == d]
    usage = Counter(ve + ef)
    indices = {pair: i for i, pair in enumerate(strict)}
    rows = []
    for a, b, c in flags:
        usage[a, b] += 1
        usage[b, c] += 1
        row = [0] * len(strict)
        row[indices[a, b]] = row[indices[b, c]] = 1
        row[indices[a, c]] = -1
        rows.append(row)
    assert set(usage.values()) == {3}
    for prime in (2, 3, 5, 7):
        assert matrix_rank(rows, prime) == len(strict) - len(points) + 1
    return len(intervals), exponent_gcd, sign, len(points) + len(ve) + len(ef) + len(flags)


def subgroups_from_units(units, multiply, minus_one):
    identity = multiply(minus_one, minus_one)
    square = {multiply(u, u) for u in units}
    cube_image = {multiply(multiply(u, u), u) for u in units}
    incidence_image = {multiply(u, s) for u, s in product(square, (identity, minus_one))}
    return len(units) // len(cube_image), len(units) // len(incidence_image)


def main():
    solids = [
        ("tetrahedron", tetrahedron(), (50, 6, -1, 62)),
        ("cube", cube(), (98, 2, -1, 122)),
        ("octahedron", dual(cube()), (98, 2, -1, 122)),
        ("icosahedron", icosahedron(), (242, 2, -1, 302)),
        ("dodecahedron", dual(icosahedron()), (242, 2, -1, 302)),
    ]
    for name, solid, expected in solids:
        output = count_cells(solid)
        assert output == expected, (name, output, expected)
        print(name, output)
    for q, expected in ((5, (1, 2)), (7, (3, 1))):
        assert subgroups_from_units(range(1, q), lambda a, b: a * b % q, q - 1) == expected
    assert subgroups_from_units((1, 3), lambda a, b: a * b % 4, 3) == (1, 1)
    # Units 1 + a*epsilon are encoded by their coefficients a in F_2.
    assert subgroups_from_units((0, 1), lambda a, b: a ^ b, 0) == (1, 2)


if __name__ == "__main__":
    main()
