"""Check the surface-chain predictions on actual polyhedral and torus flags."""
from collections import Counter
from itertools import combinations, permutations, product


def icosahedron():
    points = set()
    for a, b in product((-1, 1), repeat=2):
        v = ((0, 0), (a, 0), (0, b))
        points.update(v[i:] + v[:i] for i in range(3))
    points = sorted(points)
    index = {v: i for i, v in enumerate(points)}
    antipodes = [index[tuple((-a, -b) for a, b in v)] for v in points]

    def distance(v, w):
        first = second = 0
        for (a, b), (c, d) in zip(v, w, strict=True):
            x, y = a - c, b - d
            first += x * x + y * y
            second += 2 * x * y + y * y
        return first, second

    edges = {(i, j) for i, j in combinations(range(12), 2)
             if distance(points[i], points[j]) == (4, 0)}
    faces = {f for f in combinations(range(12), 3)
             if all(e in edges for e in combinations(f, 2))}
    assert len(edges) == 30 and len(faces) == 20
    representatives = sorted({min(i, antipodes[i]) for i in range(12)})
    fibres = [representatives.index(min(i, antipodes[i])) for i in range(12)]
    hemi = {tuple(sorted(fibres[i] for i in f)) for f in faces}
    assert len(hemi) == 10 and all(len(set(f)) == 3 for f in hemi)
    return faces, hemi


def lattice_torus(n):
    def vertex(x, y):
        return (x % n) * n + (y % n)

    faces = set()
    for x, y in product(range(n), repeat=2):
        a, b, c = vertex(x, y), vertex(x + 1, y), vertex(x, y + 1)
        d = vertex(x + 1, y + 1)
        faces.add(tuple(sorted((a, b, c))))
        faces.add(tuple(sorted((d, b, c))))
    actions = (lambda x, y: (x + 1, y), lambda x, y: (x, y + 1),
               lambda x, y: (-y, x + y), lambda x, y: (y, x))
    generators = [tuple(vertex(*move(x, y)) for x, y in product(range(n), repeat=2))
                  for move in actions]
    return faces, generators


def complex_data(faces):
    vertices = sorted({x for f in faces for x in f})
    edge_faces = Counter(e for f in faces for e in combinations(f, 2))
    assert set(edge_faces.values()) == {2}
    edges = sorted(edge_faces)
    cells = [(v,) for v in vertices] + edges + sorted(faces)
    flags = [(v, e, f) for f in sorted(faces) for e in combinations(f, 2)
             for v in ((e[0],), (e[1],))]
    pairs = sorted({p for v, e, f in flags for p in ((v, e), (e, f), (v, f))})
    assert Counter(p for flag in flags for p in combinations(flag, 2)) == {
        p: 2 for p in pairs
    }
    position = {p: i for i, p in enumerate(pairs)}
    boundaries = [{position[v, e]: 1, position[e, f]: 1, position[v, f]: -1}
                  for v, e, f in flags]
    beta = {i: 1 for i, (v, f) in enumerate(pairs) if len(v) == 1 and len(f) == 3}
    return cells, pairs, boundaries, beta


def span_contains(boundaries, target, p):
    basis = {}

    def reduce(row):
        row = {i: a % p for i, a in row.items() if a % p}
        while row:
            first = min(row)
            if first not in basis:
                break
            multiple = row[first]
            for j, a in basis[first].items():
                value = (row.get(j, 0) - multiple * a) % p
                if value:
                    row[j] = value
                elif j in row:
                    del row[j]
        return row

    for boundary in boundaries:
        row = reduce(boundary)
        if row:
            first = min(row)
            inverse = pow(row[first], -1, p)
            basis[first] = {j: a * inverse % p for j, a in row.items()}
    return not reduce(target)


def permutation_sign(cells, pairs, action):
    labels = [(c, c) for c in cells] + pairs
    position = {p: i for i, p in enumerate(labels)}

    def image(cell):
        return tuple(sorted(action[v] for v in cell))

    moved = [position[image(c), image(d)] for c, d in labels]
    seen = set()
    cycles = 0
    for start in range(len(moved)):
        if start in seen:
            continue
        cycles += 1
        v = start
        while v not in seen:
            seen.add(v)
            v = moved[v]
    return (-1) ** (len(moved) - cycles)


def main():
    full, hemi = icosahedron()
    for faces, rank, torsion_detected in ((full, 242, False), (hemi, 121, True)):
        cells, pairs, boundaries, _ = complex_data(faces)
        assert len(cells) + len(pairs) == rank
        comparison = {i: 1 for i in range(len(pairs))}
        assert span_contains(boundaries, comparison, 2) != torsion_detected
    hemi_cells, hemi_pairs, _, _ = complex_data(hemi)
    automorphisms = [
        p for p in permutations(range(6))
        if {tuple(sorted(p[i] for i in f)) for f in hemi} == hemi
    ]
    assert len(automorphisms) == 60
    assert all(permutation_sign(hemi_cells, hemi_pairs, p) == 1 for p in automorphisms)
    print("Icosahedral sphere and hemi-icosahedron: ranks 242 and 121, distinct mod-2 chains")
    print("All 60 hemi-icosahedral automorphisms checked directly")
    for n in (4, 5, 6, 7):
        faces, generators = lattice_torus(n)
        cells, pairs, boundaries, beta = complex_data(faces)
        assert len(cells) + len(pairs) == 24 * n * n
        assert span_contains(boundaries, beta, 3)
        assert not span_contains(boundaries, beta, 2)
        assert all(permutation_sign(cells, pairs, p) == 1 for p in generators)
        print(f"Period {n}: mod-3 chain and four geometric generators verified")


if __name__ == "__main__":
    main()
