from itertools import product
from math import prod


def monomials(n):
    return tuple(indices for indices in product(range(4), repeat=n) if sum(indices) == 3)


def determinant(matrix):
    if len(matrix) == 2:
        (a, b), (c, d) = matrix
        return (a * d - b * c) % 3
    (a, b, c), (d, e, f), (g, h, i) = matrix
    return (a * (e * i - f * h) + b * (f * g - d * i) + c * (d * h - e * g)) % 3


def general_linear(n):
    for entries in product(range(3), repeat=n * n):
        matrix = tuple(entries[i:i + n] for i in range(0, n * n, n))
        if determinant(matrix):
            yield matrix


def pullback_columns(matrix, mono, terms=None):
    n = len(matrix)
    index = {m: j for j, m in enumerate(mono)}
    columns = []
    for m in mono if terms is None else terms:
        rows = [i for i, power in enumerate(m) for _ in range(power)]
        column = [0] * len(mono)
        for choices in product(*(tuple(j for j, a in enumerate(matrix[i]) if a) for i in rows)):
            weight = prod(matrix[i][j] for i, j in zip(rows, choices))
            key = tuple(choices.count(i) for i in range(n))
            column[index[key]] = (column[index[key]] + weight) % 3
        columns.append(tuple(column))
    return tuple(columns)


def apply(columns, form):
    return tuple(sum(a * b for a, b in zip(row, form)) % 3
                 for row in zip(*columns))


def polar_key(form, mono):
    return tuple(a for a, m in zip(form, mono) if 3 not in m)


def projective(column):
    factor = next(a for a in column if a)
    return tuple(factor * a % 3 for a in column)


def matrix_product(a, b):
    return tuple(tuple(sum(u * v for u, v in zip(row, col)) % 3 for col in zip(*b))
                 for row in a)


def projective_chain(group):
    current = group
    order = 1
    generators = []
    for i in range(2):
        image_reps = {}
        for s in current:
            image_reps.setdefault(projective(tuple(row[i] for row in s)), s)
        order *= len(image_reps)
        generators.extend(image_reps.values())
        fixed = tuple(int(i == j) for j in range(2))
        current = [s for s in current if projective(tuple(row[i] for row in s)) == fixed]
    order *= len(current)
    generators.extend(current)
    identity = ((1, 0), (0, 1))
    found = {identity}
    queue = [identity]
    for s in queue:
        for g in generators:
            next_matrix = matrix_product(g, s)
            if next_matrix not in found:
                found.add(next_matrix)
                queue.append(next_matrix)
    assert order == len(group) and found == set(group)


def binary_trials():
    mono = monomials(2)
    maps = [(matrix, pullback_columns(matrix, mono)) for matrix in general_linear(2)]
    forms = tuple(product(range(3), repeat=len(mono)))
    count = 0
    for f in forms:
        key = polar_key(f, mono)
        literal = {apply(columns, f) for _, columns in maps}
        polar_stabilizer = [(s, cols) for s, cols in maps
                            if polar_key(apply(cols, f), mono) == key]
        projective_chain([s for s, _ in polar_stabilizer])
        fiber = {apply(cols, f) for _, cols in polar_stabilizer}
        assert len(fiber) <= 9
        assert len(polar_stabilizer) == len(fiber) * sum(apply(cols, f) == f
                                                       for _, cols in maps)
        reps = {}
        for _, cols in maps:
            target_key = polar_key(apply(cols, f), mono)
            reps.setdefault(target_key, cols)
        for g in forms:
            rep = reps.get(polar_key(g, mono))
            predicted = rep is not None and any(apply(rep, member) == g for member in fiber)
            assert predicted == (g in literal)
            count += 1
    f = tuple(int(m == (2, 1)) for m in mono)
    g = tuple(int(m in ((2, 1), (0, 3))) for m in mono)
    assert polar_key(f, mono) == polar_key(g, mono)
    assert all(apply(cols, f) != g for _, cols in maps)
    return count


def radical_count_trials():
    binary_mono = monomials(2)
    binary_f = tuple(int(m == (2, 1)) for m in binary_mono)
    binary_maps = [pullback_columns(s, binary_mono) for s in general_linear(2)]
    exact = sum(apply(s, binary_f) == binary_f for s in binary_maps)
    polar = sum(polar_key(apply(s, binary_f), binary_mono) == polar_key(binary_f, binary_mono)
                for s in binary_maps)
    cube_mono = monomials(3)
    p = (2, 1, 0)
    z = (0, 0, 3)
    cubic_f = tuple(int(m == p) for m in cube_mono)
    cube_z = tuple(int(m == z) for m in cube_mono)
    combined = tuple(a + b for a, b in zip(cubic_f, cube_z))
    counts = [0, 0, 0]
    visited = 0
    for matrix in general_linear(3):
        fp, zp = pullback_columns(matrix, cube_mono, (p, z))
        counts[0] += fp == cubic_f
        counts[1] += tuple((a + b) % 3 for a, b in zip(fp, zp)) == combined
        counts[2] += zp == cube_z
        visited += 1
    assert counts == [3 ** 2 * 2 * exact, polar, 3 ** 2 * 48]
    assert visited == 11232
    return counts


FRUCHT = {(0, 1), (0, 6), (0, 7), (1, 2), (1, 7), (2, 3), (2, 8), (3, 4),
          (3, 9), (4, 5), (4, 9), (5, 6), (5, 10), (6, 10), (7, 11), (8, 9),
          (8, 11), (10, 11)}


def count_automorphisms(edges):
    vertices = sorted(set().union(*map(set, edges)))
    neighbors = {v: {a if b == v else b for a, b in edges if v in (a, b)} for v in vertices}
    image = {}
    unused = set(vertices)

    def choices(v):
        return [w for w in unused if len(neighbors[v]) == len(neighbors[w])
                and all((a in neighbors[v]) == (b in neighbors[w]) for a, b in image.items())]

    def count():
        if not unused:
            return 1
        v = min((a for a in vertices if a not in image), key=lambda x: len(choices(x)))
        total = 0
        for w in choices(v):
            image[v] = w
            unused.remove(w)
            total += count()
            unused.add(w)
            del image[v]
        return total

    return count()


def graph_trials():
    for k in range(18, 25):
        path = (0,) + tuple(range(12, 12 + k - 18)) + (1,)
        edges = (FRUCHT - {(0, 1)}) | {tuple(sorted(pair)) for pair in zip(path, path[1:])}
        assert len(edges) == k and count_automorphisms(edges) == 1
        vertices = set().union(*map(set, edges))
        neighborhoods = [{e for e in edges if v in e} for v in vertices]
        assert all(len(s) >= 2 for s in neighborhoods)
        assert all(not s <= t for s in neighborhoods for t in neighborhoods if s is not t)


def extension_field_trials():
    elements = tuple(product(range(3), repeat=2))

    def mul(x, y):
        a, b = x
        c, d = y
        return ((a*c - b*d) % 3, (a*d + b*c) % 3)

    def cube(x):
        return mul(mul(x, x), x)

    for x, y in product(elements, repeat=2):
        total = tuple((a + b) % 3 for a, b in zip(x, y))
        assert cube(total) == tuple((a + b) % 3 for a, b in zip(cube(x), cube(y)))
        assert cube(cube(x)) == x
    assert cube((0, 1)) == (0, 2)


def main():
    assert binary_trials() == 6561
    counts = radical_count_trials()
    graph_trials()
    extension_field_trials()
    print("6,561 binary cubic pairs and 81 projective stabilizer chains passed.")
    print("11,232 ternary GL tests, 7 rigid graph instances, and 81 Frobenius checks passed.")
    print("Radical examples give exact automorphism counts:", *counts)


if __name__ == "__main__":
    main()

